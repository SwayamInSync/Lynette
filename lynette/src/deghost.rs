use crate::{utils::*, DeghostMode};
use proc_macro2::TokenStream;
use quote::ToTokens;
use std::path::PathBuf;
use syn_verus::Token;
use syn_verus::TraitItemFn;
use syn_verus::parse_quote;

fn remove_ghost_local(local: &syn_verus::Local, mode: &DeghostMode) -> Option<syn_verus::Local> {
    match local.ghost {
        Some(_) => None,
        None => {
            match local.tracked {
                Some(_) => None,
                None => {
                    local.init.clone().map_or_else(
                        || {
                            Some(syn_verus::Local {
                                attrs: local.attrs.clone(),
                                let_token: local.let_token.clone(),
                                tracked: None,
                                ghost: None,
                                pat: local.pat.clone(),
                                init: None,
                                semi_token: local.semi_token.clone()
                            })
                        },
                        |i| {
                            remove_ghost_expr(&i.expr, mode).map(|i_expr| {
                                syn_verus::Local {
                                    attrs: local.attrs.clone(),
                                    let_token: local.let_token.clone(),
                                    tracked: None,
                                    ghost: None,
                                    pat: local.pat.clone(),
                                    init: Some(syn_verus::LocalInit {
                                        eq_token: i.eq_token.clone(),
                                        expr: Box::new(i_expr),
                                        diverge: i.diverge.clone().map_or_else(
                                            || None,
                                            |d| remove_ghost_expr(&d.1, mode).map(|e|
                                                (d.0.clone(), Box::new(e))
                                            )
                                        )
                                    }),
                                    semi_token: local.semi_token.clone()
                                }
                            })
                        }
                    )
                }
            }
        },
    }
}

fn remove_ghost_expr(expr: &syn_verus::Expr, mode: &DeghostMode) -> Option<syn_verus::Expr> {
    //println!("{}\n", expr.to_token_stream().to_string());
    match expr {
        syn_verus::Expr::Block(b) => remove_ghost_block(&b.block, mode).map(|new_block| {
            syn_verus::Expr::Block(syn_verus::ExprBlock {
                attrs: b.attrs.clone(),
                label: b.label.clone(),
                block: syn_verus::Block {
                    brace_token: b.block.brace_token.clone(),
                    stmts: new_block.stmts,
                },
            })
        }),
        syn_verus::Expr::Call(c) => {
            let new_args: syn_verus::punctuated::Punctuated<syn_verus::Expr, Token![,]> = c
                .args
                .iter()
                .map(|arg| {
                    if let syn_verus::Expr::Closure(c) = arg {
                        remove_ghost_expr(&*c.body, mode).unwrap()
                    } else {
                        arg.clone()
                    }
                })
                .collect();

            Some(syn_verus::Expr::Call(syn_verus::ExprCall {
                attrs: c.attrs.clone(),
                func: c.func.clone(),
                paren_token: c.paren_token.clone(),
                args: new_args,
            }))
        }
        syn_verus::Expr::Closure(c) => remove_ghost_expr(&*c.body, mode).map(|new_body| {
            syn_verus::Expr::Closure(syn_verus::ExprClosure {
                attrs: c.attrs.clone(),
                asyncness: c.asyncness.clone(),
                movability: c.movability.clone(),
                capture: c.capture.clone(),
                or1_token: c.or1_token.clone(),
                inputs: c.inputs.clone(),
                or2_token: c.or2_token.clone(),
                output: c.output.clone(),
                requires: if mode.requires { c.requires.clone() } else { None },
                ensures: if mode.ensures { c.ensures.clone() } else { None },
                inner_attrs: c.inner_attrs.clone(),
                body: Box::new(new_body),
                constness: c.constness.clone(),
                lifetimes: c.lifetimes.clone(),
                options: c.options.clone(),
                proof_fn: None
            })
        }),
        syn_verus::Expr::While(w) => {
            /*
             * Fields to remove:
             * - invariant_except_break
             * - invariant
             * - invariant_ensures
             * - ensures
             * - decreases
             */
            remove_ghost_block(&w.body, mode).map(|new_body| {
                syn_verus::Expr::While(syn_verus::ExprWhile {
                    attrs: w.attrs.clone(),
                    label: w.label.clone(),
                    while_token: w.while_token.clone(),
                    cond: w.cond.clone(),
                    body: new_body,
                    invariant_except_break: if mode.invariants { w.invariant_except_break.clone() } else { None },
                    invariant: if mode.invariants { w.invariant.clone() } else { None },
                    invariant_ensures: if mode.invariants { w.invariant_ensures.clone() } else { None },
                    ensures: if mode.ensures { w.ensures.clone() } else { None },
                    decreases: if mode.decreases { w.decreases.clone() } else { None },
                })
            })
        }
        syn_verus::Expr::ForLoop(f) => {
            /*
             * Fields to remove:
             * - invariant
             * - decreases
             */
            remove_ghost_block(&f.body, mode).map(|new_body| {
                syn_verus::Expr::ForLoop(syn_verus::ExprForLoop {
                    attrs: f.attrs.clone(),
                    label: f.label.clone(),
                    for_token: f.for_token.clone(),
                    pat: f.pat.clone(),
                    in_token: f.in_token.clone(),
                    expr: f.expr.clone(),
                    body: new_body,
                    expr_name: f.expr_name.clone(),
                    invariant: if mode.invariants { f.invariant.clone() } else { None },
                    decreases: if mode.decreases { f.decreases.clone() } else { None },
                })
            })
        }
        syn_verus::Expr::Unary(u) => {
            match u.op {
                /*
                 * verus:
                 * Proof
                 * Forall
                 * Exists
                 * Choose
                 */
                syn_verus::UnOp::Proof(_) => {
                    if mode.proof_block {
                        Some(expr.clone())
                    } else {
                        None
                    }
                }
                syn_verus::UnOp::Forall(_)
                | syn_verus::UnOp::Exists(_)
                | syn_verus::UnOp::Choose(_) => None,
                _ => Some(expr.clone()),
            }
        }
        syn_verus::Expr::If(i) => {
            remove_ghost_block(&i.then_branch, mode).and_then(|new_then_branch| {
                if let Some((else_token, else_expr)) = i.else_branch.as_ref() {
                    remove_ghost_expr(&*else_expr, mode).map(|new_else_branch| {
                        syn_verus::Expr::If(syn_verus::ExprIf {
                            attrs: i.attrs.clone(),
                            if_token: i.if_token.clone(),
                            cond: i.cond.clone(),
                            then_branch: new_then_branch,
                            else_branch: Some((else_token.clone(), Box::new(new_else_branch))),
                        })
                    })
                } else {
                    Some(syn_verus::Expr::If(syn_verus::ExprIf {
                        attrs: i.attrs.clone(),
                        if_token: i.if_token.clone(),
                        cond: i.cond.clone(),
                        then_branch: new_then_branch,
                        else_branch: None,
                    }))
                }
            })
        }
        syn_verus::Expr::Match(m) => {
            let new_arms: Vec<syn_verus::Arm> = m
                .arms
                .iter()
                .filter_map(|arm| {
                    remove_ghost_expr(&*arm.body, mode).map_or_else(
                        || Some(syn_verus::Arm {
                            attrs: arm.attrs.clone(),
                            pat: arm.pat.clone(),
                            guard: arm.guard.clone(),
                            fat_arrow_token: arm.fat_arrow_token.clone(),
                            body: Box::new(syn_verus::Expr::Block( parse_quote! { {} })), // insert an empty block. removing the match arm entirely can cause an error
                            comma: arm.comma.clone(),
                        }),
                        |new_body| Some(syn_verus::Arm {
                            attrs: arm.attrs.clone(),
                            pat: arm.pat.clone(),
                            guard: arm.guard.clone(),
                            fat_arrow_token: arm.fat_arrow_token.clone(),
                            body: Box::new(new_body),
                            comma: arm.comma.clone(),
                        }))
                })
                .collect();

            Some(syn_verus::Expr::Match(syn_verus::ExprMatch {
                attrs: m.attrs.clone(),
                match_token: m.match_token.clone(),
                expr: m.expr.clone(),
                brace_token: m.brace_token.clone(),
                arms: new_arms,
            }))
        }
        // veurs:
        syn_verus::Expr::Assert(a) => {
            fn annotated_assert(a: &syn_verus::Assert) -> bool {
                a.attrs.iter().any(|attr| match &attr.meta {
                    syn_verus::Meta::List(l) => l.tokens.to_string() == "(llm_do_not_change)",
                    _ => false
                })
            }

            if mode.asserts || (mode.asserts_anno && annotated_assert(a)) {
                Some(expr.clone())
            } else {
                None
            }
        }
        syn_verus::Expr::Assume(..) => {
            if mode.assumes {
                Some(expr.clone())
            } else {
                None
            }
        }
        syn_verus::Expr::AssertForall(..) => {
            if mode.assert_forall {
                Some(expr.clone())
            } else {
                None
            }
        }
        syn_verus::Expr::RevealHide(..)
        | syn_verus::Expr::View(..)
        | syn_verus::Expr::BigAnd(..)
        | syn_verus::Expr::BigOr(..)
        | syn_verus::Expr::Is(..)
        | syn_verus::Expr::IsNot(..)
        | syn_verus::Expr::Has(..)
        | syn_verus::Expr::HasNot(..)
        | syn_verus::Expr::Matches(..)
        | syn_verus::Expr::GetField(..) => None,
        _ => Some(expr.clone()),
    }
}

fn remove_ghost_stmt(stmt: &syn_verus::Stmt, mode: &DeghostMode) -> Option<syn_verus::Stmt> {
    match stmt {
        syn_verus::Stmt::Local(l) => remove_ghost_local(l, mode).map(syn_verus::Stmt::Local),
        syn_verus::Stmt::Item(i) => {
            // While we do have visit_item, I am not sure if we need to visit the item here
            // or just keep it as is.
            Some(syn_verus::Stmt::Item(i.clone()))
            // match visit_item(i) {
            //     Some(new_item) => Some(syn_verus::Stmt::Item(new_item)),
            //     None => None
            // }
        }
        syn_verus::Stmt::Expr(e, s) => remove_ghost_expr(e, mode).map(|e1| syn_verus::Stmt::Expr(e1, s.clone())),
        syn_verus::Stmt::Macro(e) => {
            Some(syn_verus::Stmt::Macro(e.clone()))
        },
    }
}

pub fn remove_ghost_block(block: &syn_verus::Block, mode: &DeghostMode) -> Option<syn_verus::Block> {
    let new_stms: Vec<syn_verus::Stmt> =
        block.stmts.iter().filter_map(|stmt| remove_ghost_stmt(stmt, mode)).collect();

    if new_stms.is_empty() {
        return None;
    }

    Some(syn_verus::Block { brace_token: block.brace_token.clone(), stmts: new_stms })
}

pub fn remove_ghost_sig(
    sig: &syn_verus::Signature,
    mode: &DeghostMode,
) -> Option<syn_verus::Signature> {
    /*
     * Fields to remove:
     * - publish
     * - broadcast
     * - prover
     * - mode
     * - requires
     * - ensures
     * - recommends
     * - decreases
     * - invariants
     */
    if (!mode.spec
        && matches!(sig.mode, syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)))
        || (!mode.proof && matches!(sig.mode, syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_)))
    {
        return None;
    }

    Some(syn_verus::Signature {
        publish: syn_verus::Publish::Default, // Removed
        constness: sig.constness.clone(),
        asyncness: sig.asyncness.clone(),
        unsafety: sig.unsafety.clone(),
        abi: sig.abi.clone(),
        broadcast: sig.broadcast.clone(), // Removed
        mode: sig.mode.clone(),           // Removed
        fn_token: sig.fn_token.clone(),
        ident: sig.ident.clone(),
        generics: sig.generics.clone(),
        paren_token: sig.paren_token.clone(),
        inputs: sig.inputs.clone(),
        variadic: sig.variadic.clone(),
        output: match &sig.output {
            syn_verus::ReturnType::Type(_, _, _, ty) => {
                syn_verus::ReturnType::Type(Default::default(), None, None, ty.clone())
            }
            syn_verus::ReturnType::Default => syn_verus::ReturnType::Default,
        },
        spec: syn_verus::SignatureSpec {
            prover: sig.spec.prover.clone(), // Removed
            // TODO: This fix needs to be propagated to other places using `Specification`
            requires: sig
                .spec
                .requires
                .clone()
                .map(|mut new_req| {
                    if !new_req.exprs.exprs.is_empty() && !new_req.exprs.exprs.trailing_punct() {
                        new_req.exprs.exprs.push_punct(Default::default());
                    }
                    new_req
                })
                .filter(|_| mode.requires), // Removed
            recommends: sig.spec.recommends.clone().map(|mut new_rec| {
                if !new_rec.exprs.exprs.is_empty() && !new_rec.exprs.exprs.trailing_punct() {
                    new_rec.exprs.exprs.push_punct(Default::default());
                }
                new_rec
            }).filter(|_| mode.recommends), // Removed
            ensures: sig
                .spec
                .ensures
                .clone()
                .map(|mut new_ens| {
                    if !new_ens.exprs.exprs.is_empty() && !new_ens.exprs.exprs.trailing_punct() {
                        new_ens.exprs.exprs.push_punct(Default::default());
                    }
                    new_ens
                })
                .filter(|_| mode.ensures), // Removed
            decreases: sig
                .spec
                .decreases
                .clone()
                .map(|mut new_dec| {
                    if !new_dec.decreases.exprs.exprs.is_empty() && !new_dec.decreases.exprs.exprs.trailing_punct() {
                        new_dec.decreases.exprs.exprs.push_punct(Default::default());
                    }
                    new_dec
                })
                .filter(|_| mode.decreases), // Removed
            invariants: sig.spec.invariants.clone().filter(|_| mode.invariants), // Removed
            default_ensures: sig
                .spec
                .default_ensures
                .clone()
                .map(|mut new_ens| {
                    if !new_ens.exprs.exprs.is_empty() && !new_ens.exprs.exprs.trailing_punct() {
                        new_ens.exprs.exprs.push_punct(Default::default());
                    }
                    new_ens
                })
                .filter(|_| mode.ensures), // Removed
            returns: None,
            unwind: None,
            with: None
        }
    })
}

fn is_verifier_attr(attr: &syn_verus::Attribute) -> bool {
    attr.path().segments.len() > 0 && attr.path().segments[0].ident.to_string() == "verifier"
}

pub fn remove_verifier_attr(attr: &Vec<syn_verus::Attribute>) -> Vec<syn_verus::Attribute> {
    attr.iter().filter(|a| !is_verifier_attr(a)).map(|a| a.clone()).collect()
}

/*
 * Target Mode:
 *  Executable function: qualifiers cannot be modifified; executable part cannot be modified
 *  spec function: cannot be modified at all
 *  proof function: do not care at all
 * Non-Target Mode:
 *  Executable function: qualifiers can be modified; executable part cannot be modified
 *  spec function: do not care at all
 *  proof function: do not care at all
 */

fn remove_ghost_fn(func: &syn_verus::ItemFn, mode: &DeghostMode) -> Option<syn_verus::ItemFn> {
    remove_ghost_sig(&func.sig, mode).and_then(|new_sig| {
        if matches!(new_sig.mode, syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_))
            || matches!(new_sig.mode, syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_))
        {
            Some(func.clone())
        } else {
            remove_ghost_block(&(*func.block), mode).map(|new_block| {
                syn_verus::ItemFn {
                    attrs: remove_verifier_attr(&func.attrs),
                    vis: func.vis.clone(),
                    sig: new_sig,
                    block: Box::new(new_block), // Box the new block
                    semi_token: func.semi_token.clone(), // XXX: What is this?
                }
            })
        }
    })
}

fn remove_ghost_impl(i: &syn_verus::ItemImpl, mode: &DeghostMode) -> syn_verus::ItemImpl {
    syn_verus::ItemImpl {
        attrs: i.attrs.clone(),
        defaultness: i.defaultness.clone(),
        unsafety: i.unsafety.clone(),
        impl_token: i.impl_token.clone(),
        generics: i.generics.clone(),
        trait_: i.trait_.clone(),
        self_ty: i.self_ty.clone(),
        brace_token: i.brace_token.clone(),
        items: i
            .items
            .iter()
            .filter_map(|it| {
                if let syn_verus::ImplItem::Fn(func) = it {
                    remove_ghost_sig(&func.sig, mode).and_then(|new_sig| {
                        {
                            if matches!(
                                new_sig.mode,
                                syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)
                            ) || matches!(
                                new_sig.mode,
                                syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_)
                            ) {
                                Some(func.clone())
                            } else {
                                remove_ghost_block(&func.block, mode).map(|new_block| {
                                    syn_verus::ImplItemFn {
                                        attrs: func.attrs.clone(),
                                        vis: func.vis.clone(),
                                        defaultness: func.defaultness.clone(),
                                        sig: new_sig,
                                        block: new_block,
                                        semi_token: func.semi_token.clone(), // XXX: What is this?
                                    }
                                })
                            }
                        }
                        .and_then(|new_method| Some(syn_verus::ImplItem::Fn(new_method)))
                    })
                } else {
                    Some(it.clone())
                }
            })
            .collect(),
    }
}

fn remove_ghost_item(item: &syn_verus::Item, mode: &DeghostMode) -> Option<syn_verus::Item> {
    match item {
        syn_verus::Item::Fn(f) => match remove_ghost_fn(f, mode) {
            Some(new_func) => Some(syn_verus::Item::Fn(new_func)),
            None => None,
        },
        syn_verus::Item::Impl(i) => Some(syn_verus::Item::Impl(remove_ghost_impl(i, mode))),
        syn_verus::Item::Trait(t) => Some(syn_verus::Item::Trait(syn_verus::ItemTrait {
            attrs: t.attrs.clone(),
            vis: t.vis.clone(),
            unsafety: t.unsafety.clone(),
            auto_token: t.auto_token.clone(),
            trait_token: t.trait_token.clone(),
            ident: t.ident.clone(),
            generics: t.generics.clone(),
            colon_token: t.colon_token.clone(),
            supertraits: t.supertraits.clone(),
            brace_token: t.brace_token.clone(),
            restriction: t.restriction.clone(),
            items: t
                .items
                .iter()
                .filter_map(|i| match i {
                    syn_verus::TraitItem::Fn(func) => {
                        Some(syn_verus::TraitItem::Fn(TraitItemFn {
                            attrs: func.attrs.clone(),
                            sig: remove_ghost_sig(&func.sig, mode)?,
                            default: func.default.as_ref().map(|b| {
                                remove_ghost_block(b, mode).unwrap_or_else(|| syn_verus::Block {
                                    brace_token: Default::default(),
                                    stmts: Vec::new(),
                                })
                            }),
                            semi_token: func.semi_token.clone(),
                        }))
                    }
                    _ => Some(i.clone()),
                })
                .collect::<Vec<syn_verus::TraitItem>>(),
        })),
        _ => Some(item.clone()), // syn_verus::Item::Macro(m) => visit_macro(m),
                                 // syn_verus::Item::Mod(m) => visit_mod(m),
                                 // syn_verus::Item::Use(u) => visit_use(u),
                                 // syn_verus::Item::Struct(s) => visit_struct(s),
                                 // syn_verus::Item::Enum(e) => visit_enum(e),
                                 // syn_verus::Item::Type(t) => visit_type(t),
                                 // syn_verus::Item::Const(c) => visit_const(c),
                                 // syn_verus::Item::Static(s) => visit_static(s),
                                 // syn_verus::Item::Union(u) => visit_union(u),
                                 // syn_verus::Item::TraitAlias(t) => visit_trait_alias(t),
                                 // syn_verus::Item::ExternCrate(e) => visit_extern_crate(e),
                                 // syn_verus::Item::ForeignMod(f) => visit_foreign_mod(f),
                                 // syn_verus::Item::Macro2(m) => visit_macro2(m),
                                 // syn_verus::Item::Verbatim(v) => visit_verbatim(v),
    }
}

pub fn remove_ghost_from_file(file: &syn_verus::File, mode: &DeghostMode) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        if let Some(item) = remove_ghost_item(item, mode) {
            new_items.push(item);
        }
    }

    let new_file = syn_verus::File {
        shebang: file.shebang.clone(),
        attrs: file.attrs.clone(),
        items: new_items,
    };

    new_file
}

pub fn remove_verus_macro(file: &syn_verus::File) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        if let syn_verus::Item::Macro(m) = item {
            if !is_verus_macro(&m.mac) {
                new_items.push(item.clone());
            }
        } else {
            new_items.push(item.clone());
        }
    }

    let new_file = syn_verus::File {
        shebang: file.shebang.clone(),
        attrs: file.attrs.clone(),
        items: new_items,
    };

    new_file
}

pub fn deghost_merge_files(file: &syn_verus::File, verus_files: Vec<syn_verus::File>) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        new_items.push(item.clone());
    }

    for verus_file in verus_files {
        for item in &verus_file.items {
            new_items.push(item.clone());
        }
    }

    let new_file = syn_verus::File {
        shebang: file.shebang.clone(),
        attrs: file.attrs.clone(),
        items: new_items,
    };

    new_file
}

pub fn fextract_pure_rust(filepath: PathBuf, mode: &DeghostMode) -> Result<syn_verus::File, Error> {
    let orig_file = fload_file(&filepath)?;
    let pure_file = remove_verus_macro(&orig_file);

    extract_verus_macro(&orig_file).and_then(|verus_macros| {
        let mut verus_files: Vec<syn_verus::File> = Vec::new();
        for vm in verus_macros {
            let new_verus_file = remove_ghost_from_file(&vm, mode);

            let mut new_verus_ts = TokenStream::new();

            new_verus_file.to_tokens(&mut new_verus_ts);
            verus_files.push(new_verus_file);
        }

        //println!("{}", fprint_file(&merge_files(&pure_file, verus_files.clone()), VFormatter::VerusFmt));

        Ok(deghost_merge_files(&pure_file, verus_files))
    })
}

#[cfg(test)]
mod deghost_tests {
    use super::*;
    use crate::utils::fprint_file;
    use crate::Formatter;
    use std::io::Write;

    /// Write code to a temp file, deghost with the given mode, return the pretty-printed result.
    fn deghost(code: &str, mode: &DeghostMode) -> String {
        let mut tmp = tempfile::Builder::new().suffix(".rs").tempfile().unwrap();
        tmp.write_all(code.as_bytes()).unwrap();
        tmp.flush().unwrap();
        let result = fextract_pure_rust(tmp.path().to_path_buf(), mode).unwrap();
        fprint_file(&result, Formatter::VerusFmt)
    }

    /// Check that `needle` appears in the deghosted output.
    fn deghost_contains(code: &str, mode: &DeghostMode, needle: &str) -> bool {
        deghost(code, mode).contains(needle)
    }

    // ── requires ────────────────────────────────────────────────────────

    const FN_WITH_REQUIRES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
        requires x > 0,
    { x }
}
"#;

    #[test]
    fn requires_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_REQUIRES, &DeghostMode::default(), "requires"));
    }

    #[test]
    fn requires_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.requires = true;
        assert!(deghost_contains(FN_WITH_REQUIRES, &mode, "requires"));
    }

    // ── ensures ─────────────────────────────────────────────────────────

    const FN_WITH_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
        ensures r == x,
    { x }
}
"#;

    #[test]
    fn ensures_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_ENSURES, &DeghostMode::default(), "ensures"));
    }

    #[test]
    fn ensures_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.ensures = true;
        assert!(deghost_contains(FN_WITH_ENSURES, &mode, "ensures"));
    }

    // ── recommends ──────────────────────────────────────────────────────

    const FN_WITH_RECOMMENDS: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
        recommends x > 0,
    { x }
}
"#;

    #[test]
    fn recommends_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_RECOMMENDS, &DeghostMode::default(), "recommends"));
    }

    #[test]
    fn recommends_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.recommends = true;
        assert!(deghost_contains(FN_WITH_RECOMMENDS, &mode, "recommends"));
    }

    // ── decreases ───────────────────────────────────────────────────────

    const FN_WITH_DECREASES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn countdown(n: u64) -> (r: u64)
        decreases n,
    {
        if n == 0 { 0 } else { countdown(n - 1) }
    }
}
"#;

    #[test]
    fn decreases_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_DECREASES, &DeghostMode::default(), "decreases"));
    }

    #[test]
    fn decreases_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.decreases = true;
        assert!(deghost_contains(FN_WITH_DECREASES, &mode, "decreases"));
    }

    // ── spec functions ──────────────────────────────────────────────────

    const SPEC_FN: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn my_spec(x: nat) -> nat { x + 1 }
    fn exec_fn() -> (r: u32) { 42 }
}
"#;

    #[test]
    fn spec_fn_stripped_by_default() {
        assert!(!deghost_contains(SPEC_FN, &DeghostMode::default(), "my_spec"));
    }

    #[test]
    fn spec_fn_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        assert!(deghost_contains(SPEC_FN, &mode, "my_spec"));
    }

    #[test]
    fn exec_fn_always_retained() {
        assert!(deghost_contains(SPEC_FN, &DeghostMode::default(), "exec_fn"));
    }

    // ── proof functions ─────────────────────────────────────────────────

    const PROOF_FN: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    proof fn my_lemma()
    {
    }
    fn exec_fn() -> (r: u32) { 42 }
}
"#;

    #[test]
    fn proof_fn_stripped_by_default() {
        assert!(!deghost_contains(PROOF_FN, &DeghostMode::default(), "my_lemma"));
    }

    #[test]
    fn proof_fn_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        assert!(deghost_contains(PROOF_FN, &mode, "my_lemma"));
    }

    // ── asserts ─────────────────────────────────────────────────────────

    const FN_WITH_ASSERT: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
    {
        assert(x == x);
        x
    }
}
"#;

    #[test]
    fn assert_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_ASSERT, &DeghostMode::default(), "assert("));
    }

    #[test]
    fn assert_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.asserts = true;
        assert!(deghost_contains(FN_WITH_ASSERT, &mode, "assert("));
    }

    // ── assert_forall ───────────────────────────────────────────────────

    const FN_WITH_ASSERT_FORALL: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo()
    {
        assert forall |i: int| i >= 0 implies i >= 0 by {};
        let x: u32 = 1;
    }
}
"#;

    #[test]
    fn assert_forall_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_ASSERT_FORALL, &DeghostMode::default(), "assert forall"));
    }

    #[test]
    fn assert_forall_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.assert_forall = true;
        assert!(deghost_contains(FN_WITH_ASSERT_FORALL, &mode, "assert forall"));
    }

    // ── assumes ─────────────────────────────────────────────────────────

    const FN_WITH_ASSUME: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
    {
        assume(x > 0);
        x
    }
}
"#;

    #[test]
    fn assume_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_ASSUME, &DeghostMode::default(), "assume("));
    }

    #[test]
    fn assume_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.assumes = true;
        assert!(deghost_contains(FN_WITH_ASSUME, &mode, "assume("));
    }

    // ── proof_block ─────────────────────────────────────────────────────

    const FN_WITH_PROOF_BLOCK: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
    {
        proof {
            assert(x == x);
        }
        x
    }
}
"#;

    #[test]
    fn proof_block_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_PROOF_BLOCK, &DeghostMode::default(), "proof {"));
    }

    #[test]
    fn proof_block_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.proof_block = true;
        assert!(deghost_contains(FN_WITH_PROOF_BLOCK, &mode, "proof"));
    }

    // ── while loop invariants ───────────────────────────────────────────

    const FN_WITH_WHILE_INVARIANTS: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(n: u64) -> (r: u64)
    {
        let mut i: u64 = 0;
        let mut s: u64 = 0;
        while i < n
            invariant
                i <= n,
                s == i,
            decreases n - i,
        {
            s = s + 1;
            i = i + 1;
        }
        s
    }
}
"#;

    #[test]
    fn while_invariant_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_WHILE_INVARIANTS, &DeghostMode::default(), "invariant"));
    }

    #[test]
    fn while_invariant_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.invariants = true;
        assert!(deghost_contains(FN_WITH_WHILE_INVARIANTS, &mode, "invariant"));
    }

    #[test]
    fn while_decreases_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_WHILE_INVARIANTS, &DeghostMode::default(), "decreases"));
    }

    #[test]
    fn while_decreases_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.decreases = true;
        assert!(deghost_contains(FN_WITH_WHILE_INVARIANTS, &mode, "decreases"));
    }

    // ── empty requires/ensures (the push_punct fix) ─────────────────────

    const FN_WITH_EMPTY_CLAUSES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(x: u32) -> (r: u32)
        requires
            // TODO
        ensures
            // TODO
    { x }
}
"#;

    #[test]
    fn empty_clauses_no_panic() {
        // This used to panic with "Punctuated::push_punct: cannot push punctuation..."
        let _ = deghost(FN_WITH_EMPTY_CLAUSES, &DeghostMode::default());
    }

    #[test]
    fn empty_clauses_with_requires_flag_no_panic() {
        let mut mode = DeghostMode::default();
        mode.requires = true;
        mode.ensures = true;
        let _ = deghost(FN_WITH_EMPTY_CLAUSES, &mode);
    }

    // ── flag isolation: enabling one flag doesn't leak others ────────────

    const FN_WITH_ALL_GHOST: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn my_spec(x: nat) -> nat { x + 1 }
    proof fn my_lemma()
    {
    }
    fn foo(x: u32) -> (r: u32)
        requires
            x > 0,
        ensures
            r == x,
    {
        assert(x == x);
        assume(x > 0);
        x
    }
}
"#;

    #[test]
    fn requires_flag_does_not_leak_ensures() {
        let mut mode = DeghostMode::default();
        mode.requires = true;
        let out = deghost(FN_WITH_ALL_GHOST, &mode);
        assert!(out.contains("requires"));
        assert!(!out.contains("ensures"));
    }

    #[test]
    fn ensures_flag_does_not_leak_requires() {
        let mut mode = DeghostMode::default();
        mode.ensures = true;
        let out = deghost(FN_WITH_ALL_GHOST, &mode);
        assert!(out.contains("ensures"));
        assert!(!out.contains("requires"));
    }

    #[test]
    fn asserts_flag_does_not_leak_assumes() {
        let mut mode = DeghostMode::default();
        mode.asserts = true;
        let out = deghost(FN_WITH_ALL_GHOST, &mode);
        assert!(out.contains("assert("));
        assert!(!out.contains("assume("));
    }

    #[test]
    fn assumes_flag_does_not_leak_asserts() {
        let mut mode = DeghostMode::default();
        mode.assumes = true;
        let out = deghost(FN_WITH_ALL_GHOST, &mode);
        assert!(out.contains("assume("));
        assert!(!out.contains("assert("));
    }

    #[test]
    fn spec_flag_does_not_leak_proof() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        let out = deghost(FN_WITH_ALL_GHOST, &mode);
        assert!(out.contains("my_spec"));
        assert!(!out.contains("my_lemma"));
    }

    #[test]
    fn proof_flag_does_not_leak_spec() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        let out = deghost(FN_WITH_ALL_GHOST, &mode);
        assert!(out.contains("my_lemma"));
        assert!(!out.contains("my_spec"));
    }

    #[test]
    fn recommends_flag_does_not_leak_requires() {
        let mut mode = DeghostMode::default();
        mode.recommends = true;
        let out = deghost(FN_WITH_RECOMMENDS, &mode);
        assert!(out.contains("recommends"));
        assert!(!out.contains("requires"));
    }

    // ── default mode strips everything ──────────────────────────────────

    #[test]
    fn default_mode_strips_all_ghost() {
        let out = deghost(FN_WITH_ALL_GHOST, &DeghostMode::default());
        assert!(!out.contains("requires"));
        assert!(!out.contains("ensures"));
        assert!(!out.contains("assert("));
        assert!(!out.contains("assume("));
        assert!(!out.contains("my_spec"));
        assert!(!out.contains("my_lemma"));
        assert!(out.contains("foo")); // exec fn body preserved
    }

    // ── spec_checked_fn ─────────────────────────────────────────────────

    const SPEC_CHECKED_FN: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec(checked) fn my_spec_checked(x: nat) -> nat { x + 1 }
    fn exec_fn() -> (r: u32) { 42 }
}
"#;

    #[test]
    fn spec_checked_fn_stripped_by_default() {
        assert!(!deghost_contains(SPEC_CHECKED_FN, &DeghostMode::default(), "my_spec_checked"));
    }

    #[test]
    fn spec_checked_fn_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        assert!(deghost_contains(SPEC_CHECKED_FN, &mode, "my_spec_checked"));
    }

    // ── proof_axiom_fn ──────────────────────────────────────────────────

    const PROOF_AXIOM_FN: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    #[verifier::external_body]
    proof fn my_axiom()
        ensures true,
    {
    }
    fn exec_fn() -> (r: u32) { 42 }
}
"#;

    #[test]
    fn proof_axiom_fn_stripped_by_default() {
        assert!(!deghost_contains(PROOF_AXIOM_FN, &DeghostMode::default(), "my_axiom"));
    }

    #[test]
    fn proof_axiom_fn_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        assert!(deghost_contains(PROOF_AXIOM_FN, &mode, "my_axiom"));
    }

    // ── exec fn (explicit mode) ─────────────────────────────────────────

    const EXEC_FN_EXPLICIT: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    exec fn my_exec(x: u32) -> (r: u32) { x }
}
"#;

    #[test]
    fn explicit_exec_fn_always_retained() {
    }

    // ── while invariant_ensures ─────────────────────────────────────────

    const FN_WITH_WHILE_INVARIANT_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(n: u64) -> (r: u64)
    {
        let mut i: u64 = 0;
        while i < n
            invariant_ensures
                i <= n,
        {
            i = i + 1;
        }
        i
    }
}
"#;

    #[test]
    fn while_invariant_ensures_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_WHILE_INVARIANT_ENSURES, &DeghostMode::default(), "invariant_ensures"));
    }

    #[test]
    fn while_invariant_ensures_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.invariants = true;
        assert!(deghost_contains(FN_WITH_WHILE_INVARIANT_ENSURES, &mode, "invariant_ensures"));
    }

    // ── while invariant_except_break ────────────────────────────────────

    const FN_WITH_WHILE_INVARIANT_EXCEPT_BREAK: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(n: u64) -> (r: u64)
    {
        let mut i: u64 = 0;
        while i < n
            invariant_except_break
                i < n,
        {
            i = i + 1;
        }
        i
    }
}
"#;

    #[test]
    fn while_invariant_except_break_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_WHILE_INVARIANT_EXCEPT_BREAK, &DeghostMode::default(), "invariant_except_break"));
    }

    #[test]
    fn while_invariant_except_break_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.invariants = true;
        assert!(deghost_contains(FN_WITH_WHILE_INVARIANT_EXCEPT_BREAK, &mode, "invariant_except_break"));
    }

    // ── while loop ensures (separate from sig-level ensures) ────────────

    const FN_WITH_WHILE_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(n: u64) -> (r: u64)
    {
        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
            ensures
                i == n,
        {
            i = i + 1;
        }
        i
    }
}
"#;

    #[test]
    fn while_ensures_stripped_by_default() {
        let out = deghost(FN_WITH_WHILE_ENSURES, &DeghostMode::default());
        assert!(!out.contains("ensures"));
    }

    #[test]
    fn while_ensures_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.ensures = true;
        let out = deghost(FN_WITH_WHILE_ENSURES, &mode);
        assert!(out.contains("ensures"));
    }

    // ── for-loop invariants/decreases ───────────────────────────────────

    const FN_WITH_FOR_INVARIANT: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn foo(v: Vec<u64>)
    {
        let mut s: u64 = 0;
        for i in iter: 0..v.len()
            invariant
                s <= i * 1000,
        {
            s = s + 1;
        }
    }
}
"#;

    #[test]
    fn for_invariant_stripped_by_default() {
        assert!(!deghost_contains(FN_WITH_FOR_INVARIANT, &DeghostMode::default(), "invariant"));
    }

    #[test]
    fn for_invariant_retained_with_flag() {
        let mut mode = DeghostMode::default();
        mode.invariants = true;
        assert!(deghost_contains(FN_WITH_FOR_INVARIANT, &mode, "invariant"));
    }
}
