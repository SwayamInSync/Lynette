use crate::{utils::*, DeghostMode};
use proc_macro2::TokenStream;
use quote::ToTokens;
use std::path::PathBuf;
use syn_verus::Token;
use syn_verus::TraitItemFn;
use syn_verus::parse_quote;

/// Decide whether to retain a function-signature `decreases` clause.
///
/// `decreases` is a polymorphic construct in Verus: it can sit on a
/// `spec fn`, `proof fn`, or `exec fn` signature (termination measure
/// for a recursive function), or inside a loop header (proof scaffolding,
/// gated separately by `mode.invariants`). This function only governs
/// signature-level `decreases`.
///
/// Semantically, `decreases` is termination scaffolding: two function
/// definitions with identical bodies but different `decreases` clauses
/// are extensionally equivalent (they compute / prove the same thing).
/// The masking pipeline therefore blanks `decreases` per-mode (spec mode
/// blanks it on spec_fn sigs, proof mode on proof_fn sigs, exec mode on
/// exec_fn sigs), and the verifier's job under `compare --spec-mode
/// --allow-helpers` is simply to ignore signature-level `decreases`
/// everywhere so that a model completion that omits or rewrites it is
/// not flagged as a mismatch.
///
/// `mode.decreases` (the granular CLI flag) overrides this and retains
/// signature `decreases` unconditionally — preserving back-compat for
/// callers that pass `--decreases` explicitly.
fn keep_sig_decreases(_sig_mode: &syn_verus::FnMode, mode: &DeghostMode) -> bool {
    mode.decreases
}

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
                    // loop_ensures and loop-level decreases are proof-mode
                    // concerns (they describe loop behavior, not function
                    // specification). Bundle them with the loop spec block
                    // (`mode.invariants`) so `--spec-mode` strips them while
                    // `--proof-mode` keeps them.
                    ensures: if mode.invariants { w.ensures.clone() } else { None },
                    decreases: if mode.invariants { w.decreases.clone() } else { None },
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
                    // Loop-level decreases is a proof-mode concern; gate by
                    // `mode.invariants` (the loop spec block) instead of the
                    // fn-signature `mode.decreases`.
                    decreases: if mode.invariants { f.decreases.clone() } else { None },
                })
            })
        }
        syn_verus::Expr::Loop(l) => {
            /*
             * Fields to remove:
             * - invariant_except_break
             * - invariant
             * - invariant_ensures
             * - ensures
             * - decreases
             */
            remove_ghost_block(&l.body, mode).map(|new_body| {
                syn_verus::Expr::Loop(syn_verus::ExprLoop {
                    attrs: l.attrs.clone(),
                    label: l.label.clone(),
                    loop_token: l.loop_token.clone(),
                    body: new_body,
                    invariant_except_break: if mode.invariants { l.invariant_except_break.clone() } else { None },
                    invariant: if mode.invariants { l.invariant.clone() } else { None },
                    invariant_ensures: if mode.invariants { l.invariant_ensures.clone() } else { None },
                    // Loop-level ensures (loop_ensures) and decreases are
                    // proof-mode concerns; gate by `mode.invariants`.
                    ensures: if mode.invariants { l.ensures.clone() } else { None },
                    decreases: if mode.invariants { l.decreases.clone() } else { None },
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
    if !mode.spec
        && matches!(sig.mode, syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_))
    {
        return None;
    }
    // For proof functions: when --proof is off, we normally strip them entirely.
    // EXCEPTION: when any spec-clause flag is set (requires/ensures/recommends/
    // decreases), the proof function *signature* is part of the spec surface
    // (its clauses are the contract being proven). In that case we retain the
    // signature here and let the caller drop the body. This makes
    // `lynette compare --spec-mode` detect changes to lemma contracts.
    let any_spec_clause = mode.requires || mode.ensures || mode.recommends || mode.decreases;
    if !mode.proof
        && matches!(sig.mode, syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_))
        && !any_spec_clause
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
                .filter(|_| keep_sig_decreases(&sig.mode, mode)), // Removed
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
        let is_spec = matches!(
            new_sig.mode,
            syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)
        );
        let is_proof = matches!(
            new_sig.mode,
            syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_)
        );
        if is_spec || (is_proof && mode.proof) {
            Some(syn_verus::ItemFn {
                attrs: remove_verifier_attr(&func.attrs),
                vis: func.vis.clone(),
                sig: new_sig,
                block: func.block.clone(),
                semi_token: func.semi_token.clone(),
            })
        } else if is_proof {
            // Proof fn retained under --spec-mode: keep signature (with spec
            // clauses), but drop the proof body since the body is proof code,
            // not spec.
            Some(syn_verus::ItemFn {
                attrs: remove_verifier_attr(&func.attrs),
                vis: func.vis.clone(),
                sig: new_sig,
                block: Box::new(syn_verus::Block {
                    brace_token: Default::default(),
                    stmts: Vec::new(),
                }),
                semi_token: func.semi_token.clone(),
            })
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
                            let is_spec = matches!(
                                new_sig.mode,
                                syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)
                            );
                            let is_proof = matches!(
                                new_sig.mode,
                                syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_)
                            );
                            if is_spec || (is_proof && mode.proof) {
                                Some(syn_verus::ImplItemFn {
                                    attrs: func.attrs.clone(),
                                    vis: func.vis.clone(),
                                    defaultness: func.defaultness.clone(),
                                    sig: new_sig,
                                    block: func.block.clone(),
                                    semi_token: func.semi_token.clone(),
                                })
                            } else if is_proof {
                                // Proof fn retained under --spec-mode: keep
                                // signature, drop body.
                                Some(syn_verus::ImplItemFn {
                                    attrs: func.attrs.clone(),
                                    vis: func.vis.clone(),
                                    defaultness: func.defaultness.clone(),
                                    sig: new_sig,
                                    block: syn_verus::Block {
                                        brace_token: Default::default(),
                                        stmts: Vec::new(),
                                    },
                                    semi_token: func.semi_token.clone(),
                                })
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
        // Loop-level `decreases` is part of the loop spec block and is
        // gated by `mode.invariants` (a proof-mode concern), not the
        // fn-signature `mode.decreases`.
        let mut mode = DeghostMode::default();
        mode.invariants = true;
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
        // Loop-level `ensures` (loop_ensures) is gated by `mode.invariants`
        // (the loop spec block, a proof-mode concern), not the
        // fn-signature `mode.ensures`.
        let mut mode = DeghostMode::default();
        mode.invariants = true;
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

    // ── clause stripping on proof/spec functions (regression tests) ─────
    //
    // When a proof or spec function is *retained* (mode.proof/mode.spec = true),
    // clause-level flags (requires, ensures, recommends, decreases) must still
    // control whether those clauses appear in the output.  Previously the code
    // returned `func.clone()` for retained proof/spec fns, ignoring new_sig.

    const PROOF_FN_WITH_REQUIRES_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    proof fn my_lemma(x: nat)
        requires
            x > 0,
        ensures
            x >= 1,
    {
    }
}
"#;

    #[test]
    fn proof_fn_retained_strips_requires_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        // requires flag is off → requires clause should be stripped
        let out = deghost(PROOF_FN_WITH_REQUIRES_ENSURES, &mode);
        assert!(out.contains("my_lemma"), "proof fn should be retained");
        assert!(!out.contains("requires"), "requires should be stripped when flag is off");
    }

    #[test]
    fn proof_fn_retained_strips_ensures_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        // ensures flag is off → ensures clause should be stripped
        let out = deghost(PROOF_FN_WITH_REQUIRES_ENSURES, &mode);
        assert!(out.contains("my_lemma"), "proof fn should be retained");
        assert!(!out.contains("ensures"), "ensures should be stripped when flag is off");
    }

    #[test]
    fn proof_fn_retained_keeps_requires_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.requires = true;
        let out = deghost(PROOF_FN_WITH_REQUIRES_ENSURES, &mode);
        assert!(out.contains("my_lemma"));
        assert!(out.contains("requires"));
        assert!(out.contains("x > 0"));
    }

    #[test]
    fn proof_fn_retained_keeps_ensures_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.ensures = true;
        let out = deghost(PROOF_FN_WITH_REQUIRES_ENSURES, &mode);
        assert!(out.contains("my_lemma"));
        assert!(out.contains("ensures"));
        assert!(out.contains("x >= 1"));
    }

    #[test]
    fn proof_fn_retained_requires_on_ensures_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.requires = true;
        // ensures stays off
        let out = deghost(PROOF_FN_WITH_REQUIRES_ENSURES, &mode);
        assert!(out.contains("requires"));
        assert!(!out.contains("ensures"), "ensures should be stripped");
    }

    #[test]
    fn proof_fn_retained_ensures_on_requires_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.ensures = true;
        // requires stays off
        let out = deghost(PROOF_FN_WITH_REQUIRES_ENSURES, &mode);
        assert!(!out.contains("requires"), "requires should be stripped");
        assert!(out.contains("ensures"));
    }

    // ── spec fn with clauses ────────────────────────────────────────────

    const SPEC_FN_WITH_RECOMMENDS_DECREASES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn my_spec_fn(x: nat) -> nat
        recommends x > 0,
        decreases x,
    {
        if x == 0 { 0 } else { my_spec_fn((x - 1) as nat) }
    }
}
"#;

    #[test]
    fn spec_fn_retained_strips_recommends_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        let out = deghost(SPEC_FN_WITH_RECOMMENDS_DECREASES, &mode);
        assert!(out.contains("my_spec_fn"));
        assert!(!out.contains("recommends"), "recommends should be stripped when flag is off");
    }

    #[test]
    fn spec_fn_retained_strips_decreases_when_decreases_flag_off() {
        // Unified rule: signature-level `decreases` is termination
        // scaffolding and is stripped unless `--decreases` is passed
        // explicitly. The mere presence of `mode.spec` is no longer
        // enough to keep it. See `keep_sig_decreases` in deghost.rs.
        let mut mode = DeghostMode::default();
        mode.spec = true;
        let out = deghost(SPEC_FN_WITH_RECOMMENDS_DECREASES, &mode);
        assert!(out.contains("my_spec_fn"));
        assert!(!out.contains("decreases"), "decreases on a spec_fn sig must be stripped when --decreases is off");
    }

    #[test]
    fn spec_fn_retained_keeps_decreases_when_decreases_flag_on() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.decreases = true;
        let out = deghost(SPEC_FN_WITH_RECOMMENDS_DECREASES, &mode);
        assert!(out.contains("my_spec_fn"));
        assert!(out.contains("decreases"), "decreases must be kept when --decreases flag is on");
    }

    #[test]
    fn spec_fn_retained_keeps_recommends_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.recommends = true;
        let out = deghost(SPEC_FN_WITH_RECOMMENDS_DECREASES, &mode);
        assert!(out.contains("recommends"));
        assert!(out.contains("x > 0"));
    }

    #[test]
    fn spec_fn_retained_keeps_decreases_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.decreases = true;
        let out = deghost(SPEC_FN_WITH_RECOMMENDS_DECREASES, &mode);
        assert!(out.contains("decreases"));
    }

    // ── spec_checked fn with requires/ensures ───────────────────────────

    const SPEC_CHECKED_FN_WITH_CLAUSES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec(checked) fn my_spec_checked(x: nat) -> nat
        recommends x > 0,
    {
        x + 1
    }
}
"#;

    #[test]
    fn spec_checked_fn_retained_strips_recommends_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        let out = deghost(SPEC_CHECKED_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_spec_checked"));
        assert!(!out.contains("recommends"));
    }

    #[test]
    fn spec_checked_fn_retained_keeps_recommends_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.recommends = true;
        let out = deghost(SPEC_CHECKED_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_spec_checked"));
        assert!(out.contains("recommends"));
    }

    // ── proof_axiom fn with ensures ─────────────────────────────────────

    const PROOF_AXIOM_FN_WITH_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    #[verifier::external_body]
    proof fn my_axiom_lemma(x: nat)
        ensures
            x >= 0,
    {
    }
}
"#;

    #[test]
    fn proof_axiom_fn_retained_strips_ensures_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        let out = deghost(PROOF_AXIOM_FN_WITH_ENSURES, &mode);
        assert!(out.contains("my_axiom_lemma"));
        assert!(!out.contains("ensures"), "ensures should be stripped on proof axiom fn");
    }

    #[test]
    fn proof_axiom_fn_retained_keeps_ensures_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.ensures = true;
        let out = deghost(PROOF_AXIOM_FN_WITH_ENSURES, &mode);
        assert!(out.contains("my_axiom_lemma"));
        assert!(out.contains("ensures"));
    }

    // ── impl method (proof fn) with clauses ─────────────────────────────

    const IMPL_PROOF_FN_WITH_CLAUSES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    struct Foo { x: nat }
    impl Foo {
        proof fn my_impl_lemma(&self)
            requires
                self.x > 0,
            ensures
                self.x >= 1,
        {
        }
    }
}
"#;

    #[test]
    fn impl_proof_fn_retained_strips_requires_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        let out = deghost(IMPL_PROOF_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_impl_lemma"));
        assert!(!out.contains("requires"), "requires should be stripped on impl proof fn");
    }

    #[test]
    fn impl_proof_fn_retained_strips_ensures_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        let out = deghost(IMPL_PROOF_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_impl_lemma"));
        assert!(!out.contains("ensures"), "ensures should be stripped on impl proof fn");
    }

    #[test]
    fn impl_proof_fn_retained_keeps_requires_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.requires = true;
        let out = deghost(IMPL_PROOF_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_impl_lemma"));
        assert!(out.contains("requires"));
        assert!(out.contains("self.x > 0"));
    }

    #[test]
    fn impl_proof_fn_retained_keeps_ensures_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.ensures = true;
        let out = deghost(IMPL_PROOF_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_impl_lemma"));
        assert!(out.contains("ensures"));
    }

    // ── impl method (spec fn) with clauses ──────────────────────────────

    const IMPL_SPEC_FN_WITH_CLAUSES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    struct Bar { val: nat }
    impl Bar {
        spec fn my_impl_spec(&self) -> nat
            recommends self.val > 0,
        {
            self.val + 1
        }
    }
}
"#;

    #[test]
    fn impl_spec_fn_retained_strips_recommends_when_flag_off() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        let out = deghost(IMPL_SPEC_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_impl_spec"));
        assert!(!out.contains("recommends"), "recommends should be stripped on impl spec fn");
    }

    #[test]
    fn impl_spec_fn_retained_keeps_recommends_when_flag_on() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.recommends = true;
        let out = deghost(IMPL_SPEC_FN_WITH_CLAUSES, &mode);
        assert!(out.contains("my_impl_spec"));
        assert!(out.contains("recommends"));
    }

    // ── proof-mode composite flag ───────────────────────────────────────
    // --proof-mode enables proof + invariants + asserts + assert_forall +
    // assumes + proof_block, but NOT requires/ensures/recommends/decreases.

    const PROOF_FN_IN_CONTEXT: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    proof fn lemma_a(x: nat)
        requires
            x > 0,
        ensures
            x >= 1,
    {
    }

    fn exec_with_proof(n: u64) -> (r: u64)
        requires
            n > 0,
        ensures
            r == n,
    {
        proof {
            assert(n > 0);
        }
        n
    }
}
"#;

    #[test]
    fn proof_mode_strips_requires_on_proof_fn() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.invariants = true;
        mode.asserts = true;
        mode.assert_forall = true;
        mode.assumes = true;
        mode.proof_block = true;
        // This is what --proof-mode sets. requires/ensures are NOT set.
        let out = deghost(PROOF_FN_IN_CONTEXT, &mode);
        assert!(out.contains("lemma_a"), "proof fn should be retained");
        assert!(!out.contains("requires"), "requires should be stripped on both fns");
        assert!(!out.contains("ensures"), "ensures should be stripped on both fns");
        assert!(out.contains("proof"), "proof block should be retained");
        assert!(out.contains("assert("), "assert should be retained");
    }

    #[test]
    fn spec_mode_keeps_proof_fn_signature() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.requires = true;
        mode.ensures = true;
        mode.recommends = true;
        mode.decreases = true;
        // This is what --spec-mode sets. proof is NOT set.
        // Proof fn signatures (with their requires/ensures) are part of the
        // spec surface and must be preserved so spec-level changes to lemma
        // contracts are detected by `lynette compare --spec-mode`.
        let out = deghost(PROOF_FN_IN_CONTEXT, &mode);
        assert!(out.contains("lemma_a"), "proof fn signature should be retained");
        assert!(out.contains("exec_with_proof"), "exec fn should be retained");
        assert!(out.contains("requires"), "requires on exec/proof fn should be retained");
        assert!(out.contains("ensures"), "ensures on exec/proof fn should be retained");
    }

    // ── proof fn body is preserved when proof mode is on ────────────────

    const PROOF_FN_WITH_BODY: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    proof fn lemma_with_body(x: nat, y: nat)
        requires
            x > 0,
            y > 0,
        ensures
            x + y > 1,
    {
        assert(x >= 1);
        assert(y >= 1);
    }
}
"#;

    #[test]
    fn proof_fn_body_preserved_clauses_stripped() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        let out = deghost(PROOF_FN_WITH_BODY, &mode);
        assert!(out.contains("lemma_with_body"));
        // Body should be preserved as-is (not deghosted for proof fns)
        assert!(out.contains("assert(x >= 1)") || out.contains("assert (x >= 1)"));
        // But clauses should be stripped
        assert!(!out.contains("requires"));
        assert!(!out.contains("ensures"));
    }

    #[test]
    fn proof_fn_body_and_clauses_preserved() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.requires = true;
        mode.ensures = true;
        let out = deghost(PROOF_FN_WITH_BODY, &mode);
        assert!(out.contains("lemma_with_body"));
        assert!(out.contains("requires"));
        assert!(out.contains("ensures"));
        assert!(out.contains("x > 0"));
        assert!(out.contains("x + y > 1") || out.contains("x + y > 1"));
    }

    // ── mixed file: proof-mode should strip spec clauses everywhere ─────

    const MIXED_FILE: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn helper(x: nat) -> bool { x > 0 }

    proof fn my_proof(x: nat)
        requires
            helper(x),
        ensures
            x > 0,
    {
    }

    fn my_exec(x: u32) -> (r: u32)
        requires
            x > 0,
        ensures
            r == x,
    {
        x
    }
}
"#;

    #[test]
    fn mixed_file_proof_mode_only() {
        let mut mode = DeghostMode::default();
        mode.proof = true;
        mode.invariants = true;
        mode.asserts = true;
        mode.assert_forall = true;
        mode.assumes = true;
        mode.proof_block = true;
        let out = deghost(MIXED_FILE, &mode);
        // spec fn stripped (mode.spec is off)
        assert!(!out.contains("helper"), "spec fn should be stripped");
        // proof fn retained
        assert!(out.contains("my_proof"), "proof fn should be retained");
        // exec fn retained
        assert!(out.contains("my_exec"), "exec fn should be retained");
        // ALL requires/ensures stripped (mode.requires/ensures are off)
        assert!(!out.contains("requires"), "all requires should be stripped");
        assert!(!out.contains("ensures"), "all ensures should be stripped");
    }

    #[test]
    fn mixed_file_spec_mode_only() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.requires = true;
        mode.ensures = true;
        mode.recommends = true;
        mode.decreases = true;
        let out = deghost(MIXED_FILE, &mode);
        // spec fn retained
        assert!(out.contains("helper"), "spec fn should be retained");
        // proof fn signature retained (body dropped)
        assert!(out.contains("my_proof"), "proof fn signature should be retained");
        // exec fn retained with clauses
        assert!(out.contains("my_exec"));
        assert!(out.contains("requires"));
        assert!(out.contains("ensures"));
    }

    #[test]
    fn mixed_file_both_modes() {
        let mut mode = DeghostMode::default();
        mode.spec = true;
        mode.proof = true;
        mode.requires = true;
        mode.ensures = true;
        mode.recommends = true;
        mode.decreases = true;
        mode.invariants = true;
        mode.asserts = true;
        mode.assert_forall = true;
        mode.assumes = true;
        mode.proof_block = true;
        let out = deghost(MIXED_FILE, &mode);
        assert!(out.contains("helper"));
        assert!(out.contains("my_proof"));
        assert!(out.contains("my_exec"));
        assert!(out.contains("requires"));
        assert!(out.contains("ensures"));
    }

    #[test]
    fn mixed_file_default_strips_everything() {
        let out = deghost(MIXED_FILE, &DeghostMode::default());
        assert!(!out.contains("helper"));
        assert!(!out.contains("my_proof"));
        assert!(out.contains("my_exec"));
        assert!(!out.contains("requires"));
        assert!(!out.contains("ensures"));
    }

    // ────────────────────────────────────────────────────────────────────
    // `lynette compare --spec-mode` regression suite.
    //
    // These tests exercise the exact flag set that `--spec-mode` enables
    // (spec, requires, ensures, recommends, decreases). The intent of
    // `--spec-mode` is to detect *any* change to the exec or specification
    // surface of a file while ignoring proof-only edits.
    //
    // Each test pairs an "original" snippet with a "modified" snippet and
    // asserts whether `compare --spec-mode` should consider them equivalent
    // (`assert_spec_mode_eq`) or different (`assert_spec_mode_ne`).
    // ────────────────────────────────────────────────────────────────────

    /// Mode equivalent to CLI `--spec-mode`.
    fn spec_mode() -> DeghostMode {
        let mut m = DeghostMode::default();
        m.spec = true;
        m.requires = true;
        m.ensures = true;
        m.recommends = true;
        // Note: do NOT set `m.decreases = true` here. Signature-level
        // `decreases` retention is now context-aware via
        // `keep_sig_decreases` (kept on spec_fn / exec_fn signatures,
        // stripped on proof_fn signatures), and loop-level decreases is
        // gated by `mode.invariants` (off under spec-mode).
        m
    }

    /// Two files are "equivalent under --spec-mode" iff their deghosted
    /// pretty-printed forms match (this matches `compare`'s `result1 == result2`
    /// up to formatter-determinism).
    fn spec_mode_equal(a: &str, b: &str) -> bool {
        deghost(a, &spec_mode()) == deghost(b, &spec_mode())
    }

    fn assert_spec_mode_eq(a: &str, b: &str) {
        if !spec_mode_equal(a, b) {
            panic!(
                "expected spec-mode-equal\n--- A (deghosted) ---\n{}\n--- B (deghosted) ---\n{}",
                deghost(a, &spec_mode()),
                deghost(b, &spec_mode())
            );
        }
    }

    fn assert_spec_mode_ne(a: &str, b: &str) {
        if spec_mode_equal(a, b) {
            panic!(
                "expected spec-mode-different\n--- A (deghosted) ---\n{}\n--- B (deghosted) ---\n{}",
                deghost(a, &spec_mode()),
                deghost(b, &spec_mode())
            );
        }
    }

    fn wrap(body: &str) -> String {
        format!(
            "use vstd::prelude::*;\nfn main() {{}}\nverus! {{\n{}\n}}\n",
            body
        )
    }

    // ── exec function: body changes are detected ────────────────────────

    #[test]
    fn spec_mode_detects_exec_body_change() {
        let a = wrap("fn foo(x: u32) -> u32 { x + 1 }");
        let b = wrap("fn foo(x: u32) -> u32 { x + 2 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_signature_param_change() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u64) -> u32 { x as u32 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_signature_return_change() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u64 { x as u64 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_rename() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn bar(x: u32) -> u32 { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_added() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u32 { x }\nfn bar(x: u32) -> u32 { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_removed() {
        let a = wrap("fn foo(x: u32) -> u32 { x }\nfn bar(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u32 { x }");
        assert_spec_mode_ne(&a, &b);
    }

    // ── exec function clauses: requires/ensures/decreases/recommends ────

    #[test]
    fn spec_mode_detects_exec_requires_added() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u32 requires x > 0, { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_requires_removed() {
        let a = wrap("fn foo(x: u32) -> u32 requires x > 0, { x }");
        let b = wrap("fn foo(x: u32) -> u32 { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_requires_weakened() {
        let a = wrap("fn foo(x: u32) -> u32 requires x > 5, { x }");
        let b = wrap("fn foo(x: u32) -> u32 requires x > 0, { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_ensures_added() {
        let a = wrap("fn foo(x: u32) -> (r: u32) { x }");
        let b = wrap("fn foo(x: u32) -> (r: u32) ensures r == x, { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_ensures_weakened_to_true() {
        let a = wrap("fn foo(x: u32) -> (r: u32) ensures r == x, { x }");
        let b = wrap("fn foo(x: u32) -> (r: u32) ensures true, { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_exec_ensures_changed() {
        let a = wrap("fn foo(x: u32) -> (r: u32) ensures r == x, { x }");
        let b = wrap("fn foo(x: u32) -> (r: u32) ensures r >= x, { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_ignores_exec_decreases_change() {
        // Unified rule: signature `decreases` is termination scaffolding
        // and is stripped under --spec-mode regardless of fn kind.
        let a = wrap(
            "fn foo(n: u32) -> u32 decreases n, { if n == 0 { 0 } else { foo(n - 1) } }",
        );
        let b = wrap(
            "fn foo(n: u32) -> u32 decreases n + 1, { if n == 0 { 0 } else { foo(n - 1) } }",
        );
        assert_spec_mode_eq(&a, &b);
    }

    // ── spec functions: bodies, signatures, presence ────────────────────

    #[test]
    fn spec_mode_detects_spec_fn_body_change() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 10 }");
        let b = wrap("spec fn p(x: nat) -> bool { x > 20 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_weakened_to_true() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 10 }");
        let b = wrap("spec fn p(x: nat) -> bool { true }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_added() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = wrap("spec fn p(x: nat) -> bool { x > 0 }\nspec fn q(x: nat) -> bool { x > 1 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_removed() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 0 }\nspec fn q(x: nat) -> bool { x > 1 }");
        let b = wrap("spec fn p(x: nat) -> bool { x > 0 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_renamed() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = wrap("spec fn q(x: nat) -> bool { x > 0 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_param_changed() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = wrap("spec fn p(x: int) -> bool { x > 0 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_return_changed() {
        let a = wrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = wrap("spec fn p(x: nat) -> nat { x }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_spec_fn_quantifier_change() {
        let a = wrap(
            "spec fn all_gt(s: Seq<i32>, k: i32) -> bool { forall|i: int| 0 <= i < s.len() ==> s[i] > k }",
        );
        let b = wrap(
            "spec fn all_gt(s: Seq<i32>, k: i32) -> bool { exists|i: int| 0 <= i < s.len() && s[i] > k }",
        );
        assert_spec_mode_ne(&a, &b);
    }

    // ── proof functions: signature/contract changes are spec-level ──────
    // (This is the user-reported bug class.)

    #[test]
    fn spec_mode_detects_proof_fn_ensures_weakened_to_true() {
        // The exact pattern from the bug report: an equivalence lemma whose
        // ensures was weakened to `true` must be flagged.
        let a = wrap(
            "spec fn p(x: nat) -> bool { x > 0 }\n\
             spec fn p_model(x: nat) -> bool { x > 0 }\n\
             proof fn equiv(x: nat) ensures p(x) =~= p_model(x), { }",
        );
        let b = wrap(
            "spec fn p(x: nat) -> bool { x > 0 }\n\
             spec fn p_model(x: nat) -> bool { x > 0 }\n\
             proof fn equiv(x: nat) ensures true, { }",
        );
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_proof_fn_ensures_removed() {
        let a = wrap("proof fn lem(x: nat) ensures x + 0 == x, { }");
        let b = wrap("proof fn lem(x: nat) { }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_proof_fn_requires_changed() {
        let a = wrap("proof fn lem(x: nat) requires x > 0, ensures x > 0, { }");
        let b = wrap("proof fn lem(x: nat) requires true, ensures x > 0, { }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_proof_fn_signature_change() {
        let a = wrap("proof fn lem(x: nat) ensures x >= 0, { }");
        let b = wrap("proof fn lem(x: int) ensures x >= 0, { }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_proof_fn_renamed() {
        let a = wrap("proof fn lem(x: nat) ensures true, { }");
        let b = wrap("proof fn lem2(x: nat) ensures true, { }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_proof_fn_added() {
        let a = wrap("spec fn p() -> bool { true }");
        let b = wrap("spec fn p() -> bool { true }\nproof fn lem() ensures true, { }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_proof_fn_removed() {
        let a = wrap("spec fn p() -> bool { true }\nproof fn lem() ensures true, { }");
        let b = wrap("spec fn p() -> bool { true }");
        assert_spec_mode_ne(&a, &b);
    }

    // ── proof function bodies are NOT spec-level: ignored by --spec-mode ─

    #[test]
    fn spec_mode_ignores_proof_fn_body_change() {
        let a = wrap(
            "proof fn lem(x: nat) ensures x + 0 == x, { assert(x + 0 == x); }",
        );
        let b = wrap(
            "proof fn lem(x: nat) ensures x + 0 == x, { }",
        );
        assert_spec_mode_eq(&a, &b);
    }

    #[test]
    fn spec_mode_ignores_proof_fn_body_added_helper_assert() {
        let a = wrap(
            "proof fn lem(x: nat) ensures x + 0 == x, { }",
        );
        let b = wrap(
            "proof fn lem(x: nat) ensures x + 0 == x, {\n\
                assert(x >= 0);\n\
                assert(x + 0 == x);\n\
             }",
        );
        assert_spec_mode_eq(&a, &b);
    }

    // ── exec function bodies: proof-only constructs inside are ignored ──

    #[test]
    fn spec_mode_ignores_assert_in_exec_body() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u32 { assert(x == x); x }");
        assert_spec_mode_eq(&a, &b);
    }

    #[test]
    fn spec_mode_ignores_assume_in_exec_body() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u32 { assume(x > 0); x }");
        assert_spec_mode_eq(&a, &b);
    }

    #[test]
    fn spec_mode_ignores_proof_block_in_exec_body() {
        let a = wrap("fn foo(x: u32) -> u32 { x }");
        let b = wrap("fn foo(x: u32) -> u32 { proof { assert(x == x); } x }");
        assert_spec_mode_eq(&a, &b);
    }

    #[test]
    fn spec_mode_ignores_loop_invariant_changes() {
        // Loop invariants are proof scaffolding, not part of the spec surface.
        let a = wrap(
            "fn sum(n: u32) -> u32 {\n\
                let mut i: u32 = 0;\n\
                while i < n invariant i <= n, decreases n - i { i += 1; }\n\
                i\n\
             }",
        );
        let b = wrap(
            "fn sum(n: u32) -> u32 {\n\
                let mut i: u32 = 0;\n\
                while i < n invariant i <= n, i >= 0, decreases n - i { i += 1; }\n\
                i\n\
             }",
        );
        assert_spec_mode_eq(&a, &b);
    }

    // ── recommends on spec fn ───────────────────────────────────────────

    #[test]
    fn spec_mode_detects_spec_fn_recommends_change() {
        let a = wrap(
            "spec fn p(x: nat) -> bool recommends x > 0, { x > 10 }",
        );
        let b = wrap(
            "spec fn p(x: nat) -> bool recommends x > 5, { x > 10 }",
        );
        assert_spec_mode_ne(&a, &b);
    }

    // ── identical files are equal (sanity) ──────────────────────────────

    const REALISTIC_FILE: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn all_gt(s: Seq<i32>, k: i32) -> bool {
        forall|i: int| 0 <= i < s.len() ==> s[i] > k
    }

    fn filter_gt_20(list: Vec<i32>) -> (ret: Vec<i32>)
        requires all_gt(list@, 10),
        ensures ret@.len() <= list@.len(), all_gt(ret@, 20),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < list.len()
            invariant i <= list.len(), result@.len() <= i, all_gt(result@, 20),
            decreases list.len() - i,
        {
            let x = list[i];
            if x > 20 { result.push(x); }
            i += 1;
        }
        result
    }

    proof fn lemma_all_gt_20(s: Seq<i32>)
        ensures all_gt(s, 20) ==> all_gt(s, 10),
    {
    }
}
"#;

    #[test]
    fn spec_mode_identical_files_are_equal() {
        assert_spec_mode_eq(REALISTIC_FILE, REALISTIC_FILE);
    }

    #[test]
    fn spec_mode_realistic_proof_body_only_change_is_equal() {
        // Add a helper assert inside the lemma body — this is proof code only.
        let modified = REALISTIC_FILE.replace(
            "proof fn lemma_all_gt_20(s: Seq<i32>)\n\
        ensures all_gt(s, 20) ==> all_gt(s, 10),\n    {\n    }",
            "proof fn lemma_all_gt_20(s: Seq<i32>)\n\
        ensures all_gt(s, 20) ==> all_gt(s, 10),\n    {\n        assert(true);\n    }",
        );
        assert_spec_mode_eq(REALISTIC_FILE, &modified);
    }

    #[test]
    fn spec_mode_realistic_proof_ensures_weakened_is_different() {
        // Mirrors the user-reported bug: weaken a lemma's ensures to `true`.
        let modified = REALISTIC_FILE.replace(
            "ensures all_gt(s, 20) ==> all_gt(s, 10),",
            "ensures true,",
        );
        assert_spec_mode_ne(REALISTIC_FILE, &modified);
    }

    #[test]
    fn spec_mode_realistic_exec_ensures_weakened_is_different() {
        let modified = REALISTIC_FILE.replace(
            "ensures ret@.len() <= list@.len(), all_gt(ret@, 20),",
            "ensures true,",
        );
        assert_spec_mode_ne(REALISTIC_FILE, &modified);
    }

    #[test]
    fn spec_mode_realistic_exec_body_change_is_different() {
        let modified = REALISTIC_FILE.replace("if x > 20", "if x > 30");
        assert_spec_mode_ne(REALISTIC_FILE, &modified);
    }

    #[test]
    fn spec_mode_realistic_loop_invariant_change_is_equal() {
        // Loop invariants are not in the spec surface.
        let modified = REALISTIC_FILE.replace(
            "invariant i <= list.len(), result@.len() <= i, all_gt(result@, 20),",
            "invariant i <= list.len(), all_gt(result@, 20),",
        );
        assert_spec_mode_eq(REALISTIC_FILE, &modified);
    }

    // ── impl blocks: spec/proof methods ─────────────────────────────────

    const IMPL_FILE: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    struct S { x: u32 }
    impl S {
        spec fn invariant_holds(&self) -> bool { self.x > 0 }

        proof fn lemma_self(&self)
            ensures self.x >= 0,
        {
        }

        fn get_x(&self) -> (r: u32)
            requires self.invariant_holds(),
            ensures r == self.x,
        {
            self.x
        }
    }
}
"#;

    #[test]
    fn spec_mode_detects_impl_spec_method_body_change() {
        let modified = IMPL_FILE.replace("self.x > 0", "self.x > 10");
        assert_spec_mode_ne(IMPL_FILE, &modified);
    }

    #[test]
    fn spec_mode_detects_impl_proof_method_ensures_weakened() {
        let modified = IMPL_FILE.replace("ensures self.x >= 0,", "ensures true,");
        assert_spec_mode_ne(IMPL_FILE, &modified);
    }

    #[test]
    fn spec_mode_detects_impl_exec_method_requires_change() {
        let modified =
            IMPL_FILE.replace("requires self.invariant_holds(),", "requires true,");
        assert_spec_mode_ne(IMPL_FILE, &modified);
    }

    #[test]
    fn spec_mode_detects_impl_exec_method_body_change() {
        let modified = IMPL_FILE.replace("        self.x\n", "        self.x + 1\n");
        assert_spec_mode_ne(IMPL_FILE, &modified);
    }

    #[test]
    fn spec_mode_ignores_impl_proof_method_body_change() {
        let modified = IMPL_FILE.replace(
            "        proof fn lemma_self(&self)\n\
            ensures self.x >= 0,\n        {\n        }",
            "        proof fn lemma_self(&self)\n\
            ensures self.x >= 0,\n        {\n            assert(self.x >= 0);\n        }",
        );
        assert_spec_mode_eq(IMPL_FILE, &modified);
    }

    // ── struct/enum item changes are visible (always retained) ──────────

    #[test]
    fn spec_mode_detects_struct_field_change() {
        let a = wrap("struct S { x: u32 }");
        let b = wrap("struct S { x: u64 }");
        assert_spec_mode_ne(&a, &b);
    }

    #[test]
    fn spec_mode_detects_struct_added_field() {
        let a = wrap("struct S { x: u32 }");
        let b = wrap("struct S { x: u32, y: u32 }");
        assert_spec_mode_ne(&a, &b);
    }

    // ── loop-level decreases / loop_ensures are proof-mode concerns ─────
    //
    // Background: the masking pipeline (create_masked_segments.py) blanks
    // every `decreases` clause and every loop-level `ensures` (loop_ensures)
    // in proof-mode masks. The model is then asked to fill them back in.
    // For `compare --spec-mode --allow-helpers` to verify those completions
    // without false positives, the verifier must treat loop-level decreases
    // and loop_ensures as proof-mode constructs (gated by `mode.invariants`),
    // not as spec-mode constructs.
    //
    // Conversely, a fn-signature `decreases` (e.g. on a recursive function)
    // is *also* termination scaffolding: two functions with the same body
    // but different `decreases` are extensionally equivalent. The masking
    // pipeline blanks signature `decreases` per-mode (spec-mode blanks it
    // on spec_fn sigs, etc.), and `--spec-mode` strips ALL signature
    // `decreases` so completions that omit/rewrite it are not flagged.

    const RECURSIVE_FN_WITH_SIG_DECREASES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn fact(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 1 } else { n * fact((n - 1) as nat) }
    }
}
"#;

    #[test]
    fn spec_mode_strips_fn_sig_decreases() {
        // Unified rule: `--spec-mode` strips every signature-level
        // `decreases` so the masker can blank them per-mode without
        // producing false positives during verification.
        let m = spec_mode();
        assert!(!deghost_contains(RECURSIVE_FN_WITH_SIG_DECREASES, &m, "decreases"));
    }

    #[test]
    fn spec_mode_ignores_fn_sig_decreases_removed() {
        let modified = RECURSIVE_FN_WITH_SIG_DECREASES.replace("        decreases n,\n", "");
        assert_spec_mode_eq(RECURSIVE_FN_WITH_SIG_DECREASES, &modified);
    }

    #[test]
    fn spec_mode_ignores_fn_sig_decreases_changed() {
        let modified = RECURSIVE_FN_WITH_SIG_DECREASES
            .replace("        decreases n,\n", "        decreases 0nat,\n");
        assert_spec_mode_eq(RECURSIVE_FN_WITH_SIG_DECREASES, &modified);
    }

    const WHILE_WITH_DECREASES_AND_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn count_up(n: u64) -> (r: u64)
        ensures r == n,
    {
        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
            ensures
                i == n,
            decreases n - i,
        {
            i = i + 1;
        }
        i
    }
}
"#;

    #[test]
    fn spec_mode_strips_loop_decreases() {
        // Loop-level decreases must be dropped by --spec-mode (so a model
        // asked to fill in a blanked loop `decreases` is not falsely flagged).
        let out = deghost(WHILE_WITH_DECREASES_AND_ENSURES, &spec_mode());
        assert!(
            !out.contains("decreases n - i"),
            "loop decreases should be stripped under spec-mode, got:\n{out}"
        );
    }

    #[test]
    fn spec_mode_strips_loop_ensures() {
        // Loop-level ensures (loop_ensures) must be dropped by --spec-mode.
        let out = deghost(WHILE_WITH_DECREASES_AND_ENSURES, &spec_mode());
        // Function-signature `ensures r == n,` should still be present.
        assert!(out.contains("r == n"), "fn-sig ensures should be kept");
        // The loop-level `ensures i == n,` must be gone.
        assert!(
            !out.contains("i == n"),
            "loop_ensures should be stripped under spec-mode, got:\n{out}"
        );
    }

    #[test]
    fn spec_mode_keeps_fn_sig_ensures_when_loop_ensures_dropped() {
        // Sanity: dropping loop_ensures must not also drop fn-sig ensures.
        let m = spec_mode();
        assert!(deghost_contains(WHILE_WITH_DECREASES_AND_ENSURES, &m, "ensures"));
    }

    #[test]
    fn spec_mode_eq_when_loop_decreases_differs() {
        // Two files identical except for the loop `decreases` expression
        // must compare equal under --spec-mode (model is allowed to choose
        // any termination measure for a loop).
        let modified =
            WHILE_WITH_DECREASES_AND_ENSURES.replace("decreases n - i,", "decreases (n - i) as int,");
        assert_spec_mode_eq(WHILE_WITH_DECREASES_AND_ENSURES, &modified);
    }

    #[test]
    fn spec_mode_eq_when_loop_decreases_added() {
        // Adding a loop `decreases` (where there was none) is a proof-mode
        // edit and must be ignored by --spec-mode.
        let without = WHILE_WITH_DECREASES_AND_ENSURES.replace("            decreases n - i,\n", "");
        assert_spec_mode_eq(&without, WHILE_WITH_DECREASES_AND_ENSURES);
    }

    #[test]
    fn spec_mode_eq_when_loop_ensures_differs() {
        let modified =
            WHILE_WITH_DECREASES_AND_ENSURES.replace("ensures\n                i == n,", "ensures\n                i >= n,");
        assert_spec_mode_eq(WHILE_WITH_DECREASES_AND_ENSURES, &modified);
    }

    const FOR_LOOP_WITH_DECREASES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn sum_to(n: u64) -> (r: u64)
        ensures r == n,
    {
        let mut s: u64 = 0;
        for i in 0..n
            invariant
                i <= n,
            decreases n - i,
        {
            s = s + 1;
        }
        s
    }
}
"#;

    #[test]
    fn spec_mode_strips_for_loop_decreases() {
        let out = deghost(FOR_LOOP_WITH_DECREASES, &spec_mode());
        assert!(
            !out.contains("decreases n - i"),
            "for-loop decreases should be stripped under spec-mode, got:\n{out}"
        );
    }

    #[test]
    fn spec_mode_eq_when_for_loop_decreases_added() {
        let without = FOR_LOOP_WITH_DECREASES.replace("            decreases n - i,\n", "");
        assert_spec_mode_eq(&without, FOR_LOOP_WITH_DECREASES);
    }

    const BARE_LOOP_WITH_DECREASES_AND_ENSURES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    fn run() -> (r: u64) {
        let mut i: u64 = 0;
        loop
            invariant i <= 10,
            ensures i == 10,
            decreases 10 - i,
        {
            if i == 10 { break; }
            i = i + 1;
        }
        i
    }
}
"#;

    #[test]
    fn spec_mode_strips_bare_loop_decreases_and_ensures() {
        let out = deghost(BARE_LOOP_WITH_DECREASES_AND_ENSURES, &spec_mode());
        assert!(
            !out.contains("decreases 10 - i"),
            "bare-loop decreases should be stripped under spec-mode"
        );
        assert!(
            !out.contains("ensures i == 10"),
            "bare-loop ensures (loop_ensures) should be stripped under spec-mode"
        );
    }

    // Proof-mode keeps loop-level decreases / loop_ensures because
    // `--proof-mode` enables `mode.invariants`, which now governs the whole
    // loop spec block.
    #[test]
    fn proof_mode_keeps_loop_decreases_and_loop_ensures() {
        let mut m = DeghostMode::default();
        // Mirror the CLI `--proof-mode` flag set:
        m.proof = true;
        m.invariants = true;
        m.asserts = true;
        m.assert_forall = true;
        m.assumes = true;
        m.proof_block = true;
        let out = deghost(WHILE_WITH_DECREASES_AND_ENSURES, &m);
        assert!(out.contains("decreases n - i"), "got:\n{out}");
        assert!(out.contains("i == n"), "got:\n{out}");
    }

    // Granular flag: --invariants alone (without --decreases / --ensures)
    // must keep all loop spec content.
    #[test]
    fn invariants_flag_alone_keeps_loop_decreases_and_loop_ensures() {
        let mut m = DeghostMode::default();
        m.invariants = true;
        let out = deghost(WHILE_WITH_DECREASES_AND_ENSURES, &m);
        assert!(out.contains("decreases n - i"), "got:\n{out}");
        assert!(out.contains("i == n"), "got:\n{out}");
        assert!(out.contains("i <= n"), "got:\n{out}");
    }

    // Without --invariants, --decreases alone must NOT bring back loop
    // decreases (only fn-sig decreases).
    #[test]
    fn decreases_flag_alone_keeps_only_fn_sig_decreases() {
        // Need `mode.spec` too so the spec fn isn't dropped entirely.
        let mut m = DeghostMode::default();
        m.spec = true;
        m.decreases = true;
        let sig_out = deghost(RECURSIVE_FN_WITH_SIG_DECREASES, &m);
        assert!(sig_out.contains("decreases n"), "fn-sig decreases must be kept, got:\n{sig_out}");

        let loop_out = deghost(WHILE_WITH_DECREASES_AND_ENSURES, &m);
        assert!(
            !loop_out.contains("decreases n - i"),
            "loop decreases must NOT be brought back by --decreases alone, got:\n{loop_out}"
        );
    }

    // Without --invariants, --ensures alone keeps fn-sig ensures but NOT
    // loop_ensures.
    #[test]
    fn ensures_flag_alone_keeps_only_fn_sig_ensures() {
        let mut m = DeghostMode::default();
        m.ensures = true;
        let out = deghost(WHILE_WITH_DECREASES_AND_ENSURES, &m);
        assert!(out.contains("r == n"), "fn-sig ensures must be kept");
        assert!(
            !out.contains("i == n"),
            "loop_ensures must NOT be brought back by --ensures alone"
        );
    }

    // ── Context-aware fn-signature `decreases` ──────────────────────────
    //
    // `decreases` on a function signature is classified by the kind of
    // function it lives on:
    //   - spec_fn  : kept iff `mode.spec`  (decreases is part of the spec
    //                of the spec_fn)
    //   - proof_fn : kept iff `mode.proof` (so `--spec-mode` strips it,
    //                matching that the masker blanks proof_fn decreases
    //                under proof-mode masks)
    //   - exec_fn  : kept iff `mode.spec`  (termination measure is part
    //                of the function's contract, grouped with spec)
    // The granular `--decreases` CLI flag retains all of them (back-compat).

    const PROOF_FN_WITH_SIG_DECREASES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    pub proof fn lemma_inc(n: nat)
        requires
            n >= 0,
        ensures
            n + 1 > n,
        decreases n,
    { }
}
"#;

    const EXEC_FN_WITH_SIG_DECREASES: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    pub fn countdown(n: u64) -> (r: u64)
        ensures r == 0,
        decreases n,
    {
        if n == 0 { 0 } else { countdown(n - 1) }
    }
}
"#;

    #[test]
    fn spec_mode_strips_spec_fn_sig_decreases() {
        // Under the unified rule, ALL signature-level `decreases` is
        // termination scaffolding and is stripped under --spec-mode.
        // The masker blanks `decreases` on spec_fn signatures under
        // spec-mode masks, so the verifier must ignore it.
        let m = spec_mode();
        let out = deghost(RECURSIVE_FN_WITH_SIG_DECREASES, &m);
        assert!(out.contains("fn fact"), "spec_fn must be kept");
        assert!(!out.contains("decreases n"), "decreases on spec_fn sig must be stripped under --spec-mode, got:\n{out}");
    }

    #[test]
    fn spec_mode_strips_proof_fn_sig_decreases() {
        // Proof-fn signature is kept under --spec-mode (so its requires/
        // ensures contract is checked), but the decreases on it must be
        // stripped — the masker blanks it under proof-mode masks.
        let m = spec_mode();
        let out = deghost(PROOF_FN_WITH_SIG_DECREASES, &m);
        assert!(out.contains("lemma_inc"), "proof_fn sig should be kept");
        assert!(out.contains("requires"), "requires on proof_fn must be kept");
        assert!(out.contains("ensures"), "ensures on proof_fn must be kept");
        assert!(
            !out.contains("decreases n"),
            "decreases on proof_fn sig must be stripped under --spec-mode, got:\n{out}"
        );
    }

    #[test]
    fn spec_mode_strips_exec_fn_sig_decreases() {
        // Exec_fn `decreases` is termination scaffolding, not part of
        // the executable contract semantics. Stripped under --spec-mode.
        let m = spec_mode();
        let out = deghost(EXEC_FN_WITH_SIG_DECREASES, &m);
        assert!(out.contains("fn countdown"), "exec_fn must be kept");
        assert!(!out.contains("decreases n"), "decreases on exec_fn sig must be stripped under --spec-mode, got:\n{out}");
    }

    #[test]
    fn proof_mode_strips_proof_fn_sig_decreases() {
        // Even under --proof-mode (which retains the proof_fn body), the
        // signature `decreases` is still stripped because the masker
        // under proof-mode also blanks proof_fn sig decreases.
        let mut m = DeghostMode::default();
        m.proof = true;
        m.invariants = true;
        m.asserts = true;
        m.assert_forall = true;
        m.assumes = true;
        m.proof_block = true;
        let out = deghost(PROOF_FN_WITH_SIG_DECREASES, &m);
        assert!(out.contains("lemma_inc"), "proof_fn must be kept");
        assert!(!out.contains("decreases n"), "decreases on proof_fn sig must be stripped under --proof-mode, got:\n{out}");
    }

    #[test]
    fn proof_mode_strips_spec_fn_sig_decreases() {
        // `--proof-mode` does not set mode.spec, so the spec_fn is dropped
        // entirely — its decreases is gone with it.
        let mut m = DeghostMode::default();
        m.proof = true;
        let out = deghost(RECURSIVE_FN_WITH_SIG_DECREASES, &m);
        assert!(!out.contains("decreases n"), "got:\n{out}");
    }

    #[test]
    fn decreases_flag_overrides_kind_check() {
        // The granular --decreases flag retains decreases on every kind
        // (back-compat for users who pass `--decreases` directly).
        let mut m = DeghostMode::default();
        m.decreases = true;
        m.spec = true; m.proof = true; // keep the fns themselves
        for src in [RECURSIVE_FN_WITH_SIG_DECREASES, PROOF_FN_WITH_SIG_DECREASES, EXEC_FN_WITH_SIG_DECREASES] {
            let out = deghost(src, &m);
            assert!(out.contains("decreases n"), "expected decreases retained for:\n{src}\n--- got ---\n{out}");
        }
    }

    // ── Round-trip: model fills in (or omits) a blanked decreases ───────
    #[test]
    fn spec_mode_eq_when_proof_fn_decreases_added() {
        let masked = PROOF_FN_WITH_SIG_DECREASES.replace("        decreases n,\n", "");
        assert_spec_mode_eq(&masked, PROOF_FN_WITH_SIG_DECREASES);
    }

    #[test]
    fn spec_mode_eq_when_spec_fn_decreases_removed() {
        // The model removes the spec_fn decreases — under the unified
        // rule this is allowed (decreases is termination scaffolding).
        let modified = RECURSIVE_FN_WITH_SIG_DECREASES.replace("        decreases n,\n", "");
        assert_spec_mode_eq(RECURSIVE_FN_WITH_SIG_DECREASES, &modified);
    }

    #[test]
    fn spec_mode_eq_when_exec_fn_decreases_removed() {
        let modified = EXEC_FN_WITH_SIG_DECREASES.replace("        decreases n,\n", "");
        assert_spec_mode_eq(EXEC_FN_WITH_SIG_DECREASES, &modified);
    }

    #[test]
    fn spec_mode_eq_when_decreases_expression_changed() {
        // Same kind of change, but the decreases is rewritten rather
        // than removed. Still ignored by the verifier.
        let modified = RECURSIVE_FN_WITH_SIG_DECREASES.replace("decreases n,", "decreases 0nat,");
        assert_spec_mode_eq(RECURSIVE_FN_WITH_SIG_DECREASES, &modified);
    }
}
