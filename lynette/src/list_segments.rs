use quote::ToTokens;
use serde_json::json;
use std::path::PathBuf;
use syn::spanned::Spanned;

use crate::utils::*;

/// Represents one identified segment from a Verus file.
#[derive(Debug)]
pub struct VerusSegment {
    pub kind: SegmentKind,
    /// Fully-qualified name, e.g. "ReconcileIdAllocator::allocate" or "entails_trans"
    pub name: String,
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
    /// Rendered source text of the segment (when meaningful, e.g. a
    /// requires/ensures clause expression). Empty for segments where the
    /// span suffices (top-level items, blocks, etc.).
    pub text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SegmentKind {
    SpecFn,
    SpecCheckedFn,
    ProofFn,
    ProofAxiomFn,
    ExecFn,
    DefaultFn,
    Requires,
    Ensures,
    Recommends,
    Decreases,
    Invariant,
    InvariantEnsures,
    InvariantExceptBreak,
    LoopEnsures,
    Assert,
    AssertForall,
    Assume,
    ProofBlock,
    Struct,
    Enum,
    TypeAlias,
    Trait,
    Impl,
    Macro,
}

impl SegmentKind {
    pub fn label(&self) -> &'static str {
        match self {
            SegmentKind::SpecFn => "spec_fn",
            SegmentKind::SpecCheckedFn => "spec_checked_fn",
            SegmentKind::ProofFn => "proof_fn",
            SegmentKind::ProofAxiomFn => "proof_axiom_fn",
            SegmentKind::ExecFn => "exec_fn",
            SegmentKind::DefaultFn => "fn",
            SegmentKind::Requires => "requires",
            SegmentKind::Ensures => "ensures",
            SegmentKind::Recommends => "recommends",
            SegmentKind::Decreases => "decreases",
            SegmentKind::Invariant => "invariant",
            SegmentKind::InvariantEnsures => "invariant_ensures",
            SegmentKind::InvariantExceptBreak => "invariant_except_break",
            SegmentKind::LoopEnsures => "loop_ensures",
            SegmentKind::Assert => "assert",
            SegmentKind::AssertForall => "assert_forall",
            SegmentKind::Assume => "assume",
            SegmentKind::ProofBlock => "proof_block",
            SegmentKind::Struct => "struct",
            SegmentKind::Enum => "enum",
            SegmentKind::TypeAlias => "type_alias",
            SegmentKind::Trait => "trait",
            SegmentKind::Impl => "impl",
            SegmentKind::Macro => "macro",
        }
    }
}

pub fn fn_mode_to_kind(mode: &syn_verus::FnMode) -> SegmentKind {
    match mode {
        syn_verus::FnMode::Spec(_) => SegmentKind::SpecFn,
        syn_verus::FnMode::SpecChecked(_) => SegmentKind::SpecCheckedFn,
        syn_verus::FnMode::Proof(_) => SegmentKind::ProofFn,
        syn_verus::FnMode::ProofAxiom(_) => SegmentKind::ProofAxiomFn,
        syn_verus::FnMode::Exec(_) => SegmentKind::ExecFn,
        syn_verus::FnMode::Default => SegmentKind::DefaultFn,
    }
}

fn span_to_loc(span: proc_macro2::Span) -> (usize, usize, usize, usize) {
    (span.start().line, span.start().column, span.end().line, span.end().column)
}

/// Extract ghost items (requires, ensures, etc.) from a function signature.
fn collect_sig_ghosts(sig: &syn_verus::Signature, parent_name: &str, out: &mut Vec<VerusSegment>) {
    if let Some(ref r) = sig.spec.requires {
        for expr in &r.exprs.exprs {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            out.push(VerusSegment {
                kind: SegmentKind::Requires,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
    }
    if let Some(ref e) = sig.spec.ensures {
        for expr in &e.exprs.exprs {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            out.push(VerusSegment {
                kind: SegmentKind::Ensures,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
    }
    if let Some(ref r) = sig.spec.recommends {
        for expr in &r.exprs.exprs {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            out.push(VerusSegment {
                kind: SegmentKind::Recommends,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
    }
    if let Some(ref d) = sig.spec.decreases {
        for expr in &d.decreases.exprs.exprs {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            out.push(VerusSegment {
                kind: SegmentKind::Decreases,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
    }
}

/// Recursively extract ghost segments from expressions (asserts, proof blocks, loop invariants).
fn collect_expr_ghosts(expr: &syn_verus::Expr, parent_name: &str, out: &mut Vec<VerusSegment>) {
    match expr {
        syn_verus::Expr::Assert(a) => {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            // Recurse into assert body first
            if let Some(ref body) = a.body {
                for stmt in &body.stmts {
                    collect_stmt_ghosts(stmt, parent_name, out);
                }
            }
            out.push(VerusSegment {
                kind: SegmentKind::Assert,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
        syn_verus::Expr::AssertForall(a) => {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            for stmt in &a.body.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
            out.push(VerusSegment {
                kind: SegmentKind::AssertForall,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
        syn_verus::Expr::Assume(_a) => {
            let (sl, sc, el, ec) = span_to_loc(expr.span());
            out.push(VerusSegment {
                kind: SegmentKind::Assume,
                name: parent_name.to_string(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
            });
        }
        syn_verus::Expr::Unary(u) => {
            if let syn_verus::UnOp::Proof(_) = u.op {
                let (sl, sc, el, ec) = span_to_loc(expr.span());
                collect_expr_ghosts(&u.expr, parent_name, out);
                out.push(VerusSegment {
                    kind: SegmentKind::ProofBlock,
                    name: parent_name.to_string(),
                    start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                });
            } else {
                collect_expr_ghosts(&u.expr, parent_name, out);
            }
        }
        syn_verus::Expr::Block(bl) => {
            for stmt in &bl.block.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
        }
        syn_verus::Expr::If(i) => {
            collect_expr_ghosts(&i.cond, parent_name, out);
            for stmt in &i.then_branch.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
            if let Some((_, ref else_expr)) = i.else_branch {
                collect_expr_ghosts(else_expr, parent_name, out);
            }
        }
        syn_verus::Expr::Match(m) => {
            collect_expr_ghosts(&m.expr, parent_name, out);
            for arm in &m.arms {
                if let Some((_, ref gexpr)) = arm.guard {
                    collect_expr_ghosts(gexpr, parent_name, out);
                }
                collect_expr_ghosts(&arm.body, parent_name, out);
            }
        }
        syn_verus::Expr::While(w) => {
            if let Some(ref inv) = w.invariant {
                for expr in &inv.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::Invariant,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref ie) = w.invariant_ensures {
                for expr in &ie.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::InvariantEnsures,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref ieb) = w.invariant_except_break {
                for expr in &ieb.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::InvariantExceptBreak,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref d) = w.decreases {
                for expr in &d.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::Decreases,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref ens) = w.ensures {
                for expr in &ens.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::LoopEnsures,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            for stmt in &w.body.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
        }
        syn_verus::Expr::ForLoop(fl) => {
            if let Some(ref inv) = fl.invariant {
                for expr in &inv.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::Invariant,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref d) = fl.decreases {
                for expr in &d.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::Decreases,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            for stmt in &fl.body.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
        }
        syn_verus::Expr::Loop(l) => {
            if let Some(ref inv) = l.invariant {
                for expr in &inv.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::Invariant,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref ie) = l.invariant_ensures {
                for expr in &ie.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::InvariantEnsures,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref ieb) = l.invariant_except_break {
                for expr in &ieb.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::InvariantExceptBreak,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref d) = l.decreases {
                for expr in &d.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::Decreases,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            if let Some(ref ens) = l.ensures {
                for expr in &ens.exprs.exprs {
                    let (sl, sc, el, ec) = span_to_loc(expr.span());
                    out.push(VerusSegment {
                        kind: SegmentKind::LoopEnsures,
                        name: parent_name.to_string(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: expr.to_token_stream().to_string(),
                    });
                }
            }
            for stmt in &l.body.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
        }
        syn_verus::Expr::TryBlock(t) => {
            for stmt in &t.block.stmts {
                collect_stmt_ghosts(stmt, parent_name, out);
            }
        }
        syn_verus::Expr::Closure(cl) => {
            collect_expr_ghosts(&cl.body, parent_name, out);
        }
        _ => {}
    }
}

fn collect_stmt_ghosts(stmt: &syn_verus::Stmt, parent_name: &str, out: &mut Vec<VerusSegment>) {
    match stmt {
        syn_verus::Stmt::Expr(e, _) => collect_expr_ghosts(e, parent_name, out),
        syn_verus::Stmt::Local(l) => {
            if let Some(ref init) = l.init {
                collect_expr_ghosts(&init.expr, parent_name, out);
            }
        }
        syn_verus::Stmt::Item(i) => collect_item_segments(i, "", out),
        syn_verus::Stmt::Macro(_) => {}
    }
}

/// Main entry: collect all segments from a top-level item.
fn collect_item_segments(item: &syn_verus::Item, namespace: &str, out: &mut Vec<VerusSegment>) {
    match item {
        syn_verus::Item::Fn(f) => {
            let name = if namespace.is_empty() {
                f.sig.ident.to_string()
            } else {
                format!("{}::{}", namespace, f.sig.ident)
            };
            let kind = fn_mode_to_kind(&f.sig.mode);
            let (sl, sc, el, ec) = span_to_loc(f.span());
            out.push(VerusSegment {
                kind, name: name.clone(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
            collect_sig_ghosts(&f.sig, &name, out);
            for stmt in &f.block.stmts {
                collect_stmt_ghosts(stmt, &name, out);
            }
        }
        syn_verus::Item::Struct(s) => {
            let name = if namespace.is_empty() {
                s.ident.to_string()
            } else {
                format!("{}::{}", namespace, s.ident)
            };
            let (sl, sc, el, ec) = span_to_loc(s.span());
            out.push(VerusSegment {
                kind: SegmentKind::Struct,
                name,
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
        }
        syn_verus::Item::Enum(e) => {
            let name = if namespace.is_empty() {
                e.ident.to_string()
            } else {
                format!("{}::{}", namespace, e.ident)
            };
            let (sl, sc, el, ec) = span_to_loc(e.span());
            out.push(VerusSegment {
                kind: SegmentKind::Enum,
                name,
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
        }
        syn_verus::Item::Type(t) => {
            let name = if namespace.is_empty() {
                t.ident.to_string()
            } else {
                format!("{}::{}", namespace, t.ident)
            };
            let (sl, sc, el, ec) = span_to_loc(t.span());
            out.push(VerusSegment {
                kind: SegmentKind::TypeAlias,
                name,
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
        }
        syn_verus::Item::Trait(t) => {
            let trait_name = if namespace.is_empty() {
                t.ident.to_string()
            } else {
                format!("{}::{}", namespace, t.ident)
            };
            let (sl, sc, el, ec) = span_to_loc(t.span());
            out.push(VerusSegment {
                kind: SegmentKind::Trait,
                name: trait_name.clone(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
            for ti in &t.items {
                if let syn_verus::TraitItem::Fn(m) = ti {
                    let fn_name = format!("{}::{}", trait_name, m.sig.ident);
                    let kind = fn_mode_to_kind(&m.sig.mode);
                    let (sl, sc, el, ec) = span_to_loc(m.span());
                    out.push(VerusSegment {
                        kind, name: fn_name.clone(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
                    });
                    collect_sig_ghosts(&m.sig, &fn_name, out);
                    if let Some(ref default_block) = m.default {
                        for stmt in &default_block.stmts {
                            collect_stmt_ghosts(stmt, &fn_name, out);
                        }
                    }
                }
            }
        }
        syn_verus::Item::Impl(i) => {
            let impl_name = type_path_to_string(&i.self_ty);
            let qualified_owner = qualify_impl_owner(&impl_name, namespace);
            let impl_label = if let Some((_, ref trait_path, _)) = i.trait_ {
                let trait_name = trait_path.segments.iter()
                    .map(|s| s.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::");
                format!("<{} as {}>", impl_name, trait_name)
            } else {
                impl_name.clone()
            };
            let full_impl_name = if namespace.is_empty() {
                impl_label.clone()
            } else {
                format!("{}::{}", namespace, impl_label)
            };
            let (sl, sc, el, ec) = span_to_loc(i.span());
            out.push(VerusSegment {
                kind: SegmentKind::Impl,
                name: full_impl_name.clone(),
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
            for ii in &i.items {
                if let syn_verus::ImplItem::Fn(m) = ii {
                    let fn_name = format!("{}::{}", qualified_owner, m.sig.ident);
                    let kind = fn_mode_to_kind(&m.sig.mode);
                    let (sl, sc, el, ec) = span_to_loc(m.span());
                    out.push(VerusSegment {
                        kind, name: fn_name.clone(),
                        start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
                    });
                    collect_sig_ghosts(&m.sig, &fn_name, out);
                    for stmt in &m.block.stmts {
                        collect_stmt_ghosts(stmt, &fn_name, out);
                    }
                }
            }
        }
        syn_verus::Item::Macro(m) => {
            let name = m.ident.as_ref()
                .map(|id| id.to_string())
                .unwrap_or_else(|| {
                    m.mac.path.segments.iter()
                        .map(|s| s.ident.to_string())
                        .collect::<Vec<_>>()
                        .join("::")
                });
            // Skip the outer `verus!` macro itself — its contents are parsed separately
            if name == "verus" {
                return;
            }
            let (sl, sc, el, ec) = span_to_loc(m.span());
            out.push(VerusSegment {
                kind: SegmentKind::Macro,
                name,
                start_line: sl, start_col: sc, end_line: el, end_col: ec, text: String::new(),
            });
        }
        syn_verus::Item::Mod(m) => {
            // Descend into nested module bodies so segments inside them are
            // surfaced with a fully-qualified name (e.g. ``M::N::fn_name``).
            // Without this arm, anything wrapped in ``mod ... { ... }`` is
            // silently dropped — and downstream tooling (the spec-equivalence
            // harness generator) depends on ``list`` for clauses, so the
            // resulting harness would have no equivalence checks for them.
            if let Some((_, items)) = &m.content {
                let child_ns = if namespace.is_empty() {
                    m.ident.to_string()
                } else {
                    format!("{}::{}", namespace, m.ident)
                };
                for it in items {
                    collect_item_segments(it, &child_ns, out);
                }
            }
        }
        _ => {}
    }
}

/// Parse a file and return all Verus segments.
pub fn flist_segments(filepath: &PathBuf) -> Result<Vec<VerusSegment>, Error> {
    fextract_verus_macro(filepath).map(|(files, _)| {
        let mut segments = Vec::new();
        for file in &files {
            for item in &file.items {
                collect_item_segments(item, "", &mut segments);
            }
        }
        segments
    })
}

/// Output segments as a human-readable text list.
pub fn print_segments_text(segments: &[VerusSegment]) {
    for seg in segments {
        println!(
            "{}:{}:(({}, {}), ({}, {}))",
            seg.kind.label(),
            seg.name,
            seg.start_line,
            seg.start_col,
            seg.end_line,
            seg.end_col,
        );
    }
}

/// Output segments as JSON.
pub fn print_segments_json(segments: &[VerusSegment]) {
    let json_segments: Vec<serde_json::Value> = segments
        .iter()
        .map(|seg| {
            json!({
                "kind": seg.kind.label(),
                "name": seg.name,
                "start_line": seg.start_line,
                "start_col": seg.start_col,
                "end_line": seg.end_line,
                "end_col": seg.end_col,
                "text": seg.text,
            })
        })
        .collect();
    println!("{}", serde_json::to_string_pretty(&json_segments).unwrap());
}
