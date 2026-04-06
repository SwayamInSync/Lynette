use serde_json::json;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::list_segments::SegmentKind;
use crate::utils::*;

/// A dependency record: a function and the spec_fns it references.
#[derive(Debug)]
pub struct FnDependency {
    pub name: String,
    pub kind: SegmentKind,
    pub depends_on: Vec<String>,
}

// ---------------------------------------------------------------------------
// AST-based identifier collection
// ---------------------------------------------------------------------------

/// Collect all identifiers referenced in an expression (function calls, method calls, paths).
fn collect_idents_expr(expr: &syn_verus::Expr, out: &mut HashSet<String>) {
    match expr {
        syn_verus::Expr::Call(call) => {
            collect_idents_expr(&call.func, out);
            for arg in &call.args {
                collect_idents_expr(arg, out);
            }
        }
        syn_verus::Expr::MethodCall(m) => {
            out.insert(m.method.to_string());
            collect_idents_expr(&m.receiver, out);
            for arg in &m.args {
                collect_idents_expr(arg, out);
            }
        }
        syn_verus::Expr::Path(p) => {
            // Collect each segment of the path: e.g. `Foo::bar` -> "Foo", "bar", "Foo::bar"
            let segments: Vec<String> = p.path.segments.iter()
                .map(|s| s.ident.to_string())
                .collect();
            for s in &segments {
                out.insert(s.clone());
            }
            if segments.len() > 1 {
                out.insert(segments.join("::"));
            }
        }
        syn_verus::Expr::Binary(b) => {
            collect_idents_expr(&b.left, out);
            collect_idents_expr(&b.right, out);
        }
        syn_verus::Expr::Unary(u) => {
            collect_idents_expr(&u.expr, out);
        }
        syn_verus::Expr::Block(bl) => {
            for stmt in &bl.block.stmts {
                collect_idents_stmt(stmt, out);
            }
        }
        syn_verus::Expr::If(i) => {
            collect_idents_expr(&i.cond, out);
            for stmt in &i.then_branch.stmts {
                collect_idents_stmt(stmt, out);
            }
            if let Some((_, ref else_expr)) = i.else_branch {
                collect_idents_expr(else_expr, out);
            }
        }
        syn_verus::Expr::Match(m) => {
            collect_idents_expr(&m.expr, out);
            for arm in &m.arms {
                if let Some((_, ref gexpr)) = arm.guard {
                    collect_idents_expr(gexpr, out);
                }
                collect_idents_expr(&arm.body, out);
            }
        }
        syn_verus::Expr::While(w) => {
            collect_idents_expr(&w.cond, out);
            for stmt in &w.body.stmts {
                collect_idents_stmt(stmt, out);
            }
            // Also check invariants
            if let Some(ref inv) = w.invariant {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
        }
        syn_verus::Expr::ForLoop(fl) => {
            collect_idents_expr(&fl.expr, out);
            for stmt in &fl.body.stmts {
                collect_idents_stmt(stmt, out);
            }
            if let Some(ref inv) = fl.invariant {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
        }
        syn_verus::Expr::Loop(l) => {
            for stmt in &l.body.stmts {
                collect_idents_stmt(stmt, out);
            }
            if let Some(ref inv) = l.invariant {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
        }
        syn_verus::Expr::Closure(cl) => {
            collect_idents_expr(&cl.body, out);
        }
        syn_verus::Expr::Field(f) => {
            collect_idents_expr(&f.base, out);
        }
        syn_verus::Expr::Index(i) => {
            collect_idents_expr(&i.expr, out);
            collect_idents_expr(&i.index, out);
        }
        syn_verus::Expr::Tuple(t) => {
            for elem in &t.elems {
                collect_idents_expr(elem, out);
            }
        }
        syn_verus::Expr::Array(a) => {
            for elem in &a.elems {
                collect_idents_expr(elem, out);
            }
        }
        syn_verus::Expr::Paren(p) => {
            collect_idents_expr(&p.expr, out);
        }
        syn_verus::Expr::Group(g) => {
            collect_idents_expr(&g.expr, out);
        }
        syn_verus::Expr::Reference(r) => {
            collect_idents_expr(&r.expr, out);
        }
        syn_verus::Expr::Cast(c) => {
            collect_idents_expr(&c.expr, out);
        }
        syn_verus::Expr::Return(r) => {
            if let Some(ref expr) = r.expr {
                collect_idents_expr(expr, out);
            }
        }
        syn_verus::Expr::Assign(a) => {
            collect_idents_expr(&a.left, out);
            collect_idents_expr(&a.right, out);
        }
        syn_verus::Expr::Range(r) => {
            if let Some(ref start) = r.start {
                collect_idents_expr(start, out);
            }
            if let Some(ref end) = r.end {
                collect_idents_expr(end, out);
            }
        }
        syn_verus::Expr::Struct(s) => {
            // Collect the struct path
            let segments: Vec<String> = s.path.segments.iter()
                .map(|seg| seg.ident.to_string())
                .collect();
            for seg in &segments {
                out.insert(seg.clone());
            }
            for field in &s.fields {
                collect_idents_expr(&field.expr, out);
            }
            if let Some(ref rest) = s.rest {
                collect_idents_expr(rest, out);
            }
        }
        syn_verus::Expr::Repeat(r) => {
            collect_idents_expr(&r.expr, out);
            collect_idents_expr(&r.len, out);
        }
        syn_verus::Expr::Try(t) => {
            collect_idents_expr(&t.expr, out);
        }
        syn_verus::Expr::TryBlock(t) => {
            for stmt in &t.block.stmts {
                collect_idents_stmt(stmt, out);
            }
        }
        syn_verus::Expr::Yield(y) => {
            if let Some(ref expr) = y.expr {
                collect_idents_expr(expr, out);
            }
        }
        syn_verus::Expr::Let(l) => {
            collect_idents_expr(&l.expr, out);
        }
        syn_verus::Expr::Break(b) => {
            if let Some(ref expr) = b.expr {
                collect_idents_expr(expr, out);
            }
        }
        // Assert/assume/assert_forall in Verus
        syn_verus::Expr::Assert(a) => {
            collect_idents_expr(&a.expr, out);
            if let Some(ref body) = a.body {
                for stmt in &body.stmts {
                    collect_idents_stmt(stmt, out);
                }
            }
        }
        syn_verus::Expr::AssertForall(a) => {
            collect_idents_expr(&a.expr, out);
            for stmt in &a.body.stmts {
                collect_idents_stmt(stmt, out);
            }
        }
        syn_verus::Expr::Assume(a) => {
            collect_idents_expr(&a.expr, out);
        }
        _ => {}
    }
}

fn collect_idents_stmt(stmt: &syn_verus::Stmt, out: &mut HashSet<String>) {
    match stmt {
        syn_verus::Stmt::Expr(e, _) => collect_idents_expr(e, out),
        syn_verus::Stmt::Local(l) => {
            if let Some(ref init) = l.init {
                collect_idents_expr(&init.expr, out);
            }
        }
        syn_verus::Stmt::Item(i) => collect_idents_item(i, out),
        syn_verus::Stmt::Macro(_) => {}
    }
}

fn collect_idents_item(item: &syn_verus::Item, out: &mut HashSet<String>) {
    match item {
        syn_verus::Item::Fn(f) => {
            collect_idents_sig(&f.sig, out);
            for stmt in &f.block.stmts {
                collect_idents_stmt(stmt, out);
            }
        }
        _ => {}
    }
}

/// Collect identifiers from a function signature's spec clauses (requires, ensures, etc.)
fn collect_idents_sig(sig: &syn_verus::Signature, out: &mut HashSet<String>) {
    if let Some(ref r) = sig.spec.requires {
        for expr in &r.exprs.exprs {
            collect_idents_expr(expr, out);
        }
    }
    if let Some(ref e) = sig.spec.ensures {
        for expr in &e.exprs.exprs {
            collect_idents_expr(expr, out);
        }
    }
    if let Some(ref r) = sig.spec.recommends {
        for expr in &r.exprs.exprs {
            collect_idents_expr(expr, out);
        }
    }
    if let Some(ref d) = sig.spec.decreases {
        for expr in &d.decreases.exprs.exprs {
            collect_idents_expr(expr, out);
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level dependency analysis
// ---------------------------------------------------------------------------

/// Information about a function definition needed for dependency analysis.
struct FnInfo {
    name: String,
    kind: SegmentKind,
    /// The impl/trait type this function belongs to (e.g. "Foo" for methods in `impl Foo`).
    /// `None` for free functions.
    impl_type: Option<String>,
    /// All identifiers referenced by this function (signature specs + body).
    referenced_idents: HashSet<String>,
}

/// Walk a top-level item and collect FnInfo for each spec_fn / proof_fn.
fn collect_fn_infos(item: &syn_verus::Item, namespace: &str, out: &mut Vec<FnInfo>) {
    match item {
        syn_verus::Item::Fn(f) => {
            let name = if namespace.is_empty() {
                f.sig.ident.to_string()
            } else {
                format!("{}::{}", namespace, f.sig.ident)
            };
            let kind = match f.sig.mode {
                syn_verus::FnMode::Spec(_) => SegmentKind::SpecFn,
                syn_verus::FnMode::SpecChecked(_) => SegmentKind::SpecCheckedFn,
                syn_verus::FnMode::Proof(_) => SegmentKind::ProofFn,
                syn_verus::FnMode::ProofAxiom(_) => SegmentKind::ProofAxiomFn,
                syn_verus::FnMode::Exec(_) => SegmentKind::ExecFn,
                syn_verus::FnMode::Default => SegmentKind::DefaultFn,
            };

            let mut idents = HashSet::new();
            collect_idents_sig(&f.sig, &mut idents);
            for stmt in &f.block.stmts {
                collect_idents_stmt(stmt, &mut idents);
            }

            out.push(FnInfo { name, kind, impl_type: None, referenced_idents: idents });
        }
        syn_verus::Item::Impl(i) => {
            let impl_name = type_path_to_string(&i.self_ty);
            for ii in &i.items {
                if let syn_verus::ImplItem::Fn(m) = ii {
                    let fn_name = format!("{}::{}", impl_name, m.sig.ident);
                    let kind = match m.sig.mode {
                        syn_verus::FnMode::Spec(_) => SegmentKind::SpecFn,
                        syn_verus::FnMode::SpecChecked(_) => SegmentKind::SpecCheckedFn,
                        syn_verus::FnMode::Proof(_) => SegmentKind::ProofFn,
                        syn_verus::FnMode::ProofAxiom(_) => SegmentKind::ProofAxiomFn,
                        syn_verus::FnMode::Exec(_) => SegmentKind::ExecFn,
                        syn_verus::FnMode::Default => SegmentKind::DefaultFn,
                    };

                    let mut idents = HashSet::new();
                    collect_idents_sig(&m.sig, &mut idents);
                    for stmt in &m.block.stmts {
                        collect_idents_stmt(stmt, &mut idents);
                    }

                    out.push(FnInfo { name: fn_name, kind, impl_type: Some(impl_name.clone()), referenced_idents: idents });
                }
            }
        }
        syn_verus::Item::Trait(t) => {
            let trait_name = if namespace.is_empty() {
                t.ident.to_string()
            } else {
                format!("{}::{}", namespace, t.ident)
            };
            for ti in &t.items {
                if let syn_verus::TraitItem::Fn(m) = ti {
                    let fn_name = format!("{}::{}", trait_name, m.sig.ident);
                    let kind = match m.sig.mode {
                        syn_verus::FnMode::Spec(_) => SegmentKind::SpecFn,
                        syn_verus::FnMode::SpecChecked(_) => SegmentKind::SpecCheckedFn,
                        syn_verus::FnMode::Proof(_) => SegmentKind::ProofFn,
                        syn_verus::FnMode::ProofAxiom(_) => SegmentKind::ProofAxiomFn,
                        syn_verus::FnMode::Exec(_) => SegmentKind::ExecFn,
                        syn_verus::FnMode::Default => SegmentKind::DefaultFn,
                    };

                    let mut idents = HashSet::new();
                    collect_idents_sig(&m.sig, &mut idents);
                    if let Some(ref default_block) = m.default {
                        for stmt in &default_block.stmts {
                            collect_idents_stmt(stmt, &mut idents);
                        }
                    }

                    out.push(FnInfo { name: fn_name, kind, impl_type: Some(trait_name.clone()), referenced_idents: idents });
                }
            }
        }
        _ => {}
    }
}

/// Parse a Verus file and compute dependency map.
///
/// Returns a list of FnDependency records for each proof_fn and spec_fn,
/// showing which other spec_fns (defined in this file) each one references.
pub fn fcompute_deps(filepath: &PathBuf) -> Result<Vec<FnDependency>, Error> {
    fextract_verus_macro(filepath).map(|(files, _)| {
        let mut fn_infos: Vec<FnInfo> = Vec::new();
        for file in &files {
            for item in &file.items {
                collect_fn_infos(item, "", &mut fn_infos);
            }
        }

        // Build a set of known spec_fn names (both qualified and bare)
        // Maps: bare_name -> [qualified_name, ...]
        let mut spec_by_bare: HashMap<String, Vec<String>> = HashMap::new();
        let mut spec_qualified: HashSet<String> = HashSet::new();
        for info in &fn_infos {
            if info.kind == SegmentKind::SpecFn || info.kind == SegmentKind::SpecCheckedFn {
                spec_qualified.insert(info.name.clone());
                let bare = info.name.rsplit("::").next().unwrap_or(&info.name).to_string();
                spec_by_bare.entry(bare).or_default().push(info.name.clone());
            }
        }

        // For each function, resolve which spec_fns it references
        let mut deps = Vec::new();
        for info in &fn_infos {
            let mut depends_on: Vec<String> = Vec::new();

            // Check each referenced ident against known spec_fn names
            for ident in &info.referenced_idents {
                // Direct qualified match: ident is "Foo::bar" and that's a known spec_fn
                if spec_qualified.contains(ident) && *ident != info.name {
                    depends_on.push(ident.clone());
                    continue;
                }
                // Bare name match: ident is "bar" and there are spec_fns with that bare name.
                // Heuristic: if the calling function is inside `impl Foo`, prefer
                // `Foo::bar` over other `Type::bar` candidates. Only fall back to
                // all candidates when none share the same impl type.
                if let Some(qualified_list) = spec_by_bare.get(ident) {
                    let candidates: Vec<&String> = if let Some(ref impl_ty) = info.impl_type {
                        let prefix = format!("{}::", impl_ty);
                        let same_impl: Vec<&String> = qualified_list.iter()
                            .filter(|q| q.starts_with(&prefix))
                            .collect();
                        if same_impl.is_empty() { qualified_list.iter().collect() } else { same_impl }
                    } else {
                        qualified_list.iter().collect()
                    };
                    for q in candidates {
                        if *q != info.name && !depends_on.contains(q) {
                            depends_on.push(q.clone());
                        }
                    }
                }
            }

            depends_on.sort();
            depends_on.dedup();

            deps.push(FnDependency {
                name: info.name.clone(),
                kind: info.kind,
                depends_on,
            });
        }

        deps
    })
}

/// Print dependency results as JSON.
pub fn print_deps_json(deps: &[FnDependency]) {
    let json_deps: Vec<serde_json::Value> = deps
        .iter()
        .map(|dep| {
            json!({
                "name": dep.name,
                "kind": dep.kind.label(),
                "depends_on": dep.depends_on,
            })
        })
        .collect();
    println!("{}", serde_json::to_string_pretty(&json_deps).unwrap());
}

/// Print dependency results as human-readable text.
pub fn print_deps_text(deps: &[FnDependency]) {
    for dep in deps {
        if dep.depends_on.is_empty() {
            continue;
        }
        println!("{} ({}):", dep.name, dep.kind.label());
        for d in &dep.depends_on {
            println!("  -> {}", d);
        }
    }
}
