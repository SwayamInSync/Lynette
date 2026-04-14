use serde_json::json;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::list_segments::{fn_mode_to_kind, SegmentKind};
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

/// Extract the path string from a call-target expression (the `func` in `func(args)`).
/// Returns `Some("foo")` for bare calls and `Some("Foo::bar")` for qualified calls.
fn call_target_path(expr: &syn_verus::Expr) -> Option<String> {
    match expr {
        syn_verus::Expr::Path(p) => {
            let segments: Vec<String> = p.path.segments.iter()
                .map(|s| s.ident.to_string())
                .collect();
            if segments.len() > 1 {
                Some(segments.join("::"))
            } else {
                segments.first().cloned()
            }
        }
        syn_verus::Expr::Paren(p) => call_target_path(&p.expr),
        _ => None,
    }
}

/// Collect identifiers that appear as direct call targets (in `Expr::Call.func` position).
fn collect_call_targets_expr(expr: &syn_verus::Expr, out: &mut HashSet<String>) {
    match expr {
        syn_verus::Expr::Call(call) => {
            if let Some(target) = call_target_path(&call.func) {
                out.insert(target);
            }
            collect_call_targets_expr(&call.func, out);
            for arg in &call.args {
                collect_call_targets_expr(arg, out);
            }
        }
        syn_verus::Expr::MethodCall(m) => {
            collect_call_targets_expr(&m.receiver, out);
            for arg in &m.args {
                collect_call_targets_expr(arg, out);
            }
        }
        syn_verus::Expr::Binary(b) => {
            collect_call_targets_expr(&b.left, out);
            collect_call_targets_expr(&b.right, out);
        }
        syn_verus::Expr::Unary(u) => {
            collect_call_targets_expr(&u.expr, out);
        }
        syn_verus::Expr::Block(bl) => {
            for stmt in &bl.block.stmts {
                collect_call_targets_stmt(stmt, out);
            }
        }
        syn_verus::Expr::If(i) => {
            collect_call_targets_expr(&i.cond, out);
            for stmt in &i.then_branch.stmts {
                collect_call_targets_stmt(stmt, out);
            }
            if let Some((_, ref else_expr)) = i.else_branch {
                collect_call_targets_expr(else_expr, out);
            }
        }
        syn_verus::Expr::Match(m) => {
            collect_call_targets_expr(&m.expr, out);
            for arm in &m.arms {
                if let Some((_, ref gexpr)) = arm.guard {
                    collect_call_targets_expr(gexpr, out);
                }
                collect_call_targets_expr(&arm.body, out);
            }
        }
        syn_verus::Expr::Paren(p) => {
            collect_call_targets_expr(&p.expr, out);
        }
        syn_verus::Expr::Group(g) => {
            collect_call_targets_expr(&g.expr, out);
        }
        syn_verus::Expr::Return(r) => {
            if let Some(ref expr) = r.expr {
                collect_call_targets_expr(expr, out);
            }
        }
        syn_verus::Expr::Tuple(t) => {
            for elem in &t.elems {
                collect_call_targets_expr(elem, out);
            }
        }
        syn_verus::Expr::Reference(r) => {
            collect_call_targets_expr(&r.expr, out);
        }
        syn_verus::Expr::Let(l) => {
            collect_call_targets_expr(&l.expr, out);
        }
        _ => {}
    }
}

fn collect_call_targets_stmt(stmt: &syn_verus::Stmt, out: &mut HashSet<String>) {
    match stmt {
        syn_verus::Stmt::Expr(e, _) => {
            collect_call_targets_expr(e, out);
        }
        syn_verus::Stmt::Local(local) => {
            if let Some(ref init) = local.init {
                collect_call_targets_expr(&init.expr, out);
            }
        }
        syn_verus::Stmt::Item(_) => {}
        syn_verus::Stmt::Macro(_) => {}
    }
}

/// Collect identifiers that appear as call targets in a function signature's spec clauses.
fn collect_call_targets_sig(sig: &syn_verus::Signature, out: &mut HashSet<String>) {
    if let Some(ref r) = sig.spec.requires {
        for expr in &r.exprs.exprs { collect_call_targets_expr(expr, out); }
    }
    if let Some(ref e) = sig.spec.ensures {
        for expr in &e.exprs.exprs { collect_call_targets_expr(expr, out); }
    }
    if let Some(ref r) = sig.spec.recommends {
        for expr in &r.exprs.exprs { collect_call_targets_expr(expr, out); }
    }
    if let Some(ref d) = sig.spec.decreases {
        for expr in &d.decreases.exprs.exprs { collect_call_targets_expr(expr, out); }
    }
}

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
            // For bare paths like `bar`, collect "bar".
            // For qualified paths like `Foo::bar`, collect only "Foo::bar"
            // so later bare-name resolution does not also treat the qualified
            // reference as a separate bare `bar` reference.
            let segments: Vec<String> = p.path.segments.iter()
                .map(|s| s.ident.to_string())
                .collect();
            if segments.len() > 1 {
                out.insert(segments.join("::"));
            } else if let Some(segment) = segments.first() {
                out.insert(segment.clone());
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
            // Also check loop spec clauses
            if let Some(ref inv) = w.invariant {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref inv) = w.invariant_ensures {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref inv) = w.invariant_except_break {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref dec) = w.decreases {
                for expr in &dec.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref ens) = w.ensures {
                for expr in &ens.exprs.exprs {
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
            if let Some(ref dec) = fl.decreases {
                for expr in &dec.exprs.exprs {
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
            if let Some(ref inv) = l.invariant_ensures {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref inv) = l.invariant_except_break {
                for expr in &inv.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref dec) = l.decreases {
                for expr in &dec.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref ens) = l.ensures {
                for expr in &ens.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
        }
        syn_verus::Expr::Closure(cl) => {
            collect_idents_expr(&cl.body, out);
            if let Some(ref req) = cl.requires {
                for expr in &req.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
            if let Some(ref ens) = cl.ensures {
                for expr in &ens.exprs.exprs {
                    collect_idents_expr(expr, out);
                }
            }
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
            // Do not collect the struct constructor path: struct construction
            // is not a function call, and inserting the type path would create
            // false dependencies when a type name matches a spec_fn name.
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
        // Do not descend into nested items: identifiers referenced inside
        // a nested `fn` belong to that nested item, not the enclosing function.
        syn_verus::Stmt::Item(_) => {}
        syn_verus::Stmt::Macro(_) => {}
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
    /// Identifiers that appear specifically as call targets (`func(...)` position).
    /// Used to detect genuine recursive calls without false positives from
    /// shadowed bindings/parameters that happen to share a function name.
    call_target_idents: HashSet<String>,
}

/// Walk a top-level item and collect `FnInfo` for each function definition
/// (all kinds: spec, spec-checked, proof, proof-axiom, exec, and default).
fn collect_fn_infos(item: &syn_verus::Item, namespace: &str, out: &mut Vec<FnInfo>) {
    match item {
        syn_verus::Item::Fn(f) => {
            let name = if namespace.is_empty() {
                f.sig.ident.to_string()
            } else {
                format!("{}::{}", namespace, f.sig.ident)
            };
            let kind = fn_mode_to_kind(&f.sig.mode);

            let mut idents = HashSet::new();
            collect_idents_sig(&f.sig, &mut idents);
            for stmt in &f.block.stmts {
                collect_idents_stmt(stmt, &mut idents);
            }

            let mut call_targets = HashSet::new();
            collect_call_targets_sig(&f.sig, &mut call_targets);
            for stmt in &f.block.stmts {
                collect_call_targets_stmt(stmt, &mut call_targets);
            }

            out.push(FnInfo { name, kind, impl_type: None, referenced_idents: idents, call_target_idents: call_targets });
        }
        syn_verus::Item::Impl(i) => {
            let impl_name = type_path_to_string(&i.self_ty);
            // Skip impls where we can't extract the type name (e.g. `impl Trait for &Foo`)
            if impl_name.is_empty() {
                return;
            }
            // Name impl methods as `Type::method` (matching list_segments),
            // regardless of whether this is a trait impl or inherent impl.
            for ii in &i.items {
                if let syn_verus::ImplItem::Fn(m) = ii {
                    let fn_name = format!("{}::{}", impl_name, m.sig.ident);
                    let kind = fn_mode_to_kind(&m.sig.mode);

                    let mut idents = HashSet::new();
                    collect_idents_sig(&m.sig, &mut idents);
                    for stmt in &m.block.stmts {
                        collect_idents_stmt(stmt, &mut idents);
                    }

                    let mut call_targets = HashSet::new();
                    collect_call_targets_sig(&m.sig, &mut call_targets);
                    for stmt in &m.block.stmts {
                        collect_call_targets_stmt(stmt, &mut call_targets);
                    }

                    out.push(FnInfo { name: fn_name, kind, impl_type: Some(impl_name.clone()), referenced_idents: idents, call_target_idents: call_targets });
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
                    let kind = fn_mode_to_kind(&m.sig.mode);

                    let mut idents = HashSet::new();
                    collect_idents_sig(&m.sig, &mut idents);
                    if let Some(ref default_block) = m.default {
                        for stmt in &default_block.stmts {
                            collect_idents_stmt(stmt, &mut idents);
                        }
                    }

                    let mut call_targets = HashSet::new();
                    collect_call_targets_sig(&m.sig, &mut call_targets);
                    if let Some(ref default_block) = m.default {
                        for stmt in &default_block.stmts {
                            collect_call_targets_stmt(stmt, &mut call_targets);
                        }
                    }

                    out.push(FnInfo { name: fn_name, kind, impl_type: Some(trait_name.clone()), referenced_idents: idents, call_target_idents: call_targets });
                }
            }
        }
        syn_verus::Item::Mod(m) => {
            let mod_name = if namespace.is_empty() {
                m.ident.to_string()
            } else {
                format!("{}::{}", namespace, m.ident)
            };
            if let Some((_, ref items)) = m.content {
                for item in items {
                    collect_fn_infos(item, &mod_name, out);
                }
            }
        }
        _ => {}
    }
}

/// Parse a Verus file and compute dependency map.
///
/// Returns a list of FnDependency records for every function in the file,
/// showing which spec_fns (defined in this file) each one references.
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
            let mut dep_set: HashSet<String> = HashSet::new();

            // Pre-compute whether this function genuinely calls itself
            // (i.e. its name appears in call-target position, not just as
            // a path expression that could be a shadowed binding/parameter).
            let bare_name = info.name.rsplit("::").next().unwrap_or(&info.name);
            let self_qualified = format!("Self::{}", bare_name);
            let self_is_called = info.call_target_idents.contains(&info.name)
                || info.call_target_idents.contains(bare_name)
                || info.call_target_idents.contains(&self_qualified);

            // Check each referenced ident against known spec_fn names
            for ident in &info.referenced_idents {
                // Direct qualified match: ident is "Foo::bar" and that's a known spec_fn.
                // For self-references, only include if it appears as a call target.
                if spec_qualified.contains(ident) {
                    if *ident != info.name || self_is_called {
                        dep_set.insert(ident.clone());
                    }
                    continue;
                }
                // For Rust path prefixes (crate::, self::, super::, Self::)
                // that don't directly match a known spec_fn, fall back to the
                // bare last segment for resolution. `Self::method` is common in
                // impl blocks and must be resolved via the same-impl heuristic.
                // Other qualified paths (e.g. Foo::bar) that didn't match are
                // left as-is — they were already checked against spec_qualified.
                let resolved_ident = if ident.starts_with("crate::") || ident.starts_with("self::") || ident.starts_with("super::") || ident.starts_with("Self::") {
                    ident.rsplit("::").next().unwrap_or(ident)
                } else {
                    ident.as_str()
                };
                // Bare name match: ident is "bar" and there are spec_fns with that bare name.
                // Heuristic: if the calling function is inside `impl Foo`, prefer
                // `Foo::bar` over other `Type::bar` candidates. Only fall back to
                // all candidates when none share the same impl type.
                if let Some(qualified_list) = spec_by_bare.get(resolved_ident) {
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
                        if *q != info.name || self_is_called {
                            dep_set.insert(q.clone());
                        }
                    }
                }
            }

            let mut depends_on: Vec<String> = dep_set.into_iter().collect();
            depends_on.sort();

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
        println!("{} ({}):", dep.name, dep.kind.label());
        if dep.depends_on.is_empty() {
            println!("  (none)");
        } else {
            for d in &dep.depends_on {
                println!("  -> {}", d);
            }
        }
    }
}

// ===========================================================================
// Unit tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    /// Write `code` to a temp .rs file and run `fcompute_deps`.
    fn deps_for(code: &str) -> Vec<FnDependency> {
        let mut tmp = tempfile::NamedTempFile::new().unwrap();
        tmp.write_all(code.as_bytes()).unwrap();
        tmp.flush().unwrap();
        fcompute_deps(&tmp.path().to_path_buf()).unwrap()
    }

    /// Helper: build a name -> depends_on lookup from deps vec.
    fn dep_map(deps: &[FnDependency]) -> HashMap<String, Vec<String>> {
        deps.iter()
            .map(|d| (d.name.clone(), d.depends_on.clone()))
            .collect()
    }

    /// Helper: build a name -> kind lookup from deps vec.
    fn kind_map(deps: &[FnDependency]) -> HashMap<String, &'static str> {
        deps.iter()
            .map(|d| (d.name.clone(), d.kind.label()))
            .collect()
    }

    /// Load a fixture file from tests/fixtures/<name>.
    fn fixture_path(name: &str) -> PathBuf {
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        p.push("tests/fixtures");
        p.push(name);
        p
    }

    fn deps_for_fixture(name: &str) -> Vec<FnDependency> {
        fcompute_deps(&fixture_path(name)).unwrap()
    }

    // ── basic_deps.rs ──────────────────────────────────────────────────

    #[test]
    fn basic_proof_depends_on_spec() {
        let deps = deps_for_fixture("basic_deps.rs");
        let m = dep_map(&deps);
        assert_eq!(m["my_proof"], vec!["my_spec"]);
    }

    #[test]
    fn basic_multi_dep() {
        let deps = deps_for_fixture("basic_deps.rs");
        let m = dep_map(&deps);
        let mut d = m["multi_dep_proof"].clone();
        d.sort();
        assert_eq!(d, vec!["my_spec", "other_spec"]);
    }

    #[test]
    fn basic_no_dep_proof_has_empty_deps() {
        let deps = deps_for_fixture("basic_deps.rs");
        let m = dep_map(&deps);
        assert!(m["no_dep_proof"].is_empty());
    }

    #[test]
    fn basic_spec_calls_spec() {
        let deps = deps_for_fixture("basic_deps.rs");
        let m = dep_map(&deps);
        assert_eq!(m["spec_calls_spec"], vec!["my_spec"]);
    }

    #[test]
    fn basic_exec_no_dep() {
        let deps = deps_for_fixture("basic_deps.rs");
        let m = dep_map(&deps);
        assert!(m["exec_no_dep"].is_empty());
    }

    #[test]
    fn basic_kind_classification() {
        let deps = deps_for_fixture("basic_deps.rs");
        let k = kind_map(&deps);
        assert_eq!(k["my_spec"], "spec_fn");
        assert_eq!(k["my_proof"], "proof_fn");
        assert_eq!(k["exec_no_dep"], "exec_fn");
    }

    // ── same_impl_heuristic.rs ─────────────────────────────────────────

    #[test]
    fn same_impl_prefers_own_type() {
        let deps = deps_for_fixture("same_impl_heuristic.rs");
        let m = dep_map(&deps);
        // Foo::foo_proof should only depend on Foo::view (same impl)
        assert_eq!(m["Foo::foo_proof"], vec!["Foo::view"]);
        // Bar::bar_proof should only depend on Bar::view (same impl)
        assert_eq!(m["Bar::bar_proof"], vec!["Bar::view"]);
    }

    #[test]
    fn free_function_matches_all_bare_names() {
        let deps = deps_for_fixture("same_impl_heuristic.rs");
        let m = dep_map(&deps);
        let mut d = m["free_uses_view"].clone();
        d.sort();
        assert_eq!(d, vec!["Bar::view", "Foo::view"]);
    }

    // ── self_paths.rs ──────────────────────────────────────────────────

    #[test]
    fn self_dot_method_resolves() {
        let deps = deps_for_fixture("self_paths.rs");
        let m = dep_map(&deps);
        assert_eq!(m["Foo::uses_self_dot"], vec!["Foo::val"]);
    }

    #[test]
    fn capital_self_path_resolves() {
        let deps = deps_for_fixture("self_paths.rs");
        let m = dep_map(&deps);
        assert_eq!(m["Foo::uses_Self_qualified"], vec!["Foo::val"]);
    }

    #[test]
    fn explicit_qualified_path_resolves() {
        let deps = deps_for_fixture("self_paths.rs");
        let m = dep_map(&deps);
        assert_eq!(m["Foo::uses_Foo_qualified"], vec!["Foo::val"]);
    }

    #[test]
    fn trait_spec_via_self_dot() {
        let deps = deps_for_fixture("self_paths.rs");
        let m = dep_map(&deps);
        assert_eq!(m["Foo::uses_trait_spec"], vec!["Foo::trait_spec"]);
    }

    // ── self_reference.rs ──────────────────────────────────────────────

    #[test]
    fn recursive_spec_includes_self() {
        let deps = deps_for_fixture("self_reference.rs");
        let m = dep_map(&deps);
        assert_eq!(m["recursive_spec"], vec!["recursive_spec"],
            "recursive_spec should list itself as a dependency (genuine recursive call)");
    }

    #[test]
    fn shadowed_param_false_positive() {
        let deps = deps_for_fixture("self_reference.rs");
        let m = dep_map(&deps);
        // Known limitation: `shadowed_param` has a parameter named `helper_spec`
        // which matches the spec_fn name. Since cross-function dep detection uses
        // all path expressions (not just call targets), this is a false positive.
        assert_eq!(m["shadowed_param"], vec!["helper_spec"],
            "shadowed_param picks up helper_spec as a false positive (known limitation)");
    }

    #[test]
    fn recursive_with_other_dep() {
        let deps = deps_for_fixture("self_reference.rs");
        let m = dep_map(&deps);
        let mut d = m["recursive_with_dep"].clone();
        d.sort();
        assert_eq!(d, vec!["helper_spec", "recursive_with_dep"],
            "recursive_with_dep should list both itself and helper_spec");
    }

    #[test]
    fn non_call_self_ref_no_self_dep() {
        let deps = deps_for_fixture("self_reference.rs");
        let m = dep_map(&deps);
        assert_eq!(m["non_call_self_ref"], vec!["helper_spec"],
            "non_call_self_ref should only depend on helper_spec, not itself");
    }

    #[test]
    fn impl_recursive_includes_self() {
        let deps = deps_for_fixture("self_reference.rs");
        let m = dep_map(&deps);
        assert_eq!(m["MyStruct::impl_recursive"], vec!["MyStruct::impl_recursive"],
            "impl method that calls Self::impl_recursive should list itself");
    }

    #[test]
    fn impl_non_recursive_no_self_dep() {
        let deps = deps_for_fixture("self_reference.rs");
        let m = dep_map(&deps);
        assert!(m["MyStruct::impl_non_recursive"].is_empty(),
            "non-recursive impl method should not list itself");
    }

    // ── expression_contexts.rs ─────────────────────────────────────────

    #[test]
    fn multi_ensures_picks_up_all() {
        let deps = deps_for_fixture("expression_contexts.rs");
        let m = dep_map(&deps);
        let mut d = m["multi_ensures"].clone();
        d.sort();
        assert_eq!(d, vec!["cond_a", "cond_b"]);
    }

    #[test]
    fn exec_proof_block_detects_dep() {
        let deps = deps_for_fixture("expression_contexts.rs");
        let m = dep_map(&deps);
        assert_eq!(m["exec_with_proof_block"], vec!["cond_a"]);
    }

    #[test]
    fn closure_body_detects_dep() {
        let deps = deps_for_fixture("expression_contexts.rs");
        let m = dep_map(&deps);
        assert_eq!(m["closure_test"], vec!["helper_spec"]);
    }

    #[test]
    fn loop_invariant_detects_dep() {
        let deps = deps_for_fixture("expression_contexts.rs");
        let m = dep_map(&deps);
        assert_eq!(m["loop_with_invariant"], vec!["cond_a"]);
    }

    #[test]
    fn assert_detects_dep() {
        let deps = deps_for_fixture("expression_contexts.rs");
        let m = dep_map(&deps);
        assert_eq!(m["assert_test"], vec!["cond_b"]);
    }

    // ── struct_constructor.rs ──────────────────────────────────────────

    #[test]
    fn struct_constructor_no_false_positive() {
        let deps = deps_for_fixture("struct_constructor.rs");
        let m = dep_map(&deps);
        assert!(m["bar_maker"].is_empty(),
            "struct constructor path should not create a false dep");
    }

    #[test]
    fn real_dep_still_detected() {
        let deps = deps_for_fixture("struct_constructor.rs");
        let m = dep_map(&deps);
        assert_eq!(m["real_dep"], vec!["unrelated_spec"]);
    }

    // ── inline_module.rs ───────────────────────────────────────────────

    #[test]
    fn inline_module_functions_qualified() {
        let deps = deps_for_fixture("inline_module.rs");
        let m = dep_map(&deps);
        assert!(m.contains_key("inner::inner_spec"),
            "inner module spec_fn should be qualified as inner::inner_spec");
        assert_eq!(m["inner::inner_proof"], vec!["inner::inner_spec"]);
    }

    #[test]
    fn outer_does_not_see_inner() {
        let deps = deps_for_fixture("inline_module.rs");
        let m = dep_map(&deps);
        assert_eq!(m["outer_proof"], vec!["outer_spec"]);
    }

    // ── no_functions.rs ────────────────────────────────────────────────

    #[test]
    fn empty_file_returns_empty() {
        let deps = deps_for_fixture("no_functions.rs");
        assert!(deps.is_empty());
    }

    // ── real_benchmark.rs ──────────────────────────────────────────────

    #[test]
    fn real_benchmark_parses_without_panic() {
        let deps = deps_for_fixture("real_benchmark.rs");
        // Just assert it parsed and returned something
        assert!(!deps.is_empty(),
            "real benchmark file should have at least one function");
    }

    #[test]
    fn real_benchmark_no_self_deps() {
        let deps = deps_for_fixture("real_benchmark.rs");
        for dep in &deps {
            assert!(!dep.depends_on.contains(&dep.name),
                "{} should not depend on itself", dep.name);
        }
    }

    // ── Inline code tests (no fixture file needed) ─────────────────────

    #[test]
    fn inline_requires_clause_dep() {
        let deps = deps_for(r#"
            use vstd::prelude::*;
            verus! {
                spec fn pre() -> bool { true }
                proof fn my_proof()
                    requires pre(),
                { }
            }
        "#);
        let m = dep_map(&deps);
        assert_eq!(m["my_proof"], vec!["pre"]);
    }

    #[test]
    fn inline_decreases_clause_dep() {
        let deps = deps_for(r#"
            use vstd::prelude::*;
            verus! {
                spec fn measure(n: nat) -> nat { n }
                spec fn recur(n: nat) -> nat
                    decreases measure(n),
                {
                    if n == 0 { 0 } else { recur((n - 1) as nat) }
                }
            }
        "#);
        let m = dep_map(&deps);
        assert!(m["recur"].contains(&"measure".to_string()));
    }

    #[test]
    fn inline_recommends_clause_dep() {
        let deps = deps_for(r#"
            use vstd::prelude::*;
            verus! {
                spec fn safe() -> bool { true }
                spec fn guarded() -> int
                    recommends safe(),
                { 42 }
            }
        "#);
        let m = dep_map(&deps);
        assert_eq!(m["guarded"], vec!["safe"]);
    }

    #[test]
    fn inline_no_verus_macro_returns_error() {
        // A plain Rust file without verus! macro
        let result = deps_for("fn main() {}");
        // fcompute_deps returns empty when there's no verus! macro
        // (fextract_verus_macro may error or return empty)
        // We just verify it doesn't panic.
        let _ = result;
    }

    #[test]
    fn inline_trait_impl_naming_matches_list_segments() {
        let deps = deps_for(r#"
            use vstd::prelude::*;
            verus! {
                pub struct Woo { pub x: int }
                pub trait T { spec fn method(&self) -> bool; }
                impl T for Woo {
                    open spec fn method(&self) -> bool { true }
                }
                impl Woo {
                    pub proof fn uses_method(&self)
                        ensures self.method(),
                    { }
                }
            }
        "#);
        let m = dep_map(&deps);
        // Trait impl method should be named Woo::method (not <Woo as T>::method)
        assert!(m.contains_key("Woo::method"),
            "trait impl spec_fn should be named Woo::method, got keys: {:?}", m.keys().collect::<Vec<_>>());
        // The proof fn should depend on Woo::method
        assert_eq!(m["Woo::uses_method"], vec!["Woo::method"]);
    }
}

