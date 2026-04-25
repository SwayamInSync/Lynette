// Generate a "skeleton" of a Verus source file by replacing the bodies of
// leaf-level items (function blocks, struct/enum field lists, requires/ensures
// expressions, const/static initializers, ...) with `// TODO fill here`
// placeholders. Container items such as `mod`, `impl`, `trait` and the
// top-level `verus!{ ... }` macro are recursed into without touching their
// outer signatures, so the output mirrors the structural tree of the original
// code with all leaves blanked out.
//
// The transformation is performed as plain textual replacement using the AST
// spans, which lets us emit line comments that would otherwise be stripped by
// the tokenizer if we tried to round-trip through `ToTokens`.

use std::fs;
use std::path::PathBuf;
use syn::spanned::Spanned;

use crate::utils::{fload_file, Error};

const TODO: &str = "// TODO fill here";
/// Block-comment form of the placeholder, used in inline contexts (e.g. on the
/// same line as a `const NAME: T = <expr>;` semicolon) where a `//` line
/// comment would swallow the rest of the line.
const TODO_INLINE: &str = "/* TODO fill here */";

#[derive(Debug, Clone)]
struct Replacement {
    start: (usize, usize), // (line, column) of the first char to replace (1-indexed line, 0-indexed col)
    end: (usize, usize),   // (line, column) of the first char NOT to replace
    text: String,
    /// If true, after computing byte offsets the replacement is allowed to
    /// extend its end past a trailing `,` token (used for requires/ensures
    /// expression lists, where the trailing comma is part of the clause but
    /// not part of the last expression's span).
    eat_trailing_comma: bool,
}

fn span_loc(s: proc_macro2::Span) -> ((usize, usize), (usize, usize)) {
    let st = s.start();
    let en = s.end();
    ((st.line, st.column), (en.line, en.column))
}

fn brace_replacement(span: proc_macro2::Span, outer_col: usize) -> Replacement {
    // Replace `{ ... }` (including the braces) with a freshly indented block
    // containing the TODO comment. `outer_col` is the indent of the enclosing
    // item (e.g. the column of the `fn`/`struct`/`impl` keyword).
    let ((sl, sc), (el, ec)) = span_loc(span);
    let outer_indent = " ".repeat(outer_col);
    let inner_indent = " ".repeat(outer_col + 4);
    Replacement {
        start: (sl, sc),
        end: (el, ec),
        text: format!("{{\n{}{}\n{}}}", inner_indent, TODO, outer_indent),
        eat_trailing_comma: false,
    }
}

fn inline_replacement(span: proc_macro2::Span) -> Replacement {
    let ((sl, sc), (el, ec)) = span_loc(span);
    Replacement {
        start: (sl, sc),
        end: (el, ec),
        text: TODO_INLINE.to_string(),
        eat_trailing_comma: false,
    }
}

fn collect_sig_clauses(sig: &syn_verus::Signature, out: &mut Vec<Replacement>) {
    if let Some(r) = &sig.spec.requires {
        if !r.exprs.exprs.is_empty() {
            let first = r.exprs.exprs.first().unwrap().span();
            let last = r.exprs.exprs.last().unwrap().span();
            out.push(span_pair_replacement(first, last));
        }
    }
    if let Some(r) = &sig.spec.ensures {
        if !r.exprs.exprs.is_empty() {
            let first = r.exprs.exprs.first().unwrap().span();
            let last = r.exprs.exprs.last().unwrap().span();
            out.push(span_pair_replacement(first, last));
        }
    }
    if let Some(r) = &sig.spec.recommends {
        if !r.exprs.exprs.is_empty() {
            let first = r.exprs.exprs.first().unwrap().span();
            let last = r.exprs.exprs.last().unwrap().span();
            out.push(span_pair_replacement(first, last));
        }
    }
    if let Some(d) = &sig.spec.decreases {
        if !d.decreases.exprs.exprs.is_empty() {
            let first = d.decreases.exprs.exprs.first().unwrap().span();
            let last = d.decreases.exprs.exprs.last().unwrap().span();
            out.push(span_pair_replacement(first, last));
        }
    }
}

fn span_pair_replacement(
    first: proc_macro2::Span,
    last: proc_macro2::Span,
) -> Replacement {
    let st = first.start();
    let en = last.end();
    Replacement {
        start: (st.line, st.column),
        end: (en.line, en.column),
        text: TODO.to_string(),
        eat_trailing_comma: true,
    }
}

fn collect_item(item: &syn_verus::Item, out: &mut Vec<Replacement>) {
    use syn_verus::Item;
    let item_col = item.span().start().column;
    match item {
        Item::Fn(f) => {
            collect_sig_clauses(&f.sig, out);
            // Skip empty bodies (e.g. `fn main() {}`) to keep them as-is.
            if !f.block.stmts.is_empty() {
                out.push(brace_replacement(f.block.span(), item_col));
            }
        }
        Item::Mod(m) => {
            if let Some((_, items)) = &m.content {
                for it in items {
                    collect_item(it, out);
                }
            }
        }
        Item::Impl(i) => {
            for ii in &i.items {
                let inner_col = ii.span().start().column;
                match ii {
                    syn_verus::ImplItem::Fn(m) => {
                        collect_sig_clauses(&m.sig, out);
                        if !m.block.stmts.is_empty() {
                            out.push(brace_replacement(m.block.span(), inner_col));
                        }
                    }
                    syn_verus::ImplItem::Const(c) => {
                        out.push(inline_replacement(c.expr.span()));
                    }
                    _ => {}
                }
            }
        }
        Item::Trait(t) => {
            for ti in &t.items {
                let inner_col = ti.span().start().column;
                match ti {
                    syn_verus::TraitItem::Fn(m) => {
                        collect_sig_clauses(&m.sig, out);
                        if let Some(b) = &m.default {
                            if !b.stmts.is_empty() {
                                out.push(brace_replacement(b.span(), inner_col));
                            }
                        }
                    }
                    syn_verus::TraitItem::Const(c) => {
                        if let Some((_, expr)) = &c.default {
                            out.push(inline_replacement(expr.span()));
                        }
                    }
                    _ => {}
                }
            }
        }
        Item::Struct(s) => {
            if let syn_verus::Fields::Named(fields) = &s.fields {
                if !fields.named.is_empty() {
                    out.push(brace_replacement(fields.span(), item_col));
                }
            }
        }
        Item::Enum(e) => {
            if !e.variants.is_empty() {
                // Use the brace_token span which covers `{ ... }`.
                out.push(brace_replacement(e.brace_token.span.span(), item_col));
            }
        }
        Item::Const(c) => {
            if let Some(expr) = &c.expr {
                out.push(inline_replacement(expr.span()));
            } else if let Some(block) = &c.block {
                if !block.stmts.is_empty() {
                    out.push(brace_replacement(block.span(), item_col));
                }
            }
        }
        Item::Static(s) => {
            if let Some(expr) = &s.expr {
                out.push(inline_replacement(expr.span()));
            } else if let Some(block) = &s.block {
                if !block.stmts.is_empty() {
                    out.push(brace_replacement(block.span(), item_col));
                }
            }
        }
        Item::Macro(m) => {
            // Recurse into top-level `verus!{ ... }` macros so that we look at
            // the items they contain.
            if m.mac.path.is_ident("verus") {
                if let Ok(file) =
                    syn_verus::parse2::<syn_verus::File>(m.mac.tokens.clone())
                {
                    for it in &file.items {
                        collect_item(it, out);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Convert (1-indexed line, 0-indexed char column) to a byte offset in `source`.
fn loc_to_byte(source: &str, line_starts: &[usize], line: usize, col: usize) -> usize {
    if line == 0 || line > line_starts.len() {
        return source.len();
    }
    let line_start = line_starts[line - 1];
    let line_end = if line < line_starts.len() {
        // Subtract 1 to skip the trailing newline.
        line_starts[line] - 1
    } else {
        source.len()
    };
    let line_str = &source[line_start..line_end];
    let mut char_count = 0usize;
    for (b, ch) in line_str.char_indices() {
        if char_count == col {
            return line_start + b;
        }
        char_count += 1;
        let _ = ch;
    }
    // Column past end of line: clamp to end-of-line.
    line_start + line_str.len()
}

fn build_line_starts(source: &str) -> Vec<usize> {
    let mut v = vec![0usize];
    for (i, c) in source.char_indices() {
        if c == '\n' {
            v.push(i + 1);
        }
    }
    v
}

fn apply_replacements(source: &str, mut reps: Vec<Replacement>) -> String {
    if reps.is_empty() {
        return source.to_string();
    }
    let line_starts = build_line_starts(source);
    // Sort by start descending so earlier indices remain valid as we mutate.
    reps.sort_by(|a, b| b.start.cmp(&a.start));

    // Drop any replacement whose start is inside another (later-occurring,
    // earlier in our reversed list) replacement. Since we collect leaves only,
    // overlap should not happen in well-formed input, but we guard anyway.
    let mut filtered: Vec<Replacement> = Vec::new();
    for r in reps.into_iter() {
        let overlaps = filtered.iter().any(|prev| {
            // prev starts at or after r in source order; check overlap.
            !(r.end <= prev.start || prev.end <= r.start)
        });
        if !overlaps {
            filtered.push(r);
        }
    }

    let mut result = source.to_string();
    for r in &filtered {
        let s = loc_to_byte(source, &line_starts, r.start.0, r.start.1);
        let mut e = loc_to_byte(source, &line_starts, r.end.0, r.end.1);
        if r.eat_trailing_comma {
            // Skip whitespace then a single trailing comma, if present.
            let bytes = result.as_bytes();
            let mut k = e;
            while k < bytes.len() && (bytes[k] == b' ' || bytes[k] == b'\t') {
                k += 1;
            }
            if k < bytes.len() && bytes[k] == b',' {
                e = k + 1;
            }
        }
        if s <= e && e <= result.len() {
            result.replace_range(s..e, &r.text);
        }
    }
    result
}

/// Build a skeleton view of a Verus source file by reading it from disk.
pub fn fskeleton_file(filepath: &PathBuf) -> Result<String, Error> {
    let file = fload_file(filepath)?;
    let source = fs::read_to_string(filepath).map_err(Error::ReadFile)?;
    let mut reps: Vec<Replacement> = Vec::new();
    for item in &file.items {
        collect_item(item, &mut reps);
    }
    Ok(apply_replacements(&source, reps))
}

/// Build a skeleton view from an in-memory source string (used by callers that
/// already have the code, e.g. when iterating over a JSON dataset).
pub fn skeleton_from_source(source: &str) -> Result<String, Error> {
    use std::str::FromStr;
    let ts = proc_macro2::TokenStream::from_str(source).map_err(|e| Error::LexFile {
        error: e,
        filepath: PathBuf::from("<inline>"),
    })?;
    let file = syn_verus::parse2::<syn_verus::File>(ts).map_err(|e| Error::ParseFile {
        error: e,
        filepath: PathBuf::from("<inline>"),
        source_code: source.to_string(),
    })?;
    let mut reps: Vec<Replacement> = Vec::new();
    for item in &file.items {
        collect_item(item, &mut reps);
    }
    Ok(apply_replacements(source, reps))
}
