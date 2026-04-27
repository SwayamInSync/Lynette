# Lynette — Verus Source Code Parser & Analyzer

Lynette is a Rust-based tool for parsing, analyzing, and transforming [Verus](https://github.com/verus-lang/verus)-annotated Rust source files. It is built on top of `syn_verus` (the Verus fork of the `syn` crate) and provides a CLI for extracting, inspecting, and manipulating Verus constructs such as spec/proof/exec functions, requires/ensures clauses, loop invariants, assertions, and more.

> **Note:** This is an extended version of the Lynette parser originally developed as part of [microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis). The original tool lives under `utils/lynette/` in that repository. This fork adds the `list` command for comprehensive segment extraction with fully-qualified names and filtering support.

## Building

```bash
cd lynette
cargo build --release
# Binary at: ./target/release/lynette
```

## Command Index

| Command | Description |
|---|---|
| [`list`](#lynette-list--list-all-verus-segments) | List all Verus segments with types, names, and locations |
| [`deps`](#lynette-deps--compute-function-dependencies) | Compute function dependencies (which spec_fns each function references) |
| [`skeleton`](#lynette-skeleton--generate-a-leaf-blanked-skeleton) | Generate a structural skeleton with leaf bodies replaced by `// TODO fill here` |
| [`compare`](#lynette-compare--compare-two-verus-files) | Compare two Verus files (ignoring ghost code by default) |
| [`parse`](#lynette-parse--parse--validate-syntax) | Parse and validate Verus syntax |
| [`func extract`](#func-extract--extract-a-function) | Print the full source of a function by name |
| [`func add`](#func-add--add-functions-from-another-file) | Add functions from one file into another |
| [`func get-args`](#func-get-args--get-function-arguments) | Return function arguments as JSON |
| [`func remove`](#func-remove--remove-a-function) | Remove a function by name and print the resulting file |
| [`func detect-nl`](#func-detect-nl--detect-non-linear-operations-in-a-function) | Detect non-linear operations in a function (**unimplemented**) |
| [`func prune-quali`](#func-prune-quali--prune-prepost-conditions) | Remove requires and/or ensures from a function |
| [`code get-ghost`](#code-get-ghost--extract-ghost-code-locations) | Extract ghost code locations (requires, ensures, asserts, invariants) |
| [`code get-calls`](#code-get-calls--extract-function-calls) | Extract function/method calls as JSON |
| [`code get-func`](#code-get-func--get-function-at-location) | Return the function name at a specific line or byte offset |
| [`code detect-nl`](#code-detect-nl--detect-non-linear-operations) | Detect all non-linear arithmetic/bit operations in the file |
| [`code merge`](#code-merge--merge-proof-code) | Merge proof code from two files (**currently disabled**) |
| [`code unimpl`](#code-unimpl--mark-exec-functions-as-unimplemented) | Replace exec function bodies with `unimplemented!()`, one at a time |
| [`code get-target`](#code-get-target--get-target-functions) | List functions tagged as target (**WIP**) |
| [`code remove-ghost`](#code-remove-ghost--remove-ghost-code-at-spans) | Remove ghost code at given spans (**unimplemented**) |
| [`additions`](#lynette-additions--check-allowed-additions) | Check that only allowed code additions were made between two file versions |
| [`benchmark`](#lynette-benchmark--benchmark-preparation) | Prepare a Verus file for benchmarking (strip helper lemmas, reorder, etc.) |

---

## `lynette list` — List All Verus Segments

**Added command.** Parses a Verus source file and lists every identified segment with its kind, fully-qualified name, and source location.

```bash
lynette list [OPTIONS] <FILE>
```

### Options

| Flag | Description |
|---|---|
| `-j, --json` | Output in JSON format instead of text |
| `-f, --filter <KINDS>` | Comma-separated list of segment kinds to include (see below) |

### Segment Kinds

| Kind | Description |
|---|---|
| `spec_fn` | `spec` functions |
| `spec_checked_fn` | `spec(checked)` functions |
| `proof_fn` | `proof` functions |
| `proof_axiom_fn` | `proof` axiom functions |
| `exec_fn` | `exec` functions |
| `fn` | Default-mode functions |
| `requires` | `requires` clause expressions |
| `ensures` | `ensures` clause expressions |
| `recommends` | `recommends` clause expressions |
| `decreases` | `decreases` clause expressions |
| `invariant` | Loop `invariant` expressions |
| `invariant_ensures` | Loop `invariant_ensures` expressions |
| `invariant_except_break` | Loop `invariant_except_break` expressions |
| `assert` | `assert` statements |
| `assert_forall` | `assert forall` statements |
| `assume` | `assume` statements |
| `proof_block` | Inline `proof { ... }` blocks |
| `struct` | Struct definitions |
| `enum` | Enum definitions |
| `type_alias` | Type alias definitions |
| `trait` | Trait definitions |
| `impl` | Impl blocks |
| `macro` | Macro definitions |

### Output Format

**Text (default):**
```
kind:qualified_name:((start_line, start_col), (end_line, end_col))
```

Example:
```
spec_fn:ReconcileIdAllocator::allocate:((225, 4), (229, 5))
proof_fn:always_and_equality:((35, 1), (40, 2))
requires:entails_trans:((67, 8), (67, 20))
struct:APIServerState:((148, 0), (152, 1))
```

**JSON (`-j`):**
```json
[
  {
    "kind": "spec_fn",
    "name": "ReconcileIdAllocator::allocate",
    "start_line": 225,
    "start_col": 4,
    "end_line": 229,
    "end_col": 5
  }
]
```

### Examples

```bash
# List everything
lynette list file.rs

# Only spec and proof functions
lynette list -f spec_fn,proof_fn file.rs

# Only requires and ensures clauses, as JSON
lynette list -j -f requires,ensures file.rs

# Only structs and enums
lynette list -f struct,enum file.rs
```

### Namespacing

Functions inside `impl` or `trait` blocks are qualified with their parent type:

```
spec_fn:ReconcileIdAllocator::allocate      (method in impl ReconcileIdAllocator)
spec_fn:ConfigMapView::_default             (method in impl ConfigMapView)
proof_fn:Cluster::lemma_always_...          (method in impl Cluster)
spec_fn:owner_reference_to_object_reference (free function)
```

---

## `lynette deps` — Compute Function Dependencies

**Added command.** Performs AST-level dependency analysis on a Verus source file. For each function, reports which `spec_fn`s (defined in the same file) it references — by walking the function's body and signature spec clauses and collecting all referenced identifiers, including through local macro expansion.

```bash
lynette deps [OPTIONS] <FILE>
```

### Options

| Flag | Description |
|---|---|
| `-j, --json` | Output in JSON format instead of text |
| `-f, --filter <KINDS>` | Only show dependencies for functions of these kinds (comma-separated, e.g. `proof_fn`) |
| `--non-empty` | Only show functions that have at least one dependency |

### Output Format

**Text (default):**
```
function_name (kind):
  -> dependency1
  -> dependency2

function_with_no_deps (kind):
  (none)
```

All functions are shown by default; use `--non-empty` to hide functions with zero dependencies.

**JSON (`-j`):**
```json
[
  {
    "name": "my_proof",
    "kind": "proof_fn",
    "depends_on": ["my_spec", "Foo::helper_spec"]
  }
]
```

### Examples

```bash
# Show all dependencies
lynette deps file.rs

# Only proof_fn dependencies, as JSON
lynette deps -j -f proof_fn file.rs

# Only functions with at least one dependency
lynette deps --non-empty file.rs

# Proof functions that reference spec functions, as JSON
lynette deps -j -f proof_fn --non-empty file.rs
```

### How It Works

#### 1. Parsing & Collection

The file is parsed with `syn_verus`. All function definitions are collected — free functions, impl methods, trait methods, and functions inside inline modules. Each function is represented as a `FnInfo` record containing:

- **`name`** — fully-qualified name (e.g. `Foo::bar`, `inner::my_fn`)
- **`kind`** — the function mode (`spec_fn`, `proof_fn`, `exec_fn`, etc.)
- **`referenced_idents`** — all identifiers and paths referenced anywhere in the function
- **`call_target_idents`** — only identifiers appearing in call position (`func(...)`, `obj.method(...)`)
- **`impl_type`** — the parent type for methods inside `impl` blocks

#### 2. AST Walking

Two parallel AST walkers traverse each function's body and signature:

- **`collect_idents_expr`** collects *all* referenced identifiers (used for cross-function dependency matching)
- **`collect_call_targets_expr`** collects *only call-position* identifiers (used for self-reference detection)

**Handled expression types:**

| Category | Expressions |
|---|---|
| **Calls** | `Call` (`foo(x)`), `MethodCall` (`x.foo()`) |
| **Paths** | `Path` (`foo`, `Foo::bar`) |
| **Operators** | `Binary` (`a + b`), `Unary` (`!x`) |
| **Control flow** | `If`, `Match`, `While`, `ForLoop`, `Loop`, `Break`, `Return` |
| **Blocks** | `Block`, `TryBlock`, `Closure` |
| **Data** | `Tuple`, `Array`, `Repeat`, `Struct` (field values only — see below), `Field`, `Index`, `GetField` (`->` accessor) |
| **Misc** | `Paren`, `Group`, `Reference`, `Cast`, `Assign`, `Range`, `Try` (`?`), `Yield`, `Let` |
| **Verus-specific** | `Assert` (including `.requires` and `by` block), `AssertForall` (including `.implies`), `Assume`, `View` (`.view()`), `BigAnd` (`&&&`), `BigOr` (`\|\|\|`), `RevealHide` (`reveal`/`hide`), `Has`, `HasNot`, `Matches`, `Is`, `IsNot` |

**Struct constructors** (e.g. `Foo { x: 1 }`) are a special case: the type path is *not* collected as an identifier (to avoid false positives from type names matching `spec_fn` names), but field value expressions *are* walked.

**Nested `fn` items** inside a function body are *not* descended into — their references belong to the nested function, not the enclosing one.

#### 3. Signature Spec Clause Walking

Both walkers also traverse the function signature's spec clauses:

| Clause | Fields traversed |
|---|---|
| `requires` | All expressions |
| `ensures` | All expressions |
| `recommends` | All expressions + `via` |
| `decreases` | All expressions + `when` + `via` |
| `default_ensures` | All expressions |
| `returns` | All expressions |
| `unwind` | `when` expression |

Loop spec clauses (`invariant`, `invariant_ensures`, `invariant_except_break`, `ensures`, `decreases`) inside `while`, `for`, and `loop` expressions are also traversed.

Closure spec clauses (`requires`, `ensures`, `decreases`) are traversed as well.

#### 4. Local Macro Expansion

`macro_rules!` definitions are collected from the **entire file** — both inside and outside `verus!{}` blocks — and used for token-level dependency scanning.

**How it works:**

1. **Collection**: All `macro_rules!` definitions are gathered into a map of `macro_name → Vec<arm_bodies>`. Multi-arm macros have all arms collected.

2. **Detection**: For each function, the body and signature are converted to a token stream. Any `name!` invocations matching a local macro are detected.

3. **Transitive expansion**: Macro bodies may themselves invoke other local macros. A worklist algorithm with cycle detection computes the transitive closure of all macros reachable from the function's direct invocations.

4. **Scanning**: All reachable macro arm bodies are token-scanned for identifiers and call targets. This includes qualified paths like `Foo::bar()`. Discovered identifiers are added to the function's `referenced_idents` and `call_target_idents`.

**Example:**
```rust
macro_rules! my_macro {
    () => { helper_spec() };
}

verus! {
    spec fn helper_spec() -> bool { true }
    proof fn my_proof() {
        my_macro!();  // → dependency on helper_spec detected
    }
}
```

Nested macros also work:
```rust
macro_rules! inner { () => { helper_spec() }; }
macro_rules! outer { () => { inner!() }; }

verus! {
    proof fn my_proof() {
        outer!();  // → dependency on helper_spec detected (via inner)
    }
}
```

#### 5. Dependency Resolution

Collected identifiers are cross-referenced against the set of `spec_fn` / `spec_checked_fn` definitions in the file.

**Qualified references** (e.g. `Foo::bar`) are matched directly against known spec_fns.

**Bare names** (e.g. `bar`) use a **same-impl preference heuristic**:
- If the calling function is inside `impl Foo`, only `Foo::bar` is matched
- If no same-impl candidate exists, or the caller is a free function, **all** spec_fns with that bare name are included (conservative fallback)

**Path prefix normalization**: `crate::`, `self::`, `super::`, and `Self::` prefixes are stripped to the bare last segment before matching — so `Self::bar()` inside `impl Foo` correctly resolves to `Foo::bar`.

#### 6. Self-Reference (Recursion) Detection

A function is listed as depending on itself **only** when it genuinely calls itself — i.e. its name appears in call-target position (`func(...)` or `self.func(...)`). The dual-set approach (all idents vs. call-target idents) prevents false self-deps from non-call path references.

**Recognized self-call patterns:**
- `recur(n - 1)` — direct name
- `Self::recur(n - 1)` — Self-qualified
- `self::recur(n - 1)` — module-qualified
- `crate::recur(n - 1)` — crate-qualified
- `super::recur(n - 1)` — parent-module-qualified
- `self.recur(n - 1)` — method call

> **Note:** This is purely syntactic — a local binding (e.g. a closure) called as `name(...)` that shadows a function name will still be treated as a self-call.

#### 7. Output

Dependencies are reported using qualified names (e.g. `Foo::bar`) when available, or bare names (e.g. `bar`) otherwise. Results are sorted by function name.

### Scope

The **source** side includes functions of **all** kinds (`exec_fn`, `proof_fn`, `spec_fn`, `fn`, etc.). The dependency targets (`depends_on`) are limited to **`spec_fn` and `spec_checked_fn`** defined in the same file — other function-to-function references (e.g. `proof_fn` → `proof_fn`) are not tracked. The `--filter` flag controls which source functions to *display*, not what is detected as a dependency target.

### Naming

- **Impl methods** always use `Type::method`, regardless of whether the impl is inherent or a trait impl (`impl Trait for Foo` → `Foo::method`). This matches the naming used by `lynette list`.
- **Inline module functions** are qualified with the module path: `inner::my_fn`.
- **Free functions** use their bare name.

### Limitations

| Limitation | Impact | Workaround |
|---|---|---|
| **Same-file only** | Cross-file dependencies (imports, external crates) are not tracked | N/A — would require multi-file analysis |
| **No type resolution** | Bare method calls like `self.val()` are resolved heuristically (same-impl preference, then conservative fallback) | Use explicit qualified paths (`Foo::val()`) when precision matters |
| **Variable name collisions** | A variable used as an expression that shares a `spec_fn` name creates a false positive (`let x = len;` where `spec fn len()` exists). Pattern bindings (`let len = 5;`) are *not* affected | Avoid naming variables after spec_fns |
| **Parameter name collisions** | A function parameter sharing a spec_fn name creates a false positive (e.g. `fn caller(helper_spec: int)`) | Rename the parameter |
| **Macro expansion is token-level** | No actual substitution — macro patterns/metavariables are not expanded. Token scanning may miss deps hidden behind complex token manipulation | Keep macro bodies straightforward |
| **Multi-arm macros over-approximate** | All arms of a `macro_rules!` are scanned regardless of which arm is actually matched | Acceptable — only causes false positives, not missed deps |
| **External macros opaque** | Only locally-defined `macro_rules!` are expanded; `use`-imported or proc-macros are not | Define wrapper macros locally if needed |
| **`use` aliases not tracked** | `use Foo as Bar; Bar::method()` won't resolve to `Foo::method` | Use original names |
| **`unsafe` blocks not traversed** | References inside `unsafe { ... }` blocks are missed | N/A |

---

## `lynette skeleton` — Generate a Leaf-Blanked Skeleton

**Added command.** Produces a *structural skeleton* of a Verus source file by replacing the contents of every **leaf-level** item with a `// TODO fill here` placeholder, while keeping the surrounding container items (`mod`, `impl`, `trait`, the top-level `verus!{ ... }` macro) intact.

This is intended for prompting a code-generation model with the file's structure — telling it *where* to write spec/proof/exec code without revealing the answer. The original whitespace, comments, and item ordering are preserved (the transformation is a span-based textual rewrite of the original source, not a re-rendering of the AST).

```bash
lynette skeleton <FILE>
```

The skeleton is printed to stdout. The exit code is **0** on success and **1** on parse failure (with the error printed to stderr).

### What gets blanked

Each *leaf* contribution is replaced independently; containers are recursed into without modification.

| Item kind | Replacement |
|---|---|
| `fn` body (free, `impl` method, `trait` method default) | The whole `{ ... }` block becomes `{ <newline>    // TODO fill here <newline>}`. **Empty bodies (`{}`) are preserved as-is.** |
| `requires` clause | The expression list is replaced by `// TODO fill here` (the trailing `,` is also consumed) |
| `ensures` clause | Same as `requires` |
| `recommends` clause | Same as `requires` |
| `decreases` clause (signature-level) | Same as `requires` |
| `struct` with named fields | The `{ ... }` field list becomes `{ // TODO fill here }`. **Unit and tuple structs (`struct Foo;`, `struct Foo(i32, i32);`) are left untouched.** |
| `enum` with variants | The `{ ... }` variant list becomes `{ // TODO fill here }` |
| `const` initializer (free or in `impl`) | The right-hand side becomes `/* TODO fill here */` (block comment so the trailing `;` is preserved) |
| `static` initializer | Same as `const` |
| `trait` method **without** a default body | Left untouched (no body is invented) |
| `trait` const **without** a default value | Left untouched |
| `mod`, `impl`, `trait`, top-level `verus!{ ... }` | **Containers** — header is kept, contents are recursed into |
| Type aliases, `use` items, macros (other than `verus!`) | Left untouched |

Indentation of every inserted block is computed from the column of the enclosing item, so the output is structurally faithful at every nesting level.

### Example

Input (`/tmp/example.rs`):

```rust
use vstd::prelude::*;

verus! {

struct Point { x: int, y: int }

impl Point {
    spec fn norm_sq(self) -> int {
        self.x * self.x + self.y * self.y
    }

    proof fn lemma_nonneg(self)
        requires
            true,
        ensures
            self.norm_sq() >= 0,
    {
        assert(self.x * self.x >= 0) by (nonlinear_arith);
    }
}

const MAX_VAL: u64 = 100 + 200;

mod inner {
    fn helper(x: u64) -> u64 { x + 1 }
}

fn main() {}

}
```

Running `lynette skeleton /tmp/example.rs`:

```rust
use vstd::prelude::*;

verus! {

struct Point {
    // TODO fill here
}

impl Point {
    spec fn norm_sq(self) -> int {
        // TODO fill here
    }

    proof fn lemma_nonneg(self)
        requires
            // TODO fill here
        ensures
            // TODO fill here
    {
        // TODO fill here
    }
}

const MAX_VAL: u64 = /* TODO fill here */;

mod inner {
    fn helper(x: u64) -> u64 {
        // TODO fill here
    }
}

fn main() {}

}
```

### How it works

1. The file is parsed with `syn_verus`. Top-level `verus!{ ... }` macro contents are re-parsed as a Verus `File` so that items inside it are visited too.
2. The AST is walked. For each leaf item, a `Replacement { start, end, text }` record is collected using the AST span (line/column) of the region to be blanked. Containers (`mod`, `impl`, `trait`, `verus!`) recurse without contributing their own replacement.
3. Replacements are sorted in reverse source order and applied directly to the original file's bytes. This preserves all comments, blank lines, and formatting that lie outside the blanked regions — something a `ToTokens` round-trip cannot do.
4. For `requires`/`ensures`/`recommends`/`decreases` clause lists, the trailing `,` after the last expression (which is part of the clause syntax but not part of the last expression's span) is also consumed so the result is well-formed.

### Notes & limitations

- `// TODO fill here` is a line comment; for inline contexts (after a `=` in a `const`/`static`) the block-comment form `/* TODO fill here */` is used so the trailing `;` survives.
- Functions with empty bodies (`fn main() {}`, `fn empty_test() {}`) are intentionally **not** blanked — they carry no leaf content to hide.
- Loop-internal spec clauses (`invariant`, `invariant_ensures`, `decreases` inside `while`/`for`/`loop`) are *not* blanked separately — they live inside a function body, which is blanked as a whole.
- Asserts, assumes, and inline `proof { ... }` blocks are likewise covered by the enclosing function body's blanking.
- If parsing fails, the file is left untouched and the command exits with a non-zero status.

### Programmatic use

The Rust API is exposed in `lynette::skeleton`:

```rust
use lynette::skeleton::{fskeleton_file, skeleton_from_source};

let s = fskeleton_file(&"path/to/file.rs".into())?;
let s = skeleton_from_source(verus_source_string)?;
```

### Python wrapper

```python
import os, subprocess, tempfile

LYNETTE_BIN = "/path/to/lynette"

def make_skeleton(code: str) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".rs", delete=False) as f:
        f.write(code); path = f.name
    try:
        r = subprocess.run([LYNETTE_BIN, "skeleton", path],
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError(r.stderr)
        return r.stdout
    finally:
        os.unlink(path)
```

---

## `lynette compare` — Compare Two Verus Files

Compares whether two Verus source files produce the same Rust code after stripping ghost code ("deghosting"). By default, **all** ghost code (requires, ensures, asserts, invariants, spec functions, decreases, assumes) is stripped before comparison — so only the exec-level Rust code is compared. Each `--<kind>` flag **preserves** that kind of ghost code during comparison.

Exits with code **0** if files are equivalent, or code **1** (printing `Files are different`) if they differ.

```bash
lynette compare [OPTIONS] <FILE1> <FILE2>
```

### Options

| Flag | Description |
|---|---|
| `-t, --target` | *(Deprecated)* Enables `--requires --ensures --assumes --decreases` together |
| `--spec-mode` | Enable all spec-related flags (`--spec --requires --ensures --recommends`). **Note**: signature-level `decreases` is NOT enabled here — it is treated as termination scaffolding and ignored on every fn kind. Pass `--decreases` explicitly to enforce it. |
| `--proof-mode` | Enable all proof-related flags (`--proof --invariants --asserts --assert-forall --assumes --proof-block`) |
| `--allow-helpers` | When used with `--spec-mode`, ignore *new* proof-fn helpers that `<FILE2>` introduces but that are not present in `<FILE1>`. Directional: `<FILE1>` is the original/spec-defining file and `<FILE2>` the candidate (e.g. a model-generated proof completion). Renaming or deleting an existing proof fn is therefore detected. No-op outside `--spec-mode`. |
| `--requires` | Also compare `requires` clauses |
| `--ensures` | Also compare `ensures` clauses |
| `--recommends` | Also compare `recommends` clauses |
| `--invariants` | Also compare loop invariants (`invariant`, `invariant_ensures`, `invariant_except_break`) |
| `--spec` | Also compare spec functions (`spec fn`, `spec(checked) fn`) |
| `--proof` | Also compare proof functions (`proof fn`, `proof(axiom) fn`) |
| `--asserts` | Also compare assert statements |
| `--assert-forall` | Also compare `assert forall` expressions |
| `--asserts-anno` | Also compare asserts with annotations (e.g. `#[warn(llm_do_not_change)]`) |
| `--decreases` | Also compare decreases clauses |
| `--assumes` | Also compare assume statements |
| `--proof-block` | Also compare inline `proof { ... }` blocks |
| `-v, --verbose` | Print both files after deghosting to stdout |

### Ghost Code Categories

The flags map to these Verus constructs:

| Category | Kinds | Flags |
|---|---|---|
| **Spec function kinds** | `spec fn`, `spec(checked) fn` | `--spec` (or `--spec-mode`) |
| **Spec clause kinds** | `requires`, `ensures`, `recommends` | `--requires`, `--ensures`, `--recommends` (or `--spec-mode`) |
| **Decreases (termination scaffolding)** | `decreases` (signature-level on any fn kind) | `--decreases` only \u2014 *not* enabled by `--spec-mode` or `--proof-mode`. Loop-level `decreases` is gated by `--invariants` (or `--proof-mode`). |
| **Proof function kinds** | `proof fn`, `proof(axiom) fn` | `--proof` (or `--proof-mode`) |
| **Proof clause kinds** | `invariant`, `invariant_ensures`, `invariant_except_break`, `assert`, `assert forall`, `assume`, `proof { ... }` | `--invariants`, `--asserts`, `--assert-forall`, `--assumes`, `--proof-block` (or `--proof-mode`) |
| **Exec function kinds** | `exec fn`, `fn` | Always retained (never stripped) |

> **Note on proof functions and spec clauses.** When any spec-clause flag
> (`--requires`, `--ensures`, `--recommends`, or `--spec-mode`)
> is enabled but `--proof` is not, the *signatures* of `proof fn` /
> `proof(axiom) fn` items are preserved (with the enabled clauses) and only
> the proof body is dropped. Lemma contracts are part of the spec surface,
> so weakening a lemma's `ensures` will be detected by `--spec-mode`.
> Use `--proof` (or `--proof-mode`) if you also want to compare proof bodies.
>
> **Note on `decreases`.** `decreases` is *termination scaffolding*, not
> semantic content: two functions with identical bodies but different
> `decreases` clauses are extensionally equivalent. Accordingly:
>
> - **Signature-level `decreases`** (on a `spec fn`, `proof fn`, or `exec fn`)
>   is stripped under `--spec-mode` and `--proof-mode` and is therefore
>   never compared. The masking pipeline (`create_masked_segments.py`)
>   blanks `decreases` per-mode (spec-mode on `spec fn` sigs, proof-mode
>   on `proof fn` sigs, exec-mode on `exec fn` sigs); the verifier
>   mirrors that by ignoring all signature `decreases` so blanked +
>   filled-in completions round-trip cleanly.
> - **Loop-level `decreases`** (inside `while` / `for` / `loop` headers)
>   is gated by `--invariants` (set by `--proof-mode`, *not* by
>   `--spec-mode`). It is therefore stripped under `--spec-mode` and
>   compared under `--proof-mode`.
> - To enforce signature `decreases` on every fn kind, pass `--decreases`
>   explicitly. To enforce loop-level `decreases`, pass `--invariants`
>   (or `--proof-mode`).

### Example

```bash
# Compare ignoring all ghost code (only exec-level Rust code)
lynette compare file1.rs file2.rs

# Compare including requires and ensures (but still ignoring asserts, invariants, etc.)
lynette compare --requires --ensures file1.rs file2.rs

# Compare with all spec-related ghost code preserved
lynette compare --spec-mode file1.rs file2.rs

# Compare with all proof-related ghost code preserved
lynette compare --proof-mode file1.rs file2.rs

# Compare specs/exec strictly, but allow new proof-fn helpers in file2
# (typical "model proof completion" check):
lynette compare --spec-mode --allow-helpers original.rs model_patched.rs

# Compare everything including all ghost code
lynette compare --spec-mode --proof-mode file1.rs file2.rs

# Or equivalently, enable each flag individually
lynette compare --spec --proof --requires --ensures --recommends --invariants \
  --asserts --assert-forall --decreases --assumes --proof-block file1.rs file2.rs
```

### Proof-writing contract enforced by `--spec-mode --allow-helpers`

This combination is designed for verifying that a model-generated proof
completion did not tamper with the spec/exec surface of the input file.
Argument order is significant: pass the original input as `<FILE1>` and the
model output as `<FILE2>`.

It catches (exits 1):

- spec function body / signature / parameter / return / `recommends` change
- spec function added or removed
- `requires` / `ensures` change on any spec, proof, or exec function
- exec / proof function signature change (rename, params, return, generics,
  where, visibility, unsafety)
- exec function body change
- exec function added or removed
- proof function present in `<FILE1>` but missing in `<FILE2>`, or renamed
- conversion between spec / proof / exec function kinds
- struct / enum / trait declaration changes
- top-level `use` / `const` / `static` / `mod` changes

It allows (exits 0):

- proof function body change (including filling in an empty stub)
- new proof function helpers added at the top level or inside `impl` blocks
  (asymmetric: only NEW names in `<FILE2>` are tolerated; removing or
  renaming an existing proof fn is still flagged)
- `assert`, `assert forall`, `assume`, `proof { ... }` blocks added inside
  any retained function body
- loop `invariant` / `invariant_ensures` / `invariant_except_break` changes
  (additions, strengthening, removals)
- loop-level `decreases` and loop-level `ensures` changes
- **signature-level `decreases` changes on every fn kind** (spec_fn,
  proof_fn, exec_fn) — added, removed, or rewritten. Pass `--decreases`
  explicitly to make these a hard cheat.

**Known limitation.** Verifier attributes (`#[verifier::external_body]`,
`#[verifier::opaque]`, `#[verifier::external]`, etc.) are stripped before
comparison and so additions/removals are *not* detected by `compare`.
Use `lynette additions` to catch attribute-level cheating.

---

## `lynette parse` — Parse & Validate Syntax

Parses a Verus source file using `syn_verus` and optionally prints the debug representation of the token stream. Useful for syntax validation and inspecting how Verus code is tokenized.

Exits with code **0** on successful parse, or code **1** with an error message if the file has syntax errors.

Without `-c`, prints the debug-formatted token stream for both the outer file and each `verus!{...}` macro body (showing `Ident`, `Punct`, `Literal` tokens with byte spans).

```bash
lynette parse [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-c, --check` | Only check syntax, do not print anything |

### Example

```bash
# Validate syntax (silent on success)
lynette parse -c file.rs

# Print debug token stream
lynette parse file.rs
```

---

## `lynette func` — Function Operations

Operations on individual functions within a Verus file.

### `func extract` — Extract a Function

Prints the full source of a function (signature + body) by name.

```bash
lynette func extract [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-f, --function <NAMES>` | Comma-separated function names (use `Type::method` for impl methods) |
| `-b` | Only return the function body |

```bash
# Extract a free function
lynette func extract -f guarantee_condition_holds file.rs

# Extract a method from an impl block
lynette func extract -f ReconcileIdAllocator::allocate file.rs

# Extract just the body
lynette func extract -f allocate -b file.rs
```

### `func add` — Add Functions From Another File

Adds functions from `<FILE2>` into `<FILE1>`. Both files must contain exactly one `verus!{...}` macro.

```bash
lynette func add [OPTIONS] <FILE> <FILE2>
```

| Flag | Description |
|---|---|
| `-r, --replace` | Replace existing functions on name conflict |
| `-f, --funcs <NAMES>` | Comma-separated list of function names to add |

### `func get-args` — Get Function Arguments

Returns the arguments of a function as a JSON array. Each entry has `"arg"` (parameter name/pattern) and `"ty"` (type).

```bash
lynette func get-args <FILE> <FUNCTION>
```

#### Output Format

```json
[{"arg": "base", "ty": "nat"}, {"arg": "exp", "ty": "nat"}]
```

### `func remove` — Remove a Function

Removes a function by name and prints the resulting file.

```bash
lynette func remove <FILE> <FUNCTION>
```

### `func detect-nl` — Detect Non-Linear Operations in a Function

> **Status:** Unimplemented — this command will panic at runtime. Use `code detect-nl` instead for file-level detection.

Intended to detect non-linear arithmetic/bit operations within a specific function's assert expressions.

```bash
lynette func detect-nl <FILE> <FUNCTION>
```

### `func prune-quali` — Prune Pre/Post-Conditions

Removes requires and/or ensures from a function.

```bash
lynette func prune-quali [OPTIONS] <FILE> <FNAME>
```

| Flag | Description |
|---|---|
| `--pre` | Remove pre-conditions (requires) |
| `--post` | Remove post-conditions (ensures) |
| `-a, --all` | Remove both (default) |

---

## `lynette code` — Code-Level Operations

Operations on code constructs across the entire file.

### `code get-ghost` — Extract Ghost Code Locations

Returns all ghost code (requires, ensures, assert, invariant, etc.) with source locations.

```bash
lynette code get-ghost [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-b, --byte` | Print byte offsets instead of line/column numbers (**unimplemented**) |
| `-l, --loc` | Print line/column numbers instead of byte offsets (default) |

Output format (default `--loc`):
```
type:((start_line, start_col), (end_line, end_col))
```

Example:
```
requires:((45, 8), (45, 23))
ensures:((47, 12), (47, 34))
assert_forall:((4376, 16), (4389, 17))
```

### `code get-calls` — Extract Function Calls

Returns all function/method calls in the file as a JSON array. Each entry contains the function name, its arguments (as strings), and the source line number.

```bash
lynette code get-calls [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-l, --line <RANGES>` | Only return calls at specific lines (e.g. `1-3,5,7-9`) |

#### Output Format

```json
[{"func": "pow", "args": ["base", "(exp - 1) as nat"], "line": 24}]
```

### `code get-func` — Get Function at Location

Returns the name of the function whose span contains the given line or byte offset. Outputs a JSON-like bracketed list (e.g. `[func_name]`), or `[]` if no function is found at that location.

Exactly one of `-l` or `-o` must be provided.

```bash
lynette code get-func <FILE> -l <LINE>
lynette code get-func <FILE> -o <OFFSET>
```

| Flag | Description |
|---|---|
| `-l` | The 1-based line number to look up |
| `-o` | The byte offset from the beginning of the file |

### `code detect-nl` — Detect Non-Linear Operations

Detects all non-linear arithmetic/bit operations in the file. Returns a list of `(start, end)` positions.

```bash
lynette code detect-nl [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-c, --check` | Only check syntax, do not print anything |

### `code merge` — Merge Proof Code

> **Status:** Currently disabled — this command exits with code 1 without producing output. The merge module is commented out in the source.

Merges proof code from two files that share the same exec code.

```bash
lynette code merge [OPTIONS] <FILE1> <FILE2>
```

| Flag | Description |
|---|---|
| `--invariants` | Merge invariants (currently the only supported mode) |
| `--all` | Merge everything |

### `code unimpl` — Mark Exec Functions as Unimplemented

For each **exec** function in a Verus file, produces a version of the entire file where **that function's body** is kept intact and **all other exec functions** have their bodies replaced with `unimplemented!()` and annotated with `#[verifier::external_body]`.

The following functions are **skipped** (never unimplemented):
- `spec`, `proof`, and other ghost functions
- Functions already having `#[verifier::external_body]` or `#[verifier::external_fn_specification]`
- Functions whose body is already `unimplemented!()`
- Functions tagged as "target" (unless `-t` is passed)

Functions inside `trait` definitions and `impl` blocks are also processed.

```bash
lynette code unimpl [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-t, --target` | Also unimplement target-tagged functions |

#### Output Format

Outputs a **JSON array** to stdout. Each entry represents one exec function that was eligible:

```json
[
  {
    "name": "function_name",
    "code": "...full file with this function's body kept, all others replaced..."
  }
]
```

The `"name"` field uses qualified names for methods (e.g. `Type::method`). Each `"code"` entry is the full file source with exactly **one** exec function's body preserved and all others replaced with `unimplemented!()`.

If no exec functions are found (e.g. the file only contains spec/proof functions), the output is `[]`.

#### Example

```bash
# On a file with two exec functions (binary_search, sum_vec) and a proof function:
lynette code unimpl file.rs
# Returns JSON array with 2 entries:
#   [0]: binary_search body kept, sum_vec body → unimplemented!()
#   [1]: sum_vec body kept, binary_search body → unimplemented!()
# The proof function is untouched in both entries.

# Also unimplement target-tagged functions:
lynette code unimpl -t file.rs
```

### `code get-target` — Get Target Functions

> **Status:** WIP.

Lists all functions tagged as "target" in a Verus source file.

```bash
lynette code get-target <FILE>
```

Outputs a bracketed, comma-separated list of function names:
```
[func1,func2]
```

Returns `[]` if no target-tagged functions are found.

### `code remove-ghost` — Remove Ghost Code at Spans

> **Status:** Unimplemented — this command will panic at runtime.

Removes ghost code at given starting spans in a Verus source file.

```bash
lynette code remove-ghost [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-l, --locs <LOCS>` | Comma-separated list of spans in `line:col` format to remove |

### `code get-ghost` vs `list`

- `code get-ghost` returns only ghost code (requires, ensures, asserts, invariants, proof blocks) **without function names**.
- `list` returns **all** segments (functions, structs, enums, traits, impls, macros, plus all ghost code) **with fully-qualified names and segment kinds**.

---

## `lynette additions` — Check Allowed Additions

A safety checker for Verus proof-synthesis workflows. Verifies that the changes between an original file and a changed file conform to a strict set of rules — ensuring that an LLM or tool has not altered executable code it shouldn't have touched.

Exits with code **0** if all changes are allowed, or code **1** (printing diagnostics) if disallowed changes are found.

```bash
lynette additions <FILE1> <FILE2>
```

- `<FILE1>` — the original file
- `<FILE2>` — the changed file

### What Counts as "Allowed"

The checker walks both files' items in order and applies these rules:

#### Target Functions

A "target" function is a `proof` or `exec` function whose body does **not** contain `unimplemented!()` (i.e. the function the LLM is supposed to complete). For target functions:

- **Proof target:** The body may be freely changed (new proof code), but the function's **visibility**, **non-proof attributes**, and **signature** (requires, ensures, recommends) must remain identical.
- **Exec target:** After stripping all ghost code from both versions, the exec body must be **identical** (no changes to executable logic). The signature (requires, ensures, recommends) must also match. Ghost additions (asserts, invariants, proof blocks, lemma calls) inside the body **are** allowed.
- Signature fields `decreases`, `opens_invariants`, and `prover` are excluded from the signature check — these may be freely added/changed.

#### Non-Target Functions

- **Existing `spec`, `proof`, or `exec` functions** that are not targets must be **exactly identical** in both files. Any modification is disallowed.
- **New `spec` or `proof` functions** (present in `<FILE2>` but not in `<FILE1>`) are **allowed** — helper lemmas and specs may be added.
- **New `exec` functions** are **disallowed**.

#### Other Items

| Item Type | Rule |
|---|---|
| `use` statements | May be added freely |
| `macro_rules!` | May be added freely |
| `broadcast use` | May be added freely |
| `impl` blocks | The impl header must match exactly; methods inside follow the target/non-target rules above |
| `trait` blocks | The trait header must match exactly; methods inside follow the target/non-target rules above |
| `struct`, `enum`, `const`, etc. | Must be exactly identical |
| Proof attributes (`verifier::rlimit`, `verifier::integer_ring`, `verifier::memoize`, `verifier::loop_isolation`, `verifier::spinoff_prover`) | Ignored during comparison — may be freely added or removed |
| Number of `verus!{...}` macros | Must be the same in both files |

---

## `lynette benchmark` — Benchmark Preparation

Prepares a Verus file for benchmarking by performing a sequence of transformations and writing the result to an output file. The output is formatted with `prettyplease` and then `verusfmt`.

```bash
lynette benchmark [OPTIONS] <FILE1> <FILE2>
```

- `<FILE1>` — input Verus source file
- `<FILE2>` — output file path

| Flag | Description |
|---|---|
| `-n, --no-lemma-mode` | Also erase all helper lemmas (non-target proof functions) |

### Transformations Applied

1. **Reorder**: Moves target functions (the functions to be completed) to the end of the file, so they appear after all their dependencies.
2. **Erase ghost from target**: Strips ghost code (asserts, invariants, proof blocks) from the bodies of target functions, producing a clean starting point for benchmarking.
3. **Clean uses**: Cleans up `use` statements.
4. **Remove helper lemmas** (only with `-n`): Removes all non-target `proof` functions (helper lemmas), leaving only spec functions and the target.

---

## Acknowledgements & Citations

This tool is an extended version of the Lynette parser originally developed as part of [microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis). If you use Lynette in your research, please cite the following:

```bibtex
@article{autoverus,
  title={AutoVerus: Automated Proof Generation for Rust Code},
  author={Chenyuan Yang and Xuheng Li and Md Rakib Hossain Misu and Jianan Yao and Weidong Cui and Yeyun Gong and Chris Hawblitzel and Shuvendu K. Lahiri and Jacob R. Lorch and Shuai Lu and Fan Yang and Ziqiao Zhou and Shan Lu},
  journal={Proceedings of the ACM on Programming Languages},
  volume={9},
  number={OOPSLA2},
  year={2025},
  publisher={ACM New York, NY, USA}
}

@misc{verusage,
  title={VeruSAGE: A Study of Agent-Based Verification for Rust Systems},
  author={Chenyuan Yang and Natalie Neamtu and Chris Hawblitzel and Jacob R. Lorch and Shan Lu},
  year={2025},
  eprint={2512.18436},
  archivePrefix={arXiv},
  primaryClass={cs.OS},
  url={https://arxiv.org/abs/2512.18436},
}
```
