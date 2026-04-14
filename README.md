# Lynette — Verus Source Code Parser & Analyzer

Lynette is a Rust-based tool for parsing, analyzing, and transforming [Verus](https://github.com/verus-lang/verus)-annotated Rust source files. It is built on top of `syn_verus` (the Verus fork of the `syn` crate) and provides a CLI for extracting, inspecting, and manipulating Verus constructs such as spec/proof/exec functions, requires/ensures clauses, loop invariants, assertions, and more.

> **Note:** This is an extended version of the Lynette parser originally developed as part of [microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis). The original tool lives under `utils/lynette/` in that repository. This fork adds the `list` command for comprehensive segment extraction with fully-qualified names and filtering support.

## Building

```bash
cd lynette
cargo build --release
# Binary at: ./target/release/lynette
```

## Commands Overview

```
lynette <COMMAND>

Commands:
  list        List all Verus segments with types, names, and locations
  deps        Compute function dependencies (which spec_fns each function references)
  compare     Compare two Verus files (ignoring ghost code by default)
  parse       Parse and validate Verus syntax
  func        Operations on individual functions
  code        Operations on code-level constructs (ghost code, calls, etc.)
  additions   Check that only allowed additions were made between two files
  benchmark   Prepare a file for benchmarking (strip helper lemmas, etc.)
```

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

## `lynette compare` — Compare Two Verus Files

Compares whether two Verus source files produce the same Rust code after stripping ghost code. Various flags control which ghost code should also be compared.

```bash
lynette compare [OPTIONS] <FILE1> <FILE2>
```

### Options

| Flag | Description |
|---|---|
| `-t, --target` | (Deprecated) Stricter comparison on qualifiers and spec functions |
| `--requires` | Also compare `requires` clauses |
| `--ensures` | Also compare `ensures` clauses |
| `--invariants` | Also compare loop invariants |
| `--spec` | Also compare spec functions |
| `--asserts` | Also compare assert statements |
| `--asserts-anno` | Also compare asserts with annotations (e.g. `#[warn(llm_do_not_change)]`) |
| `--decreases` | Also compare decreases clauses |
| `--assumes` | Also compare assume statements |
| `-v, --verbose` | Print both files after deghosting |

### Example

```bash
# Compare ignoring all ghost code
lynette compare file1.rs file2.rs

# Compare including requires and ensures
lynette compare --requires --ensures file1.rs file2.rs
```

---

## `lynette parse` — Parse & Validate Syntax

Parses a Verus source file and optionally prints the token stream. Useful for syntax validation.

```bash
lynette parse [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-c, --check` | Only check syntax, do not print anything |

### Example

```bash
# Validate syntax
lynette parse -c file.rs

# Print token stream
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

Returns the arguments of a function as JSON.

```bash
lynette func get-args <FILE> <FUNCTION>
```

### `func remove` — Remove a Function

Removes a function by name and prints the resulting file.

```bash
lynette func remove <FILE> <FUNCTION>
```

### `func detect-nl` — Detect Non-Linear Operations in a Function

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
lynette code get-ghost <FILE>
```

Output format:
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

Returns all function/method calls in the file as JSON.

```bash
lynette code get-calls [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-l, --line <RANGES>` | Only return calls at specific lines (e.g. `1-3,5,7-9`) |

### `code get-func` — Get Function at Location

Returns the function at a specific line or byte offset.

```bash
lynette code get-func <FILE> -l <LINE>
lynette code get-func <FILE> -o <OFFSET>
```

### `code detect-nl` — Detect Non-Linear Operations

Detects all non-linear arithmetic/bit operations in the file.

```bash
lynette code detect-nl [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-s, --sig` | Also detect in function signatures |

### `code merge` — Merge Proof Code

Merges proof code from two files that share the same exec code.

```bash
lynette code merge [OPTIONS] <FILE1> <FILE2>
```

| Flag | Description |
|---|---|
| `--invariants` | Merge invariants (currently the only supported mode) |
| `--all` | Merge everything |

### `code unimpl` — Mark Functions as Unimplemented

Replaces function bodies with `unimplemented!()`.

```bash
lynette code unimpl [OPTIONS] <FILE>
```

| Flag | Description |
|---|---|
| `-t, --target` | Also unimplement target-tagged functions |

### `code get-ghost` vs `list`

- `code get-ghost` returns only ghost code (requires, ensures, asserts, invariants, proof blocks) **without function names**.
- `list` returns **all** segments (functions, structs, enums, traits, impls, macros, plus all ghost code) **with fully-qualified names and segment kinds**.

---

## `lynette additions` — Check Allowed Additions

Checks that only allowed code additions were made between two file versions.

```bash
lynette additions <FILE1> <FILE2>
```

---

## `lynette benchmark` — Benchmark Preparation

Prepares a Verus file for benchmarking by cleaning up helper code.

```bash
lynette benchmark [OPTIONS] <FILE1> <FILE2>
```

| Flag | Description |
|---|---|
| `-n, --no-lemma-mode` | Erase all lemmas |

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
