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

**Added command.** Performs AST-level dependency analysis on a Verus source file. For each function, reports which `spec_fn`s (defined in the same file) it references — by walking the function's body and signature spec clauses (requires, ensures, recommends, decreases) and collecting all referenced identifiers.

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
```

Only functions with dependencies are shown in text mode.

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

1. Parses the file with `syn_verus` and collects all function definitions (free functions, impl methods, trait methods)
2. For each function, walks the AST of its body and signature spec clauses to collect all referenced identifiers (function calls, method calls, path references)
3. Cross-references those identifiers against the set of `spec_fn` / `spec(checked)` functions defined in the same file
4. For qualified references (e.g. `Foo::bar`), matches directly. For bare names (e.g. `bar`), applies a **same-impl preference heuristic**: if the calling function is inside `impl Foo`, only `Foo::bar` is matched; otherwise all spec_fns with that bare name are included
5. Reports matches using qualified names (e.g. `Foo::bar`) when available, or bare names (e.g. `bar`) otherwise

### Scope

The **source** side includes functions of **all** kinds (`exec_fn`, `proof_fn`, `spec_fn`, `default_fn`, etc.). The dependency targets (`depends_on`) are limited to **`spec_fn` and `spec_checked_fn`** defined in the same file — other function-to-function references (e.g. `proof_fn` → `proof_fn`) are not tracked. The `--filter` flag controls which source functions to *display*, not what is detected as a dependency target.

### Limitations

- Only detects references to `spec_fn`s defined **in the same file** — cross-file dependencies are not tracked.
- Without full type resolution, bare method calls like `self.val()` are resolved heuristically:
  - If the calling function is inside `impl Foo`, only `Foo::val` is matched (same-impl preference).
  - If no same-impl candidate exists, or the caller is a free function, **all** `spec_fn`s named `val` in the file are matched (conservative fallback).
  - This covers the common case correctly but can still over-approximate when a method calls a same-named `spec_fn` from a *different* impl via a field or argument.

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
