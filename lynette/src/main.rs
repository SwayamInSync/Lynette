use clap::{ArgGroup, Args, Parser as ClapParser, Subcommand};
use proc_macro2::TokenStream;
use quote::ToTokens;
use serde_json::json;
use std::cell::RefCell;
use std::ops::RangeInclusive;
use std::path::PathBuf;
use std::process;
use syn_verus::{FnArg, FnArgKind, Type};

mod additions;
mod benchmark_gen;
mod code;
mod deghost;
mod deps;
mod func;
mod list_segments;
//mod merge;
mod skeleton;
mod unimpl;
mod utils;

use crate::additions::*;
use crate::benchmark_gen::*;
use crate::code::*;
use crate::deghost::*;
use crate::deps::*;
use crate::func::*;
use crate::list_segments::*;
//use crate::merge::*;
use crate::skeleton::*;
use crate::unimpl::*;
use crate::utils::*;

/// Parse a string of ranges in the format of a-b,c-d,e into a vector of ranges.
fn parse_ranges(
    s: &str,
) -> Result<std::vec::Vec<RangeInclusive<usize>>, Box<dyn std::error::Error + Send + Sync>> {
    s.split(',')
        .map(|part| {
            if part.contains('-') {
                let mut range_parts = part.split('-').map(|p| p.parse::<usize>());
                let start =
                    range_parts.next().ok_or("No start for range")?.map_err(|_| "Invalid start")?;
                let end =
                    range_parts.next().ok_or("No end for range")?.map_err(|_| "Invalid end")?;
                Ok(RangeInclusive::new(start, end))
            } else {
                let num = part.parse::<usize>()?;
                Ok(RangeInclusive::new(num, num))
            }
        })
        .collect()
}

#[derive(Args)]
struct GetCallsArgs {
    file: PathBuf,
    // We have to use std::vec::Vec<...> here due to how clap treats certain types
    // of arguments.
    #[clap(short, long, value_parser = parse_ranges,
        help = "Only returns function calls for the specified line(s).",
        long_help = "Only returns function calls for the specified line(s).
The format is a comma separated list of ranges, e.g. 1-3,5,7-9.")]
    line: Option<Vec<RangeInclusive<usize>>>,
}

struct Loc {
    line: usize,
    column: usize,
}

impl Loc {
    fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }
}

impl Clone for Loc {
    fn clone(&self) -> Self {
        Self { line: self.line, column: self.column }
    }
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.line, self.column)
    }
}

impl PartialEq for Loc {
    fn eq(&self, other: &Self) -> bool {
        self.line == other.line && self.column == other.column
    }
}

impl Eq for Loc {}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.line == other.line {
            self.column.cmp(&other.column)
        } else {
            self.line.cmp(&other.line)
        }
    }
}

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Parse a string of spans in the format of a:b,c:d,e:f into a vector of spans.
fn parse_locs(s: &str) -> Result<Vec<Loc>, Box<dyn std::error::Error + Send + Sync>> {
    s.split(',')
        .map(|part| {
            part.split_once(':').ok_or_else(|| "Invalid format".into()).and_then(|(start, end)| {
                let line = start.parse::<usize>().map_err(|_| "Invalid start".to_string())?;
                let column = end.parse::<usize>().map_err(|_| "Invalid end".to_string())?;
                Ok(Loc::new(line, column))
            })
        })
        .collect()
}

#[derive(Args)]
struct RemoveSpanArgs {
    file: PathBuf,
    #[clap(short, long, help = r#"
A comma separated list of the start and end of the span in the format of (a: b) to remove."#,
    value_parser = parse_locs)]
    locs: Vec<Vec<Loc>>,
}

#[derive(Args)]
#[clap(group(ArgGroup::new("location").args(&["line", "offset", "name"]).required(true).multiple(false)))]
struct GetFuncAtArgs {
    file: PathBuf,
    #[clap(short, help = "The line number of the function.")]
    line: Option<usize>,
    #[clap(short, help = "The offset from the beginning of the file.")]
    offset: Option<usize>,
}

#[derive(Args)]
struct ParseArgs {
    file: PathBuf,
    #[clap(
        short,
        long,
        help = "Only check syntax, do not print anything",
        default_value = "false"
    )]
    check: bool,
}

#[derive(Args)]
struct DetectNLArgs {
    file: PathBuf,
    #[clap(
        short,
        long,
        help = "If set, also detect non-linear operations in function qualifiers.",
        default_value = "false"
    )]
    sig: bool,
}

/// When a flag is set, the corresponding ghost code will not be removed by the
/// deghost functions.
#[derive(Clone)]
#[derive(Args)]
pub struct DeghostMode {
    #[clap(long, help = "Compare requires (function signatures)")]
    requires: bool,
    #[clap(long, help = "Compare ensures on function signatures (loop ensures are gated by --invariants)")]
    ensures: bool,
    #[clap(long, help = "Compare recommends")]
    recommends: bool,
    #[clap(long, help = "Compare loop spec block: invariants, loop_ensures, and loop-level decreases (all proof-mode concerns)")]
    invariants: bool,
    #[clap(long, help = "Compare spec functions")]
    spec: bool,
    #[clap(long, help = "Compare proof functions")]
    proof: bool,
    #[clap(long, help = "Compare asserts")]
    asserts: bool,
    #[clap(long, help = "Compare assert_forall expressions")]
    assert_forall: bool,
    #[clap(long, help = "Compare asserts with annotations(e.g. #[warn(llm_do_not_change)])")]
    asserts_anno: bool,
    #[clap(long, help = "Compare decreases on function signatures (loop decreases are gated by --invariants)")]
    decreases: bool,
    #[clap(long, help = "Compare assumes")]
    assumes: bool,
    #[clap(long, help = "Compare proof blocks")]
    proof_block: bool,
}

impl DeghostMode {
    pub fn replace_with(&mut self, other: &DeghostMode) {
        self.requires = other.requires;
        self.ensures = other.ensures;
        self.recommends = other.recommends;
        self.invariants = other.invariants;
        self.spec = other.spec;
        self.proof = other.proof;
        self.asserts = other.asserts;
        self.assert_forall = other.assert_forall;
        self.asserts_anno = other.asserts_anno;
        self.decreases = other.decreases;
        self.assumes = other.assumes;
        self.proof_block = other.proof_block;
    }
}

thread_local! {
    static DEGHOST_MODE_OPT: RefCell<DeghostMode> = RefCell::new(DeghostMode::default());
}

/// By default, all flags are set to false so that all ghost code will be removed.
impl Default for DeghostMode {
    fn default() -> Self {
        Self {
            requires: false,
            ensures: false,
            recommends: false,
            invariants: false,
            spec: false,
            proof: false,
            asserts: false,
            assert_forall: false,
            asserts_anno: false,
            decreases: false,
            assumes: false,
            proof_block: false,
        }
    }
}

#[derive(Args)]
struct AllowedAdditionsArgs {
    #[clap(help = "Path for original file")]
    file1: PathBuf,
    #[clap(help = "Path for changed file")]
    file2: PathBuf
}

#[derive(Args)]
struct BenchmarkGenArgs {
    #[clap(help = "Path for input file")]
    file1: PathBuf,
    #[clap(help = "Path for output file")]
    file2: PathBuf,
    #[clap(short, long, action, help = "flag to erase all lemmas (true if lemmas should be erased)")]
    no_lemma_mode: bool
}

#[derive(Args)]
struct CompareArgs {
    file1: PathBuf,
    file2: PathBuf,

    #[clap(
        short,
        long,
        action,
        long_help = "(Deprecated)Targer mode. If set, the comparison will be more strict on the qualifier and spec function.
 This flag may be extended futher in the future."
    )]
    target: bool,

    #[clap(long, help = "Enable all spec-related flags (spec, requires, ensures, recommends, decreases)")]
    spec_mode: bool,

    #[clap(long, help = "Enable all proof-related flags (proof, invariants, asserts, assert-forall, assumes, proof-block)")]
    proof_mode: bool,

    #[clap(
        long,
        help = "When used with --spec-mode, ignore *new* proof-fn helpers that <FILE2> \
                introduces but that are not present in <FILE1>. The comparison is \
                directional: <FILE1> is treated as the original/spec-defining file and \
                <FILE2> as the candidate (e.g. a model-generated proof completion). \
                Proof fns present in <FILE1> must still be present in <FILE2> with an \
                identical signature (incl. requires/ensures/recommends/decreases) — \
                renaming or deleting an existing proof fn is therefore detected as a \
                difference. Has no effect outside --spec-mode."
    )]
    allow_helpers: bool,

    #[clap(flatten)]
    opts: DeghostMode,

    #[clap(
        short,
        long,
        help = "If set, the two compared files after deghosting will be printed out.",
        default_value = "false"
    )]
    verbose: bool,
}

#[derive(Args)]
struct FunctionArgs {
    file: PathBuf,
    function: String,
}

#[derive(Args)]
struct ExtractFunctionArgs {
    file: PathBuf,
    #[clap(short, long, help = "A list of comma-separated function names.", value_delimiter = ',')]
    function: Vec<String>,
    #[clap(short, help = "Only return the function body.", default_value = "false")]
    body: bool,
}

#[derive(ClapParser)]
#[command(about)]
struct FunctionArgs2 {
    /// Original file
    file: PathBuf,
    /// File containing the functions to add
    file2: PathBuf,
    /// Replace the functions in <FILE> by the functions in <FILE2> if conflicts occur
    #[clap(short, long, default_value = "false")]
    replace: bool,
    #[clap(
        short,
        long,
        help = "A list of comma-separated function names to add in <FILE2>",
        value_delimiter = ',',
        default_value = ""
    )]
    funcs: Vec<String>,
}

#[derive(Args)]
struct PruneQualiArgs {
    /// Verus source code file
    file: PathBuf,
    /// Function name
    fname: String,
    #[clap(long, help = "Prune pre-conditions.", default_value = "false")]
    pre: bool,
    #[clap(long, help = "Prune post-conditions.", default_value = "false")]
    post: bool,
    #[clap(
        long,
        short,
        help = "Prune pre- and post-conditions. Same as --pre --post",
        default_value = "true"
    )]
    all: bool,
}

#[derive(Args)]
struct MergeArgs {
    file1: PathBuf,
    file2: PathBuf,
    #[clap(flatten)]
    opts: DeghostMode,

    #[clap(long, help = "Merge everyting.", default_value = "false")]
    all: bool,
}

#[derive(Args)]
struct UnimplArgs {
    file1: PathBuf,
    #[clap(
        short,
        long,
        help = "If set, also unimplement functions tagged with ",
        default_value = "false"
    )]
    target: bool,
}

#[derive(Args)]
struct GetGhostArgs {
    file: PathBuf,
    #[clap(
        short,
        long,
        help = "Prints byte offsets instead of line/column numbers.",
        default_value = "false"
    )]
    byte: bool,
    #[clap(
        short,
        long,
        help = "Prints line/column numbers instead of byte offsets.",
        default_value = "true"
    )]
    loc: bool,
}

#[derive(Subcommand)]
enum FunctionCommands {
    #[clap[about =
            r#"Add the functions in <FILE2> to <FILE>.

Both files should contain exact one verus!{...} macro.

Use --replace will replace the function if conflicts occur;
Otherwise, an error will be thrown on conflicts.

The result will be printed to stdout."#
    ]]
    Add(FunctionArgs2),

    #[clap[about = "Extract a function in a verus source code file."]]
    Extract(ExtractFunctionArgs),

    #[clap[about = "Returns the arguments of a function in a verus source code file."]]
    GetArgs(FunctionArgs),

    Remove(FunctionArgs),

    #[clap[about = "Detect whether a function contains non-linear operations in verus assert."]]
    DetectNL(FunctionArgs),

    PruneQuali(PruneQualiArgs),
}

#[derive(Subcommand)]
enum CodeCommands {
    #[clap(about = "Get the function calls in a verus source code file.")]
    GetCalls(GetCallsArgs),
    #[clap(about = "Get the function at a specific line or offset in a verus source code file")]
    GetFunc(GetFuncAtArgs),
    #[clap(
        about = "Detect all non-linear operations in a verus source code file. Returns a list of (start, end) positions of the NL operations."
    )]
    DetectNL(ParseArgs),
    #[clap(about = "WIP: Get the target of a verus source code file.")]
    GetTarget(ParseArgs),
    #[clap(about = r#"Merge the proof code of two verus source code files.

The two files should have the exact same exec-code.
Currently only merging invariants is allowed. (use only `--invariants` flag)
Using other flags may lead to undefined behavior.

If there are conflicts in the non-merging part, <FILE1> is preferred.
"#)]
    Merge(MergeArgs),
    Unimpl(UnimplArgs),
    #[clap(
        about = r#"Get all ghost code in a verus source code file. Returns a list of (type, LOC) of the expression.

Currently we support ensures, requires, assert, invariant.

The returned list is in the AST order.
"#
    )]
    GetGhost(GetGhostArgs),
    #[clap(about = "Remove ghost code of the given starting spans in a verus source code file.")]
    RemoveGhost(RemoveSpanArgs),
}

#[derive(Args)]
struct ListArgs {
    file: PathBuf,
    #[clap(
        short,
        long,
        help = "Output in JSON format instead of text.",
        default_value = "false"
    )]
    json: bool,
    #[clap(
        short,
        long,
        help = "Filter by segment kind (e.g. spec_fn, proof_fn, exec_fn, requires, ensures, struct, enum, etc.). Comma-separated.",
        value_delimiter = ','
    )]
    filter: Option<Vec<String>>,
}

#[derive(Args)]
struct SkeletonArgs {
    file: PathBuf,
}

#[derive(Args)]
struct DepsArgs {
    file: PathBuf,
    #[clap(
        short,
        long,
        help = "Output in JSON format instead of text.",
        default_value = "false"
    )]
    json: bool,
    #[clap(
        short,
        long,
        help = "Filter source functions by kind (e.g. proof_fn,spec_fn). Only show deps for these kinds. Comma-separated.",
        value_delimiter = ','
    )]
    filter: Option<Vec<String>>,
    #[clap(
        long,
        help = "Only show functions that have at least one dependency.",
        default_value = "false"
    )]
    non_empty: bool,
}

#[derive(Subcommand)]
enum Commands {
    #[clap(about = r#"Compare whether two verus source code files generates the same rust code.

Various flags can be set to have fine-grained control over what ghost code should also be compared."#)]
    Compare(CompareArgs),
    Parse(ParseArgs),
    #[clap(subcommand, about = "Operations on functions, use func --help for more information")]
    Func(FunctionCommands),
    #[clap(subcommand)]
    Code(CodeCommands),
    Additions(AllowedAdditionsArgs),
    Benchmark(BenchmarkGenArgs),
    #[clap(about = r#"List all Verus segments in a file with their types and locations.

Extracts spec functions, proof functions, exec functions, requires/ensures clauses,
assert/assume statements, loop invariants, proof blocks, structs, enums, traits, impls, etc.

Each segment is annotated with its kind and fully-qualified name.
Example output:
  spec_fn:ReconcileIdAllocator::allocate:((228, 4), (232, 5))
  requires:entails_trans:((69, 8), (69, 20))
"#)]
    List(ListArgs),
    #[clap(about = r#"Generate a skeleton of a Verus source file.

Replaces the bodies of leaf-level items (function blocks, struct/enum field
lists, requires/ensures/decreases expressions, const/static initializers, ...)
with `// TODO fill here` placeholders, while preserving the surrounding
container items (mod, impl, trait, verus! macro).

The result is intended to be fed to a model as a structural prompt that
conditions it on where to write what.
"#)]
    Skeleton(SkeletonArgs),
    #[clap(about = r#"Compute dependencies between functions in a Verus file.

For each function (proof_fn, spec_fn, etc.), reports which spec_fns defined in the
same file it references, based on AST-level identifier analysis.

Output includes the function name, kind, and a list of spec_fn dependencies.
"#)]
    Deps(DepsArgs),
}

#[derive(ClapParser)]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

// Compare two verus source code files. Return true if the rust part of the files are the same.
fn compare_files(args: &CompareArgs) -> Result<bool, Error> {
    let (f1, f2) = (args.file1.clone(), args.file2.clone());

    let target_mode = args.target;

    let mut mode = args.opts.clone();

    if target_mode {
        mode.requires = true;
        mode.ensures = true;
        mode.assumes = true;
        mode.decreases = true;
    }

    if args.spec_mode {
        mode.spec = true;
        mode.requires = true;
        mode.ensures = true;
        mode.recommends = true;
        // Note: do NOT set `mode.decreases = true` here. Signature-level
        // `decreases` is termination scaffolding (two functions with
        // identical bodies but different `decreases` are extensionally
        // equivalent) and is unconditionally stripped under `--spec-mode`
        // by `keep_sig_decreases` in deghost.rs — the masker blanks
        // `decreases` per-mode (spec-mode on spec_fn sigs, proof-mode on
        // proof_fn sigs, exec-mode on exec_fn sigs) and the verifier
        // mirrors that by ignoring all signature `decreases`. Pass
        // `--decreases` explicitly to keep them.  Loop-level `decreases`
        // is gated by `mode.invariants` and stays off under spec-mode.
    }

    if args.proof_mode {
        mode.proof = true;
        mode.invariants = true;
        mode.asserts = true;
        mode.assert_forall = true;
        mode.assumes = true;
        mode.proof_block = true;
    }

    fextract_pure_rust(f1, &mode).and_then(|result1| {
        fextract_pure_rust(f2, &mode).and_then(|result2| {
            let (result1, result2) = if args.allow_helpers && args.spec_mode {
                strip_proof_fn_helpers(result1, result2)
            } else {
                (result1, result2)
            };
            if args.verbose {
                println!("{}", fprint_file(&result1, Formatter::VerusFmt));
                println!("{}", fprint_file(&result2, Formatter::VerusFmt));
            }
            Ok(result1 == result2)
        })
    })
}

/// Collect proof-fn names defined at the top level or inside `impl` blocks of
/// a (deghosted) file. Top-level proof fns are keyed by their identifier;
/// `impl`-bound proof fns are keyed by `<self_ty>::<method>` so methods on
/// different types don't collide.
fn collect_proof_fn_names(file: &syn_verus::File) -> std::collections::HashSet<String> {
    use syn_verus::FnMode;
    fn is_proof(mode: &FnMode) -> bool {
        matches!(mode, FnMode::Proof(_) | FnMode::ProofAxiom(_))
    }
    let mut names = std::collections::HashSet::new();
    for item in &file.items {
        match item {
            syn_verus::Item::Fn(f) if is_proof(&f.sig.mode) => {
                names.insert(f.sig.ident.to_string());
            }
            syn_verus::Item::Impl(i) => {
                let self_ty = i.self_ty.to_token_stream().to_string();
                for ii in &i.items {
                    if let syn_verus::ImplItem::Fn(m) = ii {
                        if is_proof(&m.sig.mode) {
                            names.insert(format!("{}::{}", self_ty, m.sig.ident));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    names
}

/// Drop from `file` any proof fn whose name does not appear in `keep`.
fn drop_proof_fns_not_in(
    file: syn_verus::File,
    keep: &std::collections::HashSet<String>,
) -> syn_verus::File {
    use syn_verus::FnMode;
    fn is_proof(mode: &FnMode) -> bool {
        matches!(mode, FnMode::Proof(_) | FnMode::ProofAxiom(_))
    }
    let new_items = file
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn_verus::Item::Fn(ref f) if is_proof(&f.sig.mode) => {
                if keep.contains(&f.sig.ident.to_string()) {
                    Some(item)
                } else {
                    None
                }
            }
            syn_verus::Item::Impl(mut i) => {
                let self_ty = i.self_ty.to_token_stream().to_string();
                i.items.retain(|ii| match ii {
                    syn_verus::ImplItem::Fn(m) if is_proof(&m.sig.mode) => {
                        keep.contains(&format!("{}::{}", self_ty, m.sig.ident))
                    }
                    _ => true,
                });
                Some(syn_verus::Item::Impl(i))
            }
            _ => Some(item),
        })
        .collect();
    syn_verus::File {
        shebang: file.shebang,
        attrs: file.attrs,
        items: new_items,
    }
}

/// Asymmetric pass for `--allow-helpers`. Treats `f1` as the original file and
/// `f2` as the candidate (model output). Drops from `f2` any proof fn whose
/// name is not in `f1`; `f1` is left untouched. This means:
///  * new proof helpers in `f2` are ignored (allowed),
///  * removed/renamed proof fns from `f1` produce a diff (forbidden).
///
/// Proof fns present in both are kept on both sides so that `--spec-mode`
/// continues to detect changes to their signature / requires / ensures /
/// recommends / decreases.
fn strip_proof_fn_helpers(
    f1: syn_verus::File,
    f2: syn_verus::File,
) -> (syn_verus::File, syn_verus::File) {
    let names1 = collect_proof_fn_names(&f1);
    (f1, drop_proof_fns_not_in(f2, &names1))
}

// Borrowed and modified from syn/src/item.rs
fn maybe_variadic_to_tokens(
    arg: &FnArg,
    arg_tokens: &mut TokenStream,
    ty_tokens: &mut TokenStream,
) -> bool {
    arg.tracked.to_tokens(arg_tokens);

    let arg = match &arg.kind {
        FnArgKind::Typed(arg) => arg,
        FnArgKind::Receiver(receiver) => {
            receiver.to_tokens(arg_tokens);
            return false;
        }
    };

    match arg.ty.as_ref() {
        Type::Verbatim(ty) if ty.to_string() == "..." => true,
        _ => {
            arg.pat.to_tokens(arg_tokens);
            arg.ty.to_tokens(ty_tokens);
            false
        }
    }
}

fn main() {
    let args = Cli::parse();

    match args.command {
        Commands::Additions(args) => {
            let res = check_allowed_additions_only(args.file1, args.file2).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });

            if !res {
                println!("Disallowed changes detected");
                process::exit(1);
            }
        }
        Commands::Benchmark(args) => {
            benchmark_cleanup(args.file1, args.file2, args.no_lemma_mode).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });
        }
        Commands::Compare(args) => {
            let res = compare_files(&args).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });

            if !res {
                println!("Files are different");
                process::exit(1);
            }
        }
        Commands::Parse(args) => {
            let filepath = args.file;
            let check = args.check;

            let file = fload_file(&filepath).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });

            if !check {
                let pretty_file = format!("{:#?}", file.to_token_stream()).replace("    ", "  ");
                println!("{}", pretty_file);
            }
            fextract_verus_macro(&filepath)
                .map(|(files, _)| {
                    if !check {
                        for file in files {
                            let pretty_file = format!("{:#?}", file.to_token_stream()).replace("    ", "  ");
                            println!("{}", pretty_file);
                        }
                    }
                })
                .unwrap_or_else(|e| {
                    eprintln!("{}", e);
                    process::exit(1);
                });

            //println!("{}", fprint_file(&file, Formatter::Mix));
        }
        Commands::Func(fcmd) => {
            match fcmd {
                FunctionCommands::GetArgs(args) => {
                    let filepath = args.file;
                    let function = args.function;

                    let funcs = fextract_function(&filepath, &vec![function]).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });

                    let func = &funcs[0];
                    let ret: serde_json::Value = func
                        .get_sig()
                        .inputs
                        .iter()
                        .map(|arg| {
                            let mut arg_token = TokenStream::new();
                            let mut ty_token = TokenStream::new();
                            if maybe_variadic_to_tokens(&arg, &mut arg_token, &mut ty_token) {
                                eprintln!("Varaidic arguments are not supported");
                                process::exit(1);
                            }

                            json!({
                                "arg": arg_token.to_string(),
                                "ty": ty_token.to_string(),
                            })
                        })
                        .collect();

                    println!("{}", ret);
                }
                FunctionCommands::Extract(args) => {
                    let filepath = args.file;
                    let funcs = args.function;
                    let body = args.body;

                    fextract_function(&filepath, &funcs)
                        .and_then(|funcs| {
                            let func = &funcs[0];

                            if !body {
                                print_block(&filepath, func.get_span_rect()).unwrap_or(());
                            } else {
                                print_block(&filepath, get_block_rect(func.get_block()))
                                    .unwrap_or(());
                            }
                            Ok(())
                        })
                        .unwrap_or_else(|e| {
                            eprintln!("{}", e);
                            process::exit(1);
                        });
                }
                FunctionCommands::Remove(args) => {
                    let filepath = args.file;
                    let function = args.function;

                    fremove_function(&filepath, function)
                        .and_then(|new_file| {
                            println!("{}", fprint_file(&new_file, Formatter::Mix));
                            Ok(())
                        })
                        .unwrap_or_else(|e| {
                            eprintln!("{}", e);
                            process::exit(1);
                        })
                }
                FunctionCommands::Add(args) => {
                    let filepath1 = args.file;
                    let filepath2 = args.file2;
                    let replace = args.replace;
                    let funcs = args.funcs;

                    // let new_funs = ffind_all_functions(&filepath2).unwrap_or_else(|e| {
                    //     eprintln!("{}", e);
                    //     process::exit(1);
                    // });

                    let new_funcs = fextract_function(&filepath2, &funcs).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });

                    fextract_verus_macro(&filepath1)
                        .map(|(mut files, orig)| {
                            // We shouldn't be doing this in a loop since it'll insert the same functions multiple times
                            // Assert there is only one `verus!` macro.
                            assert!(files.len() == 1);
                            for file in &mut files {
                                insert_functions(file, new_funcs.clone(), replace).unwrap_or_else(
                                    |e| {
                                        eprintln!("{}", e);
                                        process::exit(1);
                                    },
                                );
                            }

                            let new_file = update_verus_macros_files(&orig, files);

                            println!("{}", fprint_file(&new_file, Formatter::Mix));
                        })
                        .unwrap_or_else(|e| {
                            eprintln!("{}", e);
                            process::exit(1);
                        });
                }
                FunctionCommands::DetectNL(args) => {
                    let filepath = args.file;
                    let function = args.function;

                    fextract_function(&filepath, &vec![function])
                        .and_then(|_func| {
                            unimplemented!();
                            // let nl = detect_non_linear_func(&func);
                            // println!("{}", nl);
                            // Ok(())
                        })
                        .unwrap_or_else(|e| {
                            eprintln!("{}", e);
                            process::exit(1);
                        })
                }
                FunctionCommands::PruneQuali(args) => {
                    let filepath = args.file;
                    let fname = args.fname;
                    let pre = args.pre || args.all;
                    let post = args.post || args.all;

                    fextract_function(&filepath, &vec![fname])
                        .and_then(|funcs| {
                            assert!(funcs.len() == 1);
                            let func = &funcs[0];

                            match func {
                                FnMethod::Fn(f) => {
                                    let sig = &f.sig;
                                    let new_sig = syn_verus::Signature {
                                        publish: syn_verus::Publish::Default,
                                        constness: sig.constness.clone(),
                                        asyncness: sig.asyncness.clone(),
                                        unsafety: sig.unsafety.clone(),
                                        abi: sig.abi.clone(),
                                        broadcast: sig.broadcast.clone(),
                                        mode: sig.mode.clone(),
                                        fn_token: sig.fn_token.clone(),
                                        ident: sig.ident.clone(),
                                        generics: sig.generics.clone(),
                                        paren_token: sig.paren_token.clone(),
                                        inputs: sig.inputs.clone(),
                                        variadic: sig.variadic.clone(),
                                        output: sig.output.clone(),
                                        spec: syn_verus::SignatureSpec {
                                            prover: sig.spec.prover.clone(),
                                            requires: if !pre { sig.spec.requires.clone() } else { None }, // Removed
                                            recommends: sig.spec.recommends.clone(),
                                            ensures: if !post { sig.spec.ensures.clone() } else { None }, // Removed
                                            decreases: sig.spec.decreases.clone(),
                                            invariants: sig.spec.invariants.clone(),
                                            default_ensures: if !post { sig.spec.default_ensures.clone() } else { None },
                                            returns: sig.spec.returns.clone(),
                                            unwind: sig.spec.unwind.clone(),
                                            with: sig.spec.with.clone(),
                                        }
                                    };

                                    let new_fn = syn_verus::ItemFn {
                                        attrs: f.attrs.clone(),
                                        vis: f.vis.clone(),
                                        sig: new_sig,
                                        block: f.block.clone(),
                                        semi_token: f.semi_token.clone(),
                                    };

                                    fextract_verus_macro(&filepath).and_then(|(mut files, orig)| {
                                        assert!(files.len() == 1);
                                        for file in &mut files {
                                            insert_functions(
                                                file,
                                                vec![FnMethod::Fn(new_fn.clone())],
                                                true,
                                            )
                                            .unwrap_or_else(|e| {
                                                eprintln!("{}", e);
                                                process::exit(1);
                                            });
                                        }

                                        let new_file = update_verus_macros_files(&orig, files);

                                        println!("{}", fprint_file(&new_file, Formatter::Mix));
                                        Ok(())
                                    })
                                }
                                FnMethod::Method(_, _m) => {
                                    unimplemented!("Method is not supported yet");
                                }
                                _ => {
                                    unimplemented!();
                                }
                            }
                        })
                        .unwrap_or_else(|e| {
                            eprintln!("{}", e);
                            process::exit(1);
                        })
                }
            }
        }
        Commands::Code(ccmd) => {
            match ccmd {
                CodeCommands::GetCalls(arg) => {
                    let filepath = arg.file;
                    let ranges = arg.line.clone();

                    let objs = get_calls_at(&filepath, ranges).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });

                    println!("{}", json!(objs));
                }
                CodeCommands::GetFunc(arg) => {
                    let filepath = arg.file;
                    let line = arg.line;
                    let offset = arg.offset;

                    let result = get_func_at(&filepath, line, offset).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });
                    println!("[{}]", result.join(","));
                }
                CodeCommands::DetectNL(arg) => {
                    let filepath = arg.file;

                    let result = fdetect_nl(&filepath).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });

                    println!("{:?}", result);
                }
                CodeCommands::GetTarget(arg) => {
                    let filepath = arg.file;

                    let result = fget_target(&filepath).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });

                    println!(
                        "[{}]",
                        result
                            .iter()
                            .map(|f| {
                                match f {
                                    FnMethod::Fn(f) => f.sig.ident.to_string(),
                                    FnMethod::Method(_, m) => m.sig.ident.to_string(),
                                    _ => unimplemented!(),
                                }
                            })
                            .collect::<Vec<String>>()
                            .join(",")
                    );
                }
                CodeCommands::Merge(_arg) => {
                    // let filepath1 = &arg.file1;
                    // let filepath2 = &arg.file2;
                    // let mode = if arg.all {
                    //     &DeghostMode {
                    //         requires: true,
                    //         ensures: true,
                    //         invariants: true,
                    //         spec: true,
                    //         asserts: true,
                    //         asserts_anno: true,
                    //         decreases: true,
                    //         assumes: true,
                    //     }
                    // } else {
                    //     &arg.opts
                    // };

                    // DEGHOST_MODE_OPT.with(|mode| {
                    //     mode.borrow_mut().replace_with(&arg.opts);
                    // });

                    // fmerge_files(filepath1, filepath2, mode)
                    //     .and_then(|f| {
                    //         println!("{}", fprint_file(&f, Formatter::Mix));
                    //         Ok(())
                    //     })
                    //     .unwrap_or_else(|e| {
                    //         eprintln!("{}", e);
                    //         process::exit(1);
                    //     });

                    process::exit(1); // unsupported for now
                }
                CodeCommands::Unimpl(arg) => {
                    let filepath = arg.file1;
                    let target = arg.target;

                    funimpl_file(&filepath, target)
                    .and_then(|f| {
                        let ret: serde_json::Value = f
                            .iter()
                            .map(|(n, f)| json!({"name":n, "code": fprint_file(&f, Formatter::Mix)}))
                            .collect();

                        println!("{}", ret);
                        Ok(())
                    })
                    .unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });
                }
                CodeCommands::GetGhost(arg) => {
                    let filepath = &arg.file;

                    let result = fget_ghosts(filepath).unwrap_or_else(|e| {
                        eprintln!("{}", e);
                        process::exit(1);
                    });

                    if arg.byte {
                        unimplemented!();
                    } else {
                        result.iter().for_each(|(t, loc)| {
                            println!(
                                "{}:(({}, {}), ({}, {}))",
                                t,
                                loc.start().line,
                                loc.start().column,
                                loc.end().line,
                                loc.end().column
                            );
                        });
                    }
                }
                CodeCommands::RemoveGhost(arg) => {
                    let _filepath = arg.file;
                    // clap parses the argument as a Vec<Vec<Loc>> because it allows multiple --locs
                    // We might find a better way to parse this in the future.
                    // But for now, we just take the first element.
                    let locs = &arg.locs[0];

                    println!("{:?}", locs);

                    unimplemented!();
                }
            }
        }
        Commands::List(args) => {
            let segments = flist_segments(&args.file).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });

            let segments = if let Some(ref filters) = args.filter {
                segments
                    .into_iter()
                    .filter(|seg| filters.iter().any(|f| f == seg.kind.label()))
                    .collect()
            } else {
                segments
            };

            if args.json {
                print_segments_json(&segments);
            } else {
                print_segments_text(&segments);
            }
        }
        Commands::Skeleton(args) => {
            let out = fskeleton_file(&args.file).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });
            print!("{}", out);
        }
        Commands::Deps(args) => {
            let deps = fcompute_deps(&args.file).unwrap_or_else(|e| {
                eprintln!("{}", e);
                process::exit(1);
            });

            let deps: Vec<_> = if let Some(ref filters) = args.filter {
                deps.into_iter()
                    .filter(|dep| filters.iter().any(|f| f == dep.kind.label()))
                    .collect()
            } else {
                deps
            };

            let deps: Vec<_> = if args.non_empty {
                deps.into_iter().filter(|dep| !dep.depends_on.is_empty()).collect()
            } else {
                deps
            };

            if args.json {
                print_deps_json(&deps);
            } else {
                print_deps_text(&deps);
            }
        }
    };
}

// ===========================================================================
// CLI integration tests
// ===========================================================================

#[cfg(test)]
mod cli_tests {
    use std::path::PathBuf;
    use std::process::Command;

    fn lynette_bin() -> PathBuf {
        // cargo test builds the binary; its path is next to the test binary
        let mut sibling = std::env::current_exe().unwrap();
        sibling.pop(); // remove test binary name
        sibling.pop(); // remove "deps-*" directory
        sibling.push("lynette");
        if sibling.exists() {
            return sibling;
        }

        // Fallback: use CARGO_MANIFEST_DIR
        let mut workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        workspace_root.pop();
        let release = workspace_root.join("target/release/lynette");
        if release.exists() {
            return release;
        }

        let debug = workspace_root.join("target/debug/lynette");
        if debug.exists() {
            return debug;
        }

        panic!(
            "could not find lynette binary for CLI tests; looked for: {}, {}, {}",
            sibling.display(),
            release.display(),
            debug.display()
        );
    }

    fn fixture_path(name: &str) -> PathBuf {
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        p.push("tests/fixtures");
        p.push(name);
        p
    }

    fn run_deps(args: &[&str], fixture: &str) -> (String, String, i32) {
        let fix = fixture_path(fixture);
        let fix_str = fix.to_str().unwrap();
        let mut cmd_args: Vec<&str> = vec!["deps"];
        cmd_args.extend_from_slice(args);
        cmd_args.push(fix_str);
        let output = Command::new(lynette_bin())
            .args(&cmd_args)
            .output()
            .expect("failed to execute lynette");
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        let code = output.status.code().unwrap_or(-1);
        (stdout, stderr, code)
    }

    #[test]
    fn cli_deps_json_output_is_valid() {
        let (stdout, _, code) = run_deps(&["-j"], "basic_deps.rs");
        assert_eq!(code, 0, "exit code should be 0");
        let parsed: serde_json::Value = serde_json::from_str(&stdout)
            .expect("deps -j should produce valid JSON");
        assert!(parsed.is_array());
    }

    #[test]
    fn cli_deps_text_output_contains_arrow() {
        let (stdout, _, code) = run_deps(&["--non-empty"], "basic_deps.rs");
        assert_eq!(code, 0);
        assert!(stdout.contains("->"), "text output should contain '->' arrows for deps");
    }

    #[test]
    fn cli_deps_filter_by_kind() {
        let (stdout, _, code) = run_deps(&["-j", "-f", "proof_fn"], "basic_deps.rs");
        assert_eq!(code, 0);
        let parsed: Vec<serde_json::Value> = serde_json::from_str(&stdout).unwrap();
        assert!(!parsed.is_empty(), "there should be proof_fn entries");
        for entry in &parsed {
            assert_eq!(entry["kind"], "proof_fn",
                "filtering by proof_fn should only return proof_fn entries");
        }
    }

    #[test]
    fn cli_deps_non_empty_excludes_no_dep_fns() {
        let (stdout, _, code) = run_deps(&["-j", "--non-empty"], "basic_deps.rs");
        assert_eq!(code, 0);
        let parsed: Vec<serde_json::Value> = serde_json::from_str(&stdout).unwrap();
        for entry in &parsed {
            let deps = entry["depends_on"].as_array().unwrap();
            assert!(!deps.is_empty(),
                "--non-empty should exclude functions with no dependencies");
        }
    }

    #[test]
    fn cli_deps_combined_filter_and_non_empty() {
        let (stdout, _, code) = run_deps(
            &["-j", "-f", "proof_fn", "--non-empty"],
            "basic_deps.rs",
        );
        assert_eq!(code, 0);
        let parsed: Vec<serde_json::Value> = serde_json::from_str(&stdout).unwrap();
        for entry in &parsed {
            assert_eq!(entry["kind"], "proof_fn");
            assert!(!entry["depends_on"].as_array().unwrap().is_empty());
        }
        let names: Vec<&str> = parsed.iter()
            .map(|e| e["name"].as_str().unwrap())
            .collect();
        assert!(names.contains(&"my_proof"));
        assert!(names.contains(&"multi_dep_proof"));
        assert!(!names.contains(&"no_dep_proof"));
    }

    #[test]
    fn cli_deps_invalid_file_returns_nonzero() {
        let output = Command::new(lynette_bin())
            .args(&["deps", "/tmp/nonexistent_file_12345.rs"])
            .output()
            .expect("failed to execute lynette");
        assert_ne!(output.status.code().unwrap_or(0), 0);
    }

    #[test]
    fn cli_deps_empty_file_returns_empty_json() {
        let (stdout, _, code) = run_deps(&["-j"], "no_functions.rs");
        assert_eq!(code, 0);
        let parsed: Vec<serde_json::Value> = serde_json::from_str(&stdout).unwrap();
        assert!(parsed.is_empty());
    }

    #[test]
    fn cli_deps_text_none_for_no_deps() {
        let (stdout, _, code) = run_deps(&[], "basic_deps.rs");
        assert_eq!(code, 0);
        assert!(stdout.contains("(none)"),
            "functions with no deps should show (none) in text mode");
    }

    #[test]
    fn cli_deps_json_has_required_fields() {
        let (stdout, _, code) = run_deps(&["-j"], "basic_deps.rs");
        assert_eq!(code, 0);
        let parsed: Vec<serde_json::Value> = serde_json::from_str(&stdout).unwrap();
        assert!(!parsed.is_empty());
        for entry in &parsed {
            assert!(entry.get("name").is_some(), "each entry should have 'name'");
            assert!(entry.get("kind").is_some(), "each entry should have 'kind'");
            assert!(entry.get("depends_on").is_some(), "each entry should have 'depends_on'");
            assert!(entry["depends_on"].is_array(), "'depends_on' should be an array");
        }
    }

    #[test]
    fn cli_deps_real_benchmark_no_panic() {
        let (_, _, code) = run_deps(&["-j"], "real_benchmark.rs");
        assert_eq!(code, 0, "real benchmark file should not panic");
    }

    // ── compare --spec-mode --allow-helpers ─────────────────────────────

    fn write_tmp(name: &str, content: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "lynette_test_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join(name);
        std::fs::write(&p, content).unwrap();
        p
    }

    fn run_compare(extra_args: &[&str], a: &PathBuf, b: &PathBuf) -> i32 {
        let mut args: Vec<&str> = vec!["compare"];
        args.extend_from_slice(extra_args);
        let a_s = a.to_str().unwrap();
        let b_s = b.to_str().unwrap();
        args.push(a_s);
        args.push(b_s);
        Command::new(lynette_bin())
            .args(&args)
            .output()
            .expect("failed to execute lynette")
            .status
            .code()
            .unwrap_or(-1)
    }

    const COMPARE_BASE: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn p(x: nat) -> bool { x > 10 }

    proof fn equiv(x: nat)
        ensures p(x) =~= p(x),
    { }

    fn use_p(x: u32) -> (r: u32)
        requires p(x as nat),
        ensures r == x,
    { x }
}
"#;

    /// Same file as COMPARE_BASE but with an *added* proof helper lemma.
    const COMPARE_WITH_PROOF_HELPER: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn p(x: nat) -> bool { x > 10 }

    proof fn equiv(x: nat)
        ensures p(x) =~= p(x),
    {
        helper(x);
    }

    proof fn helper(x: nat)
        ensures true,
    { }

    fn use_p(x: u32) -> (r: u32)
        requires p(x as nat),
        ensures r == x,
    { x }
}
"#;

    #[test]
    fn cli_compare_spec_mode_flags_added_proof_helper_without_allow_helpers() {
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", COMPARE_WITH_PROOF_HELPER);
        let code = run_compare(&["--spec-mode"], &a, &b);
        assert_eq!(code, 1, "added proof helper should be flagged without --allow-helpers");
    }

    #[test]
    fn cli_compare_spec_mode_allow_helpers_ignores_added_proof_helper() {
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", COMPARE_WITH_PROOF_HELPER);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 0, "added proof helper should be ignored under --allow-helpers");
    }

    #[test]
    fn cli_compare_spec_mode_allow_helpers_asymmetric_helper_in_file1_is_flagged() {
        // A proof fn present in FILE1 but absent in FILE2 is treated as a
        // *removed* lemma (the model dropped/renamed an existing one).
        // This MUST be flagged — the comparison is directional.
        let a = write_tmp("a.rs", COMPARE_WITH_PROOF_HELPER);
        let b = write_tmp("b.rs", COMPARE_BASE);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(
            code, 1,
            "removing a proof fn that existed in FILE1 must be flagged \
             (--allow-helpers is directional: only NEW helpers in FILE2 are allowed)"
        );
    }

    #[test]
    fn cli_compare_allow_helpers_still_detects_exec_change() {
        let modified = COMPARE_WITH_PROOF_HELPER.replace("r == x,", "r == x + 1,");
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", &modified);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 1, "exec ensures change must still be flagged");
    }

    #[test]
    fn cli_compare_allow_helpers_still_detects_existing_proof_fn_ensures_change() {
        // Weakening `equiv`'s ensures should still be flagged because `equiv`
        // exists in both files (it's not a helper).
        let modified = COMPARE_WITH_PROOF_HELPER
            .replace("ensures p(x) =~= p(x),", "ensures true,");
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", &modified);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 1, "existing proof fn ensures change must still be flagged");
    }

    #[test]
    fn cli_compare_allow_helpers_still_detects_added_spec_fn() {
        // A new spec fn is not a "helper" — it changes the spec surface.
        let with_extra_spec = COMPARE_BASE.replace(
            "spec fn p(x: nat) -> bool { x > 10 }",
            "spec fn p(x: nat) -> bool { x > 10 }\n    spec fn q(x: nat) -> bool { x > 0 }",
        );
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", &with_extra_spec);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 1, "added spec fn must still be flagged under --allow-helpers");
    }

    #[test]
    fn cli_compare_allow_helpers_still_detects_added_exec_fn() {
        let with_extra_exec = COMPARE_BASE.replace(
            "fn use_p(x: u32) -> (r: u32)",
            "fn extra(x: u32) -> u32 { x }\n\n    fn use_p(x: u32) -> (r: u32)",
        );
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", &with_extra_exec);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 1, "added exec fn must still be flagged under --allow-helpers");
    }

    #[test]
    fn cli_compare_allow_helpers_no_effect_without_spec_mode() {
        // Default compare ignores all ghost code, so adding a proof helper
        // doesn't change the deghosted output anyway. This test just confirms
        // --allow-helpers without --spec-mode doesn't error or change behavior.
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", COMPARE_WITH_PROOF_HELPER);
        let code = run_compare(&["--allow-helpers"], &a, &b);
        assert_eq!(code, 0);
    }

    #[test]
    fn cli_compare_allow_helpers_multiple_added_helpers() {
        let multi = COMPARE_BASE.replace(
            "proof fn equiv(x: nat)\n        ensures p(x) =~= p(x),\n    { }",
            "proof fn equiv(x: nat)\n        ensures p(x) =~= p(x),\n    {\n        h1(x); h2(x);\n    }\n\n    proof fn h1(x: nat) ensures true, { }\n\n    proof fn h2(x: nat) ensures true, { }",
        );
        let a = write_tmp("a.rs", COMPARE_BASE);
        let b = write_tmp("b.rs", &multi);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 0);
    }

    // Impl-method helpers
    const COMPARE_IMPL_BASE: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    struct S { x: u32 }
    impl S {
        spec fn ok(&self) -> bool { self.x > 0 }
        proof fn lemma_main(&self)
            ensures self.x >= 0,
        { }
        fn get(&self) -> u32 { self.x }
    }
}
"#;

    const COMPARE_IMPL_WITH_HELPER: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    struct S { x: u32 }
    impl S {
        spec fn ok(&self) -> bool { self.x > 0 }
        proof fn lemma_main(&self)
            ensures self.x >= 0,
        { self.lemma_helper(); }
        proof fn lemma_helper(&self)
            ensures true,
        { }
        fn get(&self) -> u32 { self.x }
    }
}
"#;

    #[test]
    fn cli_compare_allow_helpers_impl_method_helper_ignored() {
        let a = write_tmp("a.rs", COMPARE_IMPL_BASE);
        let b = write_tmp("b.rs", COMPARE_IMPL_WITH_HELPER);
        let without = run_compare(&["--spec-mode"], &a, &b);
        let with = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(without, 1, "impl proof method helper should be flagged without --allow-helpers");
        assert_eq!(with, 0, "impl proof method helper should be ignored under --allow-helpers");
    }

    // ════════════════════════════════════════════════════════════════════
    // Exhaustive cheat-vector suite for `--spec-mode --allow-helpers`.
    //
    // The proof-writing contract for the model is:
    //   1. Cannot change spec function bodies or signatures
    //   2. Cannot change requires/ensures of proof or exec functions
    //   3. Cannot change signatures of proof or exec functions
    //   4. CAN change proof-fn bodies, proof blocks, loop invariants, and
    //      other proof-only code inside function bodies
    //   5. CAN add new proof helper lemmas (top-level or impl methods)
    //
    // Every test below either confirms that a forbidden edit IS detected
    // (`assert_flagged`) or that an allowed edit is NOT detected
    // (`assert_equal`). FILE1 is the original; FILE2 is the candidate
    // (model output).
    // ════════════════════════════════════════════════════════════════════

    /// Run `compare --spec-mode --allow-helpers` on two snippet strings and
    /// assert the candidate is rejected (exit code 1).
    fn assert_flagged(input: &str, candidate: &str, msg: &str) {
        let a = write_tmp("input.rs", input);
        let b = write_tmp("candidate.rs", candidate);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 1, "MUST flag: {msg}");
    }

    /// Run `compare --spec-mode --allow-helpers` and assert the candidate is
    /// accepted (exit code 0).
    fn assert_equal(input: &str, candidate: &str, msg: &str) {
        let a = write_tmp("input.rs", input);
        let b = write_tmp("candidate.rs", candidate);
        let code = run_compare(&["--spec-mode", "--allow-helpers"], &a, &b);
        assert_eq!(code, 0, "MUST accept: {msg}");
    }

    fn vwrap(body: &str) -> String {
        format!("use vstd::prelude::*;\nfn main() {{}}\nverus! {{\n{}\n}}\n", body)
    }

    // ── Rule 1: spec function body must not change ──────────────────────

    #[test]
    fn cheat_spec_fn_body_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 10 }");
        let b = vwrap("spec fn p(x: nat) -> bool { x > 20 }");
        assert_flagged(&a, &b, "spec fn body change");
    }

    #[test]
    fn cheat_spec_fn_body_weakened_to_true() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 10 }");
        let b = vwrap("spec fn p(x: nat) -> bool { true }");
        assert_flagged(&a, &b, "weakening spec fn to `true` is the classic trivial-proof cheat");
    }

    #[test]
    fn cheat_spec_fn_quantifier_flipped() {
        let a = vwrap("spec fn all_gt(s: Seq<i32>, k: i32) -> bool { forall|i: int| 0 <= i < s.len() ==> s[i] > k }");
        let b = vwrap("spec fn all_gt(s: Seq<i32>, k: i32) -> bool { exists|i: int| 0 <= i < s.len() && s[i] > k }");
        assert_flagged(&a, &b, "forall→exists flip is a semantic cheat");
    }

    #[test]
    fn cheat_spec_fn_branch_swapped() {
        let a = vwrap("spec fn p(x: nat) -> bool { if x > 10 { true } else { false } }");
        let b = vwrap("spec fn p(x: nat) -> bool { if x > 10 { false } else { true } }");
        assert_flagged(&a, &b, "swapping if-branches in spec body");
    }

    // ── Rule 1: spec function signature must not change ─────────────────

    #[test]
    fn cheat_spec_fn_renamed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("spec fn q(x: nat) -> bool { x > 0 }");
        assert_flagged(&a, &b, "spec fn rename");
    }

    #[test]
    fn cheat_spec_fn_param_type_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("spec fn p(x: int) -> bool { x > 0 }");
        assert_flagged(&a, &b, "spec fn param type change");
    }

    #[test]
    fn cheat_spec_fn_param_name_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("spec fn p(y: nat) -> bool { y > 0 }");
        assert_flagged(&a, &b, "spec fn param rename (changes alpha-equivalent body too)");
    }

    #[test]
    fn cheat_spec_fn_return_type_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("spec fn p(x: nat) -> nat { x }");
        assert_flagged(&a, &b, "spec fn return type change");
    }

    #[test]
    fn cheat_spec_fn_arity_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("spec fn p(x: nat, y: nat) -> bool { x > 0 }");
        assert_flagged(&a, &b, "spec fn arity change");
    }

    #[test]
    fn cheat_spec_fn_recommends_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool recommends x > 0, { x > 10 }");
        let b = vwrap("spec fn p(x: nat) -> bool recommends true, { x > 10 }");
        assert_flagged(&a, &b, "spec fn recommends change");
    }

    #[test]
    fn cheat_spec_fn_kind_changed_to_spec_checked() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("spec(checked) fn p(x: nat) -> bool { x > 0 }");
        assert_flagged(&a, &b, "spec → spec(checked) is a contract change");
    }

    #[test]
    fn cheat_spec_fn_visibility_changed() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("pub spec fn p(x: nat) -> bool { x > 0 }");
        assert_flagged(&a, &b, "visibility change on spec fn");
    }

    // ── Rule 1: spec functions cannot be added or removed ──────────────

    #[test]
    fn cheat_added_spec_fn() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap(
            "spec fn p(x: nat) -> bool { x > 0 }\n    spec fn extra(x: nat) -> bool { true }",
        );
        assert_flagged(&a, &b, "model added a new spec fn (not allowed even as helper)");
    }

    #[test]
    fn cheat_removed_spec_fn() {
        let a = vwrap(
            "spec fn p(x: nat) -> bool { x > 0 }\n    spec fn q(x: nat) -> bool { x > 1 }",
        );
        let b = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        assert_flagged(&a, &b, "model removed a spec fn");
    }

    // ── Rule 2: requires/ensures of proof functions must not change ────

    #[test]
    fn cheat_proof_fn_ensures_weakened_to_true() {
        let a = vwrap("proof fn lem(x: nat) ensures x + 0 == x, { }");
        let b = vwrap("proof fn lem(x: nat) ensures true, { }");
        assert_flagged(&a, &b, "weakening proof fn ensures to `true` (the original bug)");
    }

    #[test]
    fn cheat_proof_fn_ensures_removed() {
        let a = vwrap("proof fn lem(x: nat) ensures x + 0 == x, { }");
        let b = vwrap("proof fn lem(x: nat) { }");
        assert_flagged(&a, &b, "proof fn ensures removed");
    }

    #[test]
    fn cheat_proof_fn_ensures_replaced() {
        let a = vwrap("proof fn lem(x: nat) ensures x + 0 == x, { }");
        let b = vwrap("proof fn lem(x: nat) ensures x >= 0, { }");
        assert_flagged(&a, &b, "proof fn ensures replaced with a different (easier) goal");
    }

    #[test]
    fn cheat_proof_fn_requires_strengthened() {
        // Stronger requires = trivially provable but cheaper for callers.
        let a = vwrap("proof fn lem(x: nat) requires x > 0, ensures x > 0, { }");
        let b = vwrap("proof fn lem(x: nat) requires false, ensures x > 0, { }");
        assert_flagged(&a, &b, "proof fn requires strengthened to `false`");
    }

    #[test]
    fn cheat_proof_fn_requires_weakened() {
        let a = vwrap("proof fn lem(x: nat) requires x > 0, ensures x > 0, { }");
        let b = vwrap("proof fn lem(x: nat) requires true, ensures x > 0, { }");
        assert_flagged(&a, &b, "proof fn requires weakened");
    }

    #[test]
    fn allowed_proof_fn_decreases_changed() {
        // Under the context-aware decreases rule, `decreases` on a proof_fn
        // signature is treated as proof-mode content (a termination measure
        // for a recursive lemma). The masking pipeline blanks it under
        // proof-mode masks; for `compare --spec-mode --allow-helpers` to
        // accept the model's completion we therefore must NOT flag changes
        // to proof_fn decreases. See `keep_sig_decreases` in deghost.rs.
        let a = vwrap("proof fn lem(x: nat) ensures true, decreases x, { }");
        let b = vwrap("proof fn lem(x: nat) ensures true, decreases 0nat, { }");
        assert_equal(&a, &b, "proof fn decreases change is allowed under --spec-mode");
    }

    #[test]
    fn allowed_proof_fn_decreases_removed() {
        // Same as above: model can drop the proof_fn decreases entirely.
        let a = vwrap("proof fn lem(x: nat) ensures true, decreases x, { }");
        let b = vwrap("proof fn lem(x: nat) ensures true, { }");
        assert_equal(&a, &b, "proof fn decreases removal is allowed under --spec-mode");
    }

    #[test]
    fn allowed_spec_fn_decreases_changed() {
        // Unified rule: signature `decreases` is termination scaffolding
        // and is ignored by `compare --spec-mode --allow-helpers` for
        // every fn kind. Tests for spec_fn here.
        let a = vwrap("spec fn p(x: nat) -> nat decreases x, { if x == 0 { 0 } else { p((x - 1) as nat) } }");
        let b = vwrap("spec fn p(x: nat) -> nat decreases 0nat, { if x == 0 { 0 } else { p((x - 1) as nat) } }");
        assert_equal(&a, &b, "spec fn decreases change is allowed under --spec-mode");
    }

    #[test]
    fn allowed_exec_fn_decreases_removed() {
        // Same rule for exec_fn signature decreases.
        let a = vwrap("fn foo(n: u64) -> (r: u64) decreases n, { if n == 0 { 0 } else { foo(n - 1) } }");
        let b = vwrap("fn foo(n: u64) -> (r: u64) { if n == 0 { 0 } else { foo(n - 1) } }");
        assert_equal(&a, &b, "exec fn decreases removal is allowed under --spec-mode");
    }

    // ── Rule 2: requires/ensures of exec functions must not change ─────

    #[test]
    fn cheat_exec_fn_requires_weakened() {
        let a = vwrap("fn foo(x: u32) -> u32 requires x > 5, { x }");
        let b = vwrap("fn foo(x: u32) -> u32 requires x > 0, { x }");
        assert_flagged(&a, &b, "exec fn requires weakened");
    }

    #[test]
    fn cheat_exec_fn_requires_removed() {
        let a = vwrap("fn foo(x: u32) -> u32 requires x > 5, { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { x }");
        assert_flagged(&a, &b, "exec fn requires removed");
    }

    #[test]
    fn cheat_exec_fn_ensures_weakened_to_true() {
        let a = vwrap("fn foo(x: u32) -> (r: u32) ensures r == x, { x }");
        let b = vwrap("fn foo(x: u32) -> (r: u32) ensures true, { x }");
        assert_flagged(&a, &b, "exec fn ensures weakened to true");
    }

    #[test]
    fn cheat_exec_fn_ensures_removed() {
        let a = vwrap("fn foo(x: u32) -> (r: u32) ensures r == x, { x }");
        let b = vwrap("fn foo(x: u32) -> (r: u32) { x }");
        assert_flagged(&a, &b, "exec fn ensures removed");
    }

    #[test]
    fn allowed_exec_fn_decreases_changed() {
        let a = vwrap("fn foo(n: u32) -> u32 decreases n, { if n == 0 { 0 } else { foo(n - 1) } }");
        let b = vwrap("fn foo(n: u32) -> u32 decreases 0u32, { if n == 0 { 0 } else { foo(n - 1) } }");
        assert_equal(&a, &b, "exec fn decreases change is allowed under --spec-mode");
    }

    // ── Rule 3: function signatures must not change ────────────────────

    #[test]
    fn cheat_exec_fn_renamed() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn bar(x: u32) -> u32 { x }");
        assert_flagged(&a, &b, "exec fn rename");
    }

    #[test]
    fn cheat_exec_fn_body_changed() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { x + 1 }");
        assert_flagged(&a, &b, "exec fn body change");
    }

    #[test]
    fn cheat_exec_fn_param_type_changed() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u64) -> u32 { x as u32 }");
        assert_flagged(&a, &b, "exec fn param type change");
    }

    #[test]
    fn cheat_exec_fn_return_type_changed() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u64 { x as u64 }");
        assert_flagged(&a, &b, "exec fn return type change");
    }

    #[test]
    fn cheat_exec_fn_named_return_pattern_changed() {
        let a = vwrap("fn foo(x: u32) -> (r: u32) ensures r == x, { x }");
        let b = vwrap("fn foo(x: u32) -> (s: u32) ensures s == x, { x }");
        assert_flagged(&a, &b, "renaming the named return binder changes the contract surface");
    }

    #[test]
    fn cheat_exec_fn_generics_changed() {
        let a = vwrap("fn foo<T>(x: T) -> T { x }");
        let b = vwrap("fn foo<T: Copy>(x: T) -> T { x }");
        assert_flagged(&a, &b, "exec fn generic bound change");
    }

    #[test]
    fn cheat_exec_fn_visibility_changed() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("pub fn foo(x: u32) -> u32 { x }");
        assert_flagged(&a, &b, "exec fn visibility change");
    }

    #[test]
    fn cheat_exec_fn_unsafety_changed() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("unsafe fn foo(x: u32) -> u32 { x }");
        assert_flagged(&a, &b, "adding `unsafe`");
    }

    #[test]
    fn cheat_proof_fn_renamed() {
        // KEY CHEAT VECTOR: under symmetric helper-stripping, renaming a
        // proof fn would silently pass. The asymmetric design must catch it.
        let a = vwrap("proof fn lemma_a(x: nat) ensures x >= 0, { }");
        let b = vwrap("proof fn lemma_b(x: nat) ensures x >= 0, { }");
        assert_flagged(
            &a,
            &b,
            "renaming an existing proof fn (asymmetric helper rule must catch this)",
        );
    }

    #[test]
    fn cheat_proof_fn_param_type_changed() {
        let a = vwrap("proof fn lem(x: nat) ensures true, { }");
        let b = vwrap("proof fn lem(x: int) ensures true, { }");
        assert_flagged(&a, &b, "proof fn param type change");
    }

    #[test]
    fn cheat_proof_fn_return_type_changed() {
        let a = vwrap("proof fn lem(x: nat) -> nat ensures true, { x }");
        let b = vwrap("proof fn lem(x: nat) -> int ensures true, { x as int }");
        assert_flagged(&a, &b, "proof fn return type change");
    }

    #[test]
    fn cheat_proof_fn_arity_changed() {
        let a = vwrap("proof fn lem(x: nat) ensures x >= 0, { }");
        let b = vwrap("proof fn lem(x: nat, y: nat) ensures x >= 0, { }");
        assert_flagged(&a, &b, "proof fn arity change");
    }

    // ── Rule 3 corollary: cannot delete an existing proof fn ───────────

    #[test]
    fn cheat_existing_proof_fn_deleted() {
        let a = vwrap(
            "proof fn keep(x: nat) ensures true, { }\n\
             proof fn delete_me(x: nat) ensures x >= 0, { }",
        );
        let b = vwrap("proof fn keep(x: nat) ensures true, { }");
        assert_flagged(&a, &b, "model deleted an existing proof fn");
    }

    // ── Rule 3: cannot add new exec functions ──────────────────────────

    #[test]
    fn cheat_added_exec_fn() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { x }\n    fn bar(x: u32) -> u32 { x }");
        assert_flagged(&a, &b, "model added a new exec fn");
    }

    #[test]
    fn cheat_removed_exec_fn() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }\n    fn bar(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { x }");
        assert_flagged(&a, &b, "model removed an exec fn");
    }

    // ── Rule 3: cannot convert between function kinds ──────────────────

    #[test]
    fn cheat_spec_fn_converted_to_proof_fn() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("proof fn p(x: nat) -> bool ensures true, { x > 0 }");
        assert_flagged(&a, &b, "spec → proof conversion (deletes a spec fn)");
    }

    #[test]
    fn cheat_spec_fn_converted_to_exec_fn() {
        let a = vwrap("spec fn p(x: nat) -> bool { x > 0 }");
        let b = vwrap("fn p(x: u32) -> bool { x > 0 }");
        assert_flagged(&a, &b, "spec → exec conversion");
    }

    #[test]
    fn cheat_proof_fn_converted_to_spec_fn() {
        // file1: proof fn `lem`. file2: spec fn `lem` (no proof fn `lem`).
        // Helper logic only filters proof fns from file2; the spec fn `lem`
        // remains and the deleted proof fn `lem` shows up as a diff.
        let a = vwrap("proof fn lem(x: nat) ensures x >= 0, { }");
        let b = vwrap("spec fn lem(x: nat) -> bool { x >= 0 }");
        assert_flagged(&a, &b, "proof → spec conversion");
    }

    #[test]
    fn cheat_exec_fn_converted_to_proof_fn() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("proof fn foo(x: u32) -> u32 ensures true, { x }");
        assert_flagged(&a, &b, "exec → proof conversion (loses exec body and creates new proof fn)");
    }

    // ── Rule 5: adding a proof helper IS allowed ───────────────────────

    #[test]
    fn allowed_add_top_level_proof_helper() {
        let a = vwrap(
            "proof fn equiv(x: nat) ensures x >= 0, { }",
        );
        let b = vwrap(
            "proof fn equiv(x: nat) ensures x >= 0, { helper(x); }\n\
             proof fn helper(x: nat) ensures true, { }",
        );
        assert_equal(&a, &b, "model added a helper proof fn");
    }

    #[test]
    fn allowed_add_multiple_proof_helpers() {
        let a = vwrap("proof fn equiv(x: nat) ensures x >= 0, { }");
        let b = vwrap(
            "proof fn equiv(x: nat) ensures x >= 0, { h1(x); h2(x); h3(x); }\n\
             proof fn h1(x: nat) ensures true, { }\n\
             proof fn h2(x: nat) ensures true, { }\n\
             proof fn h3(x: nat) ensures true, { }",
        );
        assert_equal(&a, &b, "model added multiple helper proof fns");
    }

    #[test]
    fn allowed_add_proof_axiom_helper() {
        let a = vwrap("proof fn equiv(x: nat) ensures x >= 0, { }");
        let b = vwrap(
            "proof fn equiv(x: nat) ensures x >= 0, { helper_axiom(x); }\n\
             #[verifier::external_body]\n\
             proof fn helper_axiom(x: nat) ensures true, { }",
        );
        assert_equal(&a, &b, "model added a proof axiom helper");
    }

    #[test]
    fn allowed_add_impl_proof_helper() {
        let a = vwrap(
            "struct S { x: u32 }\n\
             impl S {\n\
                 proof fn lem(&self) ensures self.x >= 0, { }\n\
             }",
        );
        let b = vwrap(
            "struct S { x: u32 }\n\
             impl S {\n\
                 proof fn lem(&self) ensures self.x >= 0, { self.helper(); }\n\
                 proof fn helper(&self) ensures true, { }\n\
             }",
        );
        assert_equal(&a, &b, "model added an impl-method proof helper");
    }

    // ── Rule 4: proof bodies can change freely ─────────────────────────

    #[test]
    fn allowed_proof_fn_body_filled_in() {
        let a = vwrap("proof fn lem(x: nat) ensures x + 0 == x, { }");
        let b = vwrap("proof fn lem(x: nat) ensures x + 0 == x, { assert(x + 0 == x); }");
        assert_equal(&a, &b, "model filled in proof body");
    }

    #[test]
    fn allowed_proof_fn_body_uses_existing_lemma() {
        let a = vwrap(
            "proof fn other(x: nat) ensures true, { }\n\
             proof fn lem(x: nat) ensures x + 0 == x, { }",
        );
        let b = vwrap(
            "proof fn other(x: nat) ensures true, { }\n\
             proof fn lem(x: nat) ensures x + 0 == x, { other(x); assert(x + 0 == x); }",
        );
        assert_equal(&a, &b, "proof body uses an existing lemma");
    }

    #[test]
    fn allowed_assert_in_exec_body() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { assert(x == x); x }");
        assert_equal(&a, &b, "added assert in exec body");
    }

    #[test]
    fn allowed_assume_in_exec_body() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { assume(x > 0); x }");
        assert_equal(&a, &b, "added assume in exec body");
    }

    #[test]
    fn allowed_proof_block_in_exec_body() {
        let a = vwrap("fn foo(x: u32) -> u32 { x }");
        let b = vwrap("fn foo(x: u32) -> u32 { proof { assert(x == x); } x }");
        assert_equal(&a, &b, "added proof { } block in exec body");
    }

    #[test]
    fn allowed_added_loop_invariant() {
        let a = vwrap(
            "fn sum(n: u32) -> u32 {\n\
                let mut i: u32 = 0;\n\
                while i < n decreases n - i { i += 1; }\n\
                i\n\
             }",
        );
        let b = vwrap(
            "fn sum(n: u32) -> u32 {\n\
                let mut i: u32 = 0;\n\
                while i < n invariant i <= n, decreases n - i { i += 1; }\n\
                i\n\
             }",
        );
        assert_equal(&a, &b, "model added loop invariants");
    }

    #[test]
    fn allowed_strengthened_loop_invariant() {
        let a = vwrap(
            "fn sum(n: u32) -> u32 {\n\
                let mut i: u32 = 0;\n\
                while i < n invariant i <= n, decreases n - i { i += 1; }\n\
                i\n\
             }",
        );
        let b = vwrap(
            "fn sum(n: u32) -> u32 {\n\
                let mut i: u32 = 0;\n\
                while i < n invariant i <= n, i >= 0, decreases n - i { i += 1; }\n\
                i\n\
             }",
        );
        assert_equal(&a, &b, "model strengthened loop invariant");
    }

    #[test]
    fn allowed_added_assert_forall_block() {
        let a = vwrap("proof fn lem() ensures true, { }");
        let b = vwrap(
            "proof fn lem() ensures true, {\n\
                assert forall|x: nat| x + 0 == x by { }\n\
             }",
        );
        assert_equal(&a, &b, "added assert forall in proof body");
    }

    // ── Aggregated realistic harness mirroring the bug-report file ─────

    const HARNESS: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn all_gt(s: Seq<i32>, k: i32) -> bool {
        forall|i: int| 0 <= i < s.len() ==> s[i] > k
    }

    spec fn filter_requires(list: Vec<i32>) -> bool {
        all_gt(list@, 10)
    }

    spec fn filter_ensures(list: Vec<i32>, ret: Vec<i32>) -> bool {
        ret@.len() <= list@.len() && all_gt(ret@, 20)
    }

    fn filter_gt_20(list: Vec<i32>) -> (ret: Vec<i32>)
        requires filter_requires(list),
        ensures filter_ensures(list, ret),
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

    proof fn equiv_filter_requires(list: Vec<i32>)
        ensures filter_requires(list) =~= filter_requires(list),
    { }

    proof fn equiv_filter_ensures(list: Vec<i32>, ret: Vec<i32>)
        ensures filter_ensures(list, ret) =~= filter_ensures(list, ret),
    { }

    proof fn equiv_all_gt(s: Seq<i32>, k: i32)
        ensures all_gt(s, k) =~= all_gt(s, k),
    { }
}
"#;

    /// Apply a textual modification to HARNESS and assert it is flagged.
    fn assert_harness_modification_flagged(needle: &str, replacement: &str, msg: &str) {
        let modified = HARNESS.replace(needle, replacement);
        assert_ne!(HARNESS, modified, "test bug: replacement had no effect ({msg})");
        assert_flagged(HARNESS, &modified, msg);
    }

    fn assert_harness_modification_equal(needle: &str, replacement: &str, msg: &str) {
        let modified = HARNESS.replace(needle, replacement);
        assert_ne!(HARNESS, modified, "test bug: replacement had no effect ({msg})");
        assert_equal(HARNESS, &modified, msg);
    }

    #[test]
    fn harness_unchanged_is_equal() {
        assert_equal(HARNESS, HARNESS, "identical files");
    }

    #[test]
    fn harness_proof_body_filled_in_is_equal() {
        // Fill in an existing lemma's proof body.
        let needle = "proof fn equiv_all_gt(s: Seq<i32>, k: i32)\n        ensures all_gt(s, k) =~= all_gt(s, k),\n    { }";
        let replacement = "proof fn equiv_all_gt(s: Seq<i32>, k: i32)\n        ensures all_gt(s, k) =~= all_gt(s, k),\n    {\n        assert(all_gt(s, k) =~= all_gt(s, k));\n    }";
        assert_harness_modification_equal(needle, replacement, "fill in existing proof body");
    }

    #[test]
    fn harness_added_helper_lemma_is_equal() {
        // Add a brand-new proof helper at the bottom of the verus! block.
        let needle = "proof fn equiv_all_gt(s: Seq<i32>, k: i32)\n        ensures all_gt(s, k) =~= all_gt(s, k),\n    { }\n}";
        let replacement = "proof fn equiv_all_gt(s: Seq<i32>, k: i32)\n        ensures all_gt(s, k) =~= all_gt(s, k),\n    { }\n\n    proof fn helper_pushed(s: Seq<i32>, k: i32, x: i32)\n        requires all_gt(s, k), x > k,\n        ensures all_gt(s.push(x), k),\n    { }\n}";
        let modified = HARNESS.replace(needle, replacement);
        assert_ne!(HARNESS, modified, "test bug: replacement had no effect");
        assert_equal(HARNESS, &modified, "added a brand-new proof helper");
    }

    #[test]
    fn harness_loop_invariant_relaxed_is_equal() {
        // Loop invariants are proof scaffolding, free to change.
        assert_harness_modification_equal(
            "invariant i <= list.len(), result@.len() <= i, all_gt(result@, 20),",
            "invariant i <= list.len(), all_gt(result@, 20),",
            "loop invariant change",
        );
    }

    // Forbidden modifications on the harness ─────────────────────────────

    #[test]
    fn harness_spec_fn_body_change_flagged() {
        assert_harness_modification_flagged(
            "fn all_gt(s: Seq<i32>, k: i32) -> bool {\n        forall|i: int| 0 <= i < s.len() ==> s[i] > k\n    }",
            "fn all_gt(s: Seq<i32>, k: i32) -> bool {\n        true\n    }",
            "spec fn body weakened to true",
        );
    }

    #[test]
    fn harness_spec_fn_helper_added_flagged() {
        let modified = HARNESS.replace(
            "spec fn all_gt(s: Seq<i32>, k: i32) -> bool {",
            "spec fn extra_spec(x: nat) -> bool { true }\n\n    spec fn all_gt(s: Seq<i32>, k: i32) -> bool {",
        );
        assert_flagged(HARNESS, &modified, "model added a new spec fn helper (forbidden)");
    }

    #[test]
    fn harness_exec_body_change_flagged() {
        assert_harness_modification_flagged(
            "if x > 20 { result.push(x); }",
            "if x > 30 { result.push(x); }",
            "exec body change",
        );
    }

    #[test]
    fn harness_exec_ensures_weakened_flagged() {
        assert_harness_modification_flagged(
            "ensures filter_ensures(list, ret),",
            "ensures true,",
            "exec ensures weakened",
        );
    }

    #[test]
    fn harness_exec_requires_weakened_flagged() {
        assert_harness_modification_flagged(
            "requires filter_requires(list),",
            "requires true,",
            "exec requires weakened",
        );
    }

    #[test]
    fn harness_proof_ensures_weakened_flagged() {
        // The exact bug pattern from the original report.
        assert_harness_modification_flagged(
            "ensures all_gt(s, k) =~= all_gt(s, k),\n    { }",
            "ensures true,\n    { }",
            "proof fn ensures weakened to true (original bug pattern)",
        );
    }

    #[test]
    fn harness_proof_fn_renamed_flagged() {
        // Rename equiv_all_gt -> equiv_all_gt_v2.
        let modified = HARNESS.replace("equiv_all_gt", "equiv_all_gt_v2");
        assert_flagged(HARNESS, &modified, "renaming an existing proof fn");
    }

    #[test]
    fn harness_proof_fn_deleted_flagged() {
        let needle = "proof fn equiv_all_gt(s: Seq<i32>, k: i32)\n        ensures all_gt(s, k) =~= all_gt(s, k),\n    { }\n";
        let modified = HARNESS.replace(needle, "");
        assert_ne!(HARNESS, modified, "test bug: replacement had no effect");
        assert_flagged(HARNESS, &modified, "model deleted an existing proof fn");
    }

    #[test]
    fn harness_struct_changes_caught() {
        // Struct changes: caught (data layout is part of the spec surface).
        let a = vwrap("struct S { x: u32 }\n    fn f(s: S) -> u32 { s.x }");
        let b = vwrap("struct S { x: u64 }\n    fn f(s: S) -> u64 { s.x }");
        assert_flagged(&a, &b, "struct field type change");
    }

    #[test]
    fn harness_use_statement_change_caught() {
        // Adding/removing a `use` is caught.
        let a = vwrap("fn foo() {}");
        let b = format!(
            "use std::collections::HashMap;\n{}",
            vwrap("fn foo() {}")
        );
        assert_flagged(&a, &b, "added `use` statement");
    }

    // ── Loop-level decreases / loop_ensures: proof-mode constructs ──────
    //
    // The masking pipeline (create_masked_segments.py) blanks all
    // `decreases` and loop-level `ensures` clauses in proof-mode masks and
    // expects the model to fill them back in. For
    // `compare --spec-mode --allow-helpers` to verify those completions
    // without false positives, loop `decreases` and `loop_ensures` must
    // be treated as proof-mode (stripped). A fn-signature `decreases`,
    // however, is part of the spec and MUST still be enforced.

    const LOOP_BASE: &str = r#"
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
    fn allowed_model_fills_in_loop_decreases() {
        // Input has a placeholder (no decreases); model fills it in.
        let masked = LOOP_BASE.replace("            decreases n - i,\n", "");
        assert_equal(&masked, LOOP_BASE, "model added a loop decreases (proof-mode artifact)");
    }

    #[test]
    fn allowed_model_changes_loop_decreases_expression() {
        let modified = LOOP_BASE.replace("decreases n - i,", "decreases (n - i) as int,");
        assert_equal(LOOP_BASE, &modified, "model picked a different termination measure");
    }

    #[test]
    fn allowed_model_fills_in_loop_ensures() {
        // Loop-level ensures (loop_ensures) is a proof-mode artifact.
        let masked = LOOP_BASE.replace("            ensures\n                i == n,\n", "");
        assert_equal(&masked, LOOP_BASE, "model added a loop_ensures clause");
    }

    #[test]
    fn allowed_model_changes_loop_ensures() {
        let modified = LOOP_BASE.replace("ensures\n                i == n,", "ensures\n                i >= n,");
        assert_equal(LOOP_BASE, &modified, "model strengthened loop_ensures");
    }

    #[test]
    fn allowed_loop_invariant_change_via_spec_mode_allow_helpers() {
        // Sanity: loop invariants are also proof-mode.
        let modified = LOOP_BASE.replace("invariant\n                i <= n,", "invariant\n                i <= n, true,");
        assert_equal(LOOP_BASE, &modified, "model added a loop invariant");
    }

    const RECURSIVE_BASE: &str = r#"
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
    fn allowed_fn_sig_decreases_removed() {
        // Unified rule: signature `decreases` is termination scaffolding,
        // not part of the spec for `compare --spec-mode --allow-helpers`.
        // The masker blanks it per-mode, so the verifier must accept it.
        let modified = RECURSIVE_BASE.replace("        decreases n,\n", "");
        assert_equal(RECURSIVE_BASE, &modified, "removing fn-sig decreases is allowed");
    }

    #[test]
    fn allowed_fn_sig_decreases_changed() {
        let modified =
            RECURSIVE_BASE.replace("        decreases n,\n", "        decreases 0nat,\n");
        assert_equal(RECURSIVE_BASE, &modified, "changing fn-sig decreases is allowed");
    }

    #[test]
    fn cheat_fn_sig_ensures_unchanged_by_loop_changes() {
        // Confirm fn-sig ensures is still enforced even though loop_ensures is not.
        let modified = LOOP_BASE.replace("ensures r == n,", "ensures true,");
        assert_flagged(LOOP_BASE, &modified, "weakened fn-sig ensures (not a loop_ensures)");
    }

    // End-to-end with the masking-pipeline pattern: a single file with a
    // recursive fn (sig decreases — must be enforced) AND a loop with
    // decreases+ensures (must be free for the model to fill in).
    const MIXED_BASE: &str = r#"
use vstd::prelude::*;
fn main() {}
verus! {
    spec fn fact(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 1 } else { n * fact((n - 1) as nat) }
    }

    fn count_up(n: u64) -> (r: u64)
        ensures r == n,
    {
        let mut i: u64 = 0;
        while i < n
            invariant i <= n,
            ensures i == n,
            decreases n - i,
        {
            i = i + 1;
        }
        i
    }
}
"#;

    #[test]
    fn allowed_mixed_loop_proof_artifacts_filled_in() {
        // Simulate the proof-mode mask: blank loop decreases + loop_ensures
        // + invariants. The model fills them all back in.
        let masked = MIXED_BASE
            .replace("            invariant i <= n,\n", "")
            .replace("            ensures i == n,\n", "")
            .replace("            decreases n - i,\n", "");
        assert_equal(&masked, MIXED_BASE, "mixed: loop proof artifacts filled in");
    }

    #[test]
    fn allowed_mixed_fn_sig_decreases_removed() {
        // In the same mixed file, removing fn-sig decreases on the
        // recursive spec_fn is also allowed under the unified rule.
        let modified = MIXED_BASE.replace("        decreases n,\n", "");
        assert_equal(MIXED_BASE, &modified, "mixed: removing recursive fn-sig decreases is allowed");
    }
}
