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
    #[clap(long, help = "Compare requires")]
    requires: bool,
    #[clap(long, help = "Compare ensures")]
    ensures: bool,
    #[clap(long, help = "Compare recommends")]
    recommends: bool,
    #[clap(long, help = "Compare invariants (sig-level and loop invariants)")]
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
    #[clap(long, help = "Compare decreases")]
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
        mode.decreases = true;
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
            if args.verbose {
                println!("{}", fprint_file(&result1, Formatter::VerusFmt));
                println!("{}", fprint_file(&result2, Formatter::VerusFmt));
            }
            Ok(result1 == result2)
        })
    })
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
}
