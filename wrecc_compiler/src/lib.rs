pub mod compiler;
pub mod preprocessor;

use compiler::{
    codegen::register_allocation::*, codegen::*, common::error::*, parser::*, scanner::*, typechecker::*,
};
use preprocessor::{scanner::Scanner as PPScanner, *};

use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;

// helper function to embed headers into binary
macro_rules! include_header {
    ($filename:expr) => {
        (
            PathBuf::from($filename),
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../include/",
                $filename
            )),
        )
    };
}

// Preprocesses given input file
pub fn preprocess(
    filename: &Path,
    user_include_dirs: &Vec<PathBuf>,
    defines: &Vec<(String, String)>,
    source: String,
) -> Result<Vec<PPToken>, WreccError> {
    let tokens = PPScanner::new(source).scan_token();
    let include_depth = 0;

    let standard_headers: HashMap<PathBuf, &'static str> = HashMap::from([
        include_header!("ctype.h"),
        include_header!("errno.h"),
        include_header!("fcntl.h"),
        include_header!("limits.h"),
        include_header!("stddef.h"),
        include_header!("stdio.h"),
        include_header!("stdlib.h"),
        include_header!("string.h"),
        include_header!("time.h"),
        include_header!("unistd.h"),
    ]);

    // INFO: convert all cli-passed defines to #defines as if they were in regular source file
    // to properly error check them
    let mut dummy_defines = String::new();
    for (macro_name, value) in defines {
        dummy_defines.push_str(&format!("#define {} {}\n", macro_name, value));
    }
    let (_, defines) = Preprocessor::new(
        &PathBuf::from("command-line-argument"),
        PPScanner::new(dummy_defines).scan_token(),
        HashMap::new(),
        user_include_dirs,
        &standard_headers,
        include_depth,
    )
    .start()
    .map_err(|errors| WreccError::Cli(errors.iter().map(|e| e.kind.message()).collect()))?;

    Ok(Preprocessor::new(
        filename,
        tokens,
        defines,
        user_include_dirs,
        &standard_headers,
        include_depth,
    )
    .start()
    .map(|(tokens, _)| tokens)?)
}

pub fn compile(source: Vec<PPToken>, dump_ast: bool) -> Result<String, WreccError> {
    // scan input
    let tokens = Scanner::new(source).scan_token()?;

    // parse tokens and return parse-tree
    let parse_tree = Parser::new(tokens).parse()?;

    if dump_ast {
        parse_tree.iter().for_each(|decl| eprintln!("{}", decl));
    }

    // check for semantic errors and annotate parse-tree returning new ast
    let (mir, const_labels) = TypeChecker::new().check(parse_tree)?;

    // turn AST into LIR
    let (lir, live_intervals) = Compiler::new(const_labels).translate(mir);

    // fill in physical registers
    let asm = RegisterAllocation::new(live_intervals).generate(lir);

    let output = asm
        .into_iter()
        .map(|instr| instr.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
