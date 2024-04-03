//! Wreccs library-crate which makes up the actual compiler without side-effects

pub mod compiler;
pub mod preprocessor;

use compiler::{
    codegen::register_allocation::*, codegen::*, common::error::*, parser::*, scanner::*, typechecker::*,
};
use preprocessor::{scanner::Scanner as PPScanner, *};

use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;

/// Preprocesses given input file by converting String into preprocessor-tokens.<br>
pub fn preprocess(
    filename: &Path,
    user_include_dirs: &Vec<PathBuf>,
    defines: &Vec<(String, String)>,
    standard_headers: HashMap<PathBuf, &'static str>,
    source: String,
) -> Result<Vec<PPToken>, WreccError> {
    let tokens = PPScanner::new(source).scan_token();
    let include_depth = 0;

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

/// Compiles preprocessor-tokens to a x86-64 string, using functionality defined in [compiler]
pub fn compile(source: Vec<PPToken>, dump_ast: bool) -> Result<String, WreccError> {
    let tokens = Scanner::new(source).scan_token()?;

    let parse_tree = Parser::new(tokens).parse()?;

    if dump_ast {
        parse_tree.iter().for_each(|decl| eprintln!("{}", decl));
    }

    let (mir, const_labels) = TypeChecker::new().check(parse_tree)?;

    let (lir, live_intervals) = Compiler::new(const_labels).translate(mir);

    let asm = RegisterAllocation::new(live_intervals).generate(lir);

    let output = asm
        .into_iter()
        .map(|instr| instr.as_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
