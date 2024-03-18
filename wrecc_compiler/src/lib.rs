pub mod compiler;
pub mod preprocessor;

use compiler::{
    codegen::register_allocation::*, codegen::*, common::error::*, parser::*, scanner::*, typechecker::*,
};
use preprocessor::{scanner::Scanner as PPScanner, *};

use std::path::Path;
use std::path::PathBuf;

// Preprocesses given input file
pub fn preprocess(
    filename: &Path,
    user_include_dirs: &Vec<PathBuf>,
    source: String,
) -> Result<Vec<PPToken>, Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();
    let include_depth = 0;

    Preprocessor::new(filename, tokens, None, user_include_dirs.clone(), include_depth)
        .start()
        .map(|(tokens, _)| tokens)
}

pub fn compile(source: Vec<PPToken>, dump_ast: bool) -> Result<String, Vec<Error>> {
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
