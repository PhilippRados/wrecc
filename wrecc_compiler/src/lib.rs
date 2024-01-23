pub mod compiler;
pub mod preprocessor;

use compiler::{
    codegen::register_allocation::*, codegen::*, common::error::*, parser::*, scanner::*,
    typechecker::*,
};
use preprocessor::{scanner::Scanner as PPScanner, *};

use std::path::Path;

// Preprocesses given input file
pub fn preprocess(filename: &Path, source: String) -> Result<Vec<PPToken>, Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();

    Preprocessor::new(filename, tokens, None)
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
    let (declarations, const_labels, switches) = TypeChecker::new().check(parse_tree)?;

    // turn AST into LIR
    let (ir, live_intervals) = Compiler::new(const_labels, switches).translate(declarations);

    // fill in physical registers
    let asm = RegisterAllocation::new(live_intervals).generate(ir);

    let output = asm
        .into_iter()
        .map(|instr| instr.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
