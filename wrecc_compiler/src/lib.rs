pub mod compiler;
pub mod preprocessor;

use compiler::{
    common::error::*, scanner::*, typechecker::*, wrecc_codegen::codegen::*,
    wrecc_codegen::register_allocation::*, wrecc_parser::parser::*,
};
use preprocessor::{preprocessor::*, scanner::Scanner as PPScanner};

use std::path::Path;

// Preprocesses given input file
pub fn preprocess(filename: &Path, source: String) -> Result<Vec<PPToken>, Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();

    Preprocessor::new(filename, tokens, None)
        .start()
        .map(|(tokens, _)| tokens)
}

pub fn compile(source: Vec<PPToken>, dump_ast: bool) -> Result<String, Vec<Error>> {
    // Scan input
    let tokens = Scanner::new(source).scan_token()?;

    // Parse statements and return Abstract Syntax Tree
    let mut declarations = Parser::new(tokens).parse()?;

    if dump_ast {
        declarations.iter().for_each(|decl| eprintln!("{}", decl));
    }

    // Check for semantic errors
    let (const_labels, switches) = TypeChecker::new().check(&mut declarations)?;

    // Turn AST into IR
    let (ir, live_intervals) = Compiler::new(const_labels, switches).translate(declarations);

    // Fill in physical registers
    let asm = RegisterAllocation::new(live_intervals).generate(ir);

    let output = asm
        .into_iter()
        .map(|instr| instr.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
