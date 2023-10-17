pub mod compiler;
pub mod preprocessor;

use compiler::{
    common::error::*, scanner::*, typechecker::*, wrecc_codegen::codegen::*,
    wrecc_codegen::register_allocation::*, wrecc_parser::parser::*,
};
use preprocessor::{preprocessor::Preprocessor, scanner::Scanner as PPScanner};

use std::path::Path;

// Preprocesses given input file
pub fn preprocess(filename: &Path, source: &str) -> Result<String, Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens, None)
        .start()
        .map(|(source, _)| source)
}

pub fn compile(filename: &Path, source: &str, dump_ast: bool) -> Result<String, Vec<Error>> {
    // Scan input
    let tokens = Scanner::new(filename, source).scan_token()?;

    // Parse statements and return Abstract Syntax Tree and symbol table
    let (mut statements, env) = Parser::new(tokens).parse()?;

    if dump_ast {
        statements.iter().for_each(|s| eprintln!("{}", s));
    }

    // Check for semantic errors
    let (const_labels, env, switches) = TypeChecker::new(env).check(&mut statements)?;

    // Turn AST into IR
    let (ir, live_intervals, env) =
        Compiler::new(const_labels, env, switches).translate(statements);

    // Fill in physical registers
    let asm = RegisterAllocation::new(env, live_intervals).generate(ir);

    let output = asm
        .into_iter()
        .map(|instr| instr.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
