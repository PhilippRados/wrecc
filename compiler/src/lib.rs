mod codegen;
mod common;
mod parser;
mod scanner;
mod typechecker;

// All necessary modules used for preprocessor
pub use common::error::*;
pub use parser::*;
pub use scanner::*;

use codegen::{codegen::*, register_allocation::*};
use typechecker::*;

pub fn compile(filename: &str, source: &str) -> Result<String, Vec<Error>> {
    // Scan input
    let tokens = Scanner::new(filename, source).scan_token()?;

    // Parse statements and return Abstract Syntax Tree
    let (mut statements, env) = Parser::new(tokens).parse()?;

    // Check for semantic errors
    let (const_labels, env, switches) = TypeChecker::new(env).check(&mut statements)?;

    // Turn AST into IR
    let (ir, live_intervals, env) =
        Compiler::new(const_labels, env, switches).translate(statements);

    // Fill in physical registers
    let ir = RegisterAllocation::new(env, live_intervals).generate(ir);

    let output = ir
        .into_iter()
        .map(|instr| instr.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
