mod codegen;
mod common;
mod parser;
mod scanner;
mod typechecker;

use codegen::{codegen::*, register_allocation::*};
pub use common::error::*;
use parser::*;
use scanner::*;
use typechecker::*;

pub fn compile(source: String) -> Result<String, Vec<Error>> {
    // Scan input
    let tokens = Scanner::new(&source).scan_token()?;

    // Parse statements
    let (mut statements, env) = Parser::new(tokens).parse()?;

    // Check for errors
    let typechecker = TypeChecker::new(env);
    let (const_labels, env, switches) = typechecker.check(&mut statements)?;

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
