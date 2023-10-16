mod common;
mod scanner;
mod typechecker;
mod wrecc_codegen;
mod wrecc_parser;

// All necessary modules used for preprocessor
pub use common::error::*;
pub use scanner::*;
pub use wrecc_parser::{double_peek::*, parser::*};

use std::path::Path;
use typechecker::*;
use wrecc_codegen::{codegen::*, register_allocation::*};

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
