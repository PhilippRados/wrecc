use std::fs;

mod codegen;
mod common;
mod parser;
mod scanner;
mod typechecker;

use codegen::{codegen::*, register_allocation::*};
use common::error::*;
use parser::*;
use scanner::*;
use typechecker::*;

fn main() {
    // Read input file
    let args: Vec<String> = std::env::args().collect();
    let file = match args.len() {
        2 => &args[1],
        _ => ErrorData::sys_exit("Usage: rucc <file>", 22),
    };

    let source = fs::read_to_string(file)
        .unwrap_or_else(|_| ErrorData::sys_exit(&format!("Couldn't find file: '{}'", file), 2));

    // Scan input
    let tokens = match Scanner::new(&source).scan_token() {
        Ok(v) => v,
        Err(e) => {
            for err in e {
                err.print_error();
            }
            return;
        }
    };

    // Parse statements
    let (mut statements, env) = match Parser::new(tokens).parse() {
        Some(s) => s,
        None => return,
    };

    // Check for errors
    let typechecker = TypeChecker::new(env);
    let (const_labels, env, switches) = match typechecker.check(&mut statements) {
        Some(result) => result,
        None => return,
    };

    // Turn AST into IR
    let (ir, live_intervals, env) =
        Compiler::new(const_labels, env, switches).translate(&statements);

    // Fill in physical registers
    let ir = RegisterAllocation::new(env, live_intervals).generate(ir);

    // Generate x8664 assembly
    use std::io::Write;
    let mut output =
        std::fs::File::create("/Users/philipprados/documents/coding/Rust/rucc/generated.s")
            .expect("create failed");

    for instr in ir {
        writeln!(output, "{}", instr).expect("write failed");
    }
}
