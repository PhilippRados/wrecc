use std::fs;

mod codegen;
mod common;
mod parser;
mod scanner;
mod typechecker;

use codegen::codegen::*;
use common::error::*;
use parser::*;
use scanner::*;
use typechecker::*;

fn main() {
    // read input file
    let args: Vec<String> = std::env::args().collect();
    let file = match args.len() {
        2 => &args[1],
        _ => ErrorData::sys_exit("usage: rucc <file>", 22),
    };

    let source = fs::read_to_string(file)
        .unwrap_or_else(|_| ErrorData::sys_exit(&format!("couldn't find file: '{}'", file), 2));

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
    let (func_stack, const_labels, env) = match typechecker.check(&mut statements) {
        Some(result) => result,
        None => return,
    };

    // generate x8664 assembly
    Compiler::new(func_stack, const_labels, env).compile(&statements);
}
