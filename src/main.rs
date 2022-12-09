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
        _ => Error::sys_exit("usage: rucc <file>", 22),
    };

    let source = fs::read_to_string(file)
        .unwrap_or_else(|_| Error::sys_exit(&format!("couldn't find file: '{}'", file), 2));

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
    let mut statements = match Parser::new(tokens).parse() {
        Some(s) => s,
        None => return,
    };

    // dbg!(&statements);

    // Check for errors
    let mut typechecker = TypeChecker::new();
    let (func_stack, const_labels) = match typechecker.check(&mut statements) {
        Ok(func_stack) => func_stack,
        Err(e) => {
            for err in e {
                err.print_error();
            }
            return;
        }
    };

    // generate x8664 assembly
    Compiler::new(func_stack, const_labels).compile(&statements);
}
