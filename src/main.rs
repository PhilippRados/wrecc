use std::fs;

mod environment;
mod error;
mod interpreter;
mod parser;
mod scanner;
mod token;
mod typechecker;
mod types;
use interpreter::*;
use parser::Parser;
use scanner::*;
use typechecker::TypeChecker;

fn sys_error(msg: &str, exit_code: i32) -> ! {
    eprintln!("rucc: {msg}");
    std::process::exit(exit_code);
}

fn main() {
    // read input file
    let args: Vec<String> = std::env::args().collect();
    let file = match args.len() {
        2 => &args[1],
        _ => sys_error("usage: rucc <file>", 2),
    };

    let source = fs::read_to_string(file).expect(&format!("couldn't find file: {}", file));

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
    let statements = match Parser::new(tokens).parse() {
        Some(s) => s,
        None => return,
    };

    // Check for errors
    if let Err(e) = TypeChecker::new().check(&statements) {
        for err in e {
            err.print_error();
        }
        return;
    }

    // Interpret
    Interpreter::new().interpret(&statements);
}
