use std::fs;

mod scanner;
use scanner::Tokens;
use scanner::*;
mod parser;
use parser::Parser;
mod interpreter;
use interpreter::interpret;
use interpreter::Stmt;

fn sys_error(msg: &str, exit_code: i32) {
    eprintln!("rucc: {msg}");
    std::process::exit(exit_code);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut file: Option<&str> = None;
    match args.len() {
        2 => file = Some(&args[1]),
        _ => sys_error("usage: rucc <file>", 2),
    }
    let source = fs::read_to_string(file.unwrap()).expect("couldn't find file: {file}");

    let mut tokens: Option<Vec<Tokens>> = None;
    let mut scanner = Scanner::new(&source);
    match scanner.scan_token() {
        Ok(v) => tokens = Some(v),
        Err(e) => {
            for err in e {
                err.print_error();
            }
            return;
        }
    }
    dbg!(&tokens);

    let mut statements: Option<Vec<Stmt>> = None;
    let mut parser = Parser::new(tokens.unwrap());
    match parser.parse() {
        Some(v) => statements = Some(v),
        None => return,
    }

    interpret(statements.unwrap());
}
