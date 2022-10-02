use crate::scanner::Scanner;
use crate::token::Token;

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Error {
    pub line_index: i32,
    pub line_string: String,
    pub column: i32,
    pub msg: String,
}

impl Error {
    pub fn new(t: &Token, msg: &str) -> Self {
        Error {
            line_index: t.line_index,
            line_string: t.line_string.clone(),
            column: t.column,
            msg: msg.to_string(),
        }
    }
    pub fn new_scan_error(scanner: &Scanner, msg: &str) -> Self {
        Error {
            line_index: scanner.line,
            line_string: scanner.raw_source[(scanner.line - 1) as usize].clone(),
            column: scanner.column,
            msg: msg.to_string(),
        }
    }
    pub fn print_error(&self) {
        eprintln!("Error: {}", self.msg);

        // Change to Option<>
        if self.line_index != -1 {
            eprintln!("|");
            eprintln!("{} {}", self.line_index, self.line_string);
            eprint!("|");
            for _ in 0..self.column {
                eprint!(" ");
            }
            eprintln!("^");
        }
    }
    pub fn print_exit(&self) -> ! {
        self.print_error();
        std::process::exit(-1);
    }
}
