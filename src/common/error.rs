use crate::common::token::Token;
use crate::scanner::Scanner;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Error {
    Indicator, // just to signal an error occured
    Regular(ErrorData),
}

impl Error {
    pub fn print_error(&self) {
        match self {
            Error::Regular(e) => e.print_error(),
            _ => (),
        }
    }
    pub fn new(t: &Token, msg: &str) -> Self {
        Error::Regular(ErrorData::new(t, msg))
    }

    pub fn new_scan_error(scanner: &Scanner, msg: &str) -> Self {
        Error::Regular(ErrorData::new_scan_error(scanner, msg))
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ErrorData {
    pub line_index: i32,
    pub line_string: String,
    pub column: i32,
    pub msg: String,
}
impl ErrorData {
    pub fn new(t: &Token, msg: &str) -> Self {
        ErrorData {
            line_index: t.line_index,
            line_string: t.line_string.clone(),
            column: t.column,
            msg: msg.to_string(),
        }
    }
    pub fn new_scan_error(scanner: &Scanner, msg: &str) -> Self {
        ErrorData {
            line_index: scanner.line,
            line_string: scanner.raw_source[(scanner.line - 1) as usize].clone(),
            column: scanner.column,
            msg: msg.to_string(),
        }
    }
    pub fn print_error(&self) {
        eprintln!("Error: {}", self.msg);

        if self.line_index != -1 {
            let line_length = self.line_index.to_string().len();

            eprintln!("|");
            eprintln!("{} {}", self.line_index, self.line_string);
            eprint!("|");
            for _ in 1..self.column as usize + line_length {
                eprint!(" ");
            }
            eprintln!("^");
        }
    }
    pub fn missing_entrypoint() -> Self {
        ErrorData {
            line_index: -1,
            msg: "Can't find main() entrypoint to program.".to_string(),
            line_string: "".to_string(),
            column: -1,
        }
    }

    pub fn sys_exit(msg: &str, exit_code: i32) -> ! {
        eprintln!("rucc: {msg}");
        std::process::exit(exit_code);
    }
}
