use std::collections::HashMap;
use std::fs;

#[derive(Debug, PartialEq, Clone)]
#[allow(dead_code)]
enum Tokens {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Comma,
    Dot,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Plus,
    PlusPlus,
    Minus,
    MinusMinus,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Amp,
    AmpAmp,
    PipePipe,

    // Literals.
    Ident(String),
    String(String),
    CharLit(char),
    Number(i32),

    // Keywords.
    Int,
    Char,
    Else,
    False,
    For,
    If,
    Null,
    Return,
    While,

    Eof,
}

macro_rules! hash {
    ($($key_val:expr),+) => {{
        let mut h = HashMap::new();
        $(h.insert($key_val.0,$key_val.1);)+
        h
    }}
}

struct Scanner<'a> {
    source: &'a str,
    line: i32,
    current: i32,
    start: i32,
    keywords: HashMap<String, Tokens>,
    err: bool,
}
impl<'a> Scanner<'a> {
    fn new(source: &'a str) -> Self {
        Scanner {
            source,
            line: 1,
            current: 0,
            start: 0,
            err: false,
            keywords: hash![
                ("int".to_string(), Tokens::Int),
                ("char".to_string(), Tokens::Char),
                ("if".to_string(), Tokens::If),
                ("else".to_string(), Tokens::Else),
                ("for".to_string(), Tokens::For),
                ("while".to_string(), Tokens::While),
                ("null".to_string(), Tokens::Null),
                ("return".to_string(), Tokens::Return)
            ],
        }
    }

    fn scan_token(&mut self) -> Result<Vec<Tokens>, Vec<ScanErr>> {
        let mut errors: Vec<ScanErr> = Vec::new();
        let mut tokens: Vec<Tokens> = Vec::new();
        let source_len = self.source.len() as i32;

        while self.current < source_len {
            self.start = self.current;
            let c = self.advance();
            match c {
                '(' => tokens.push(Tokens::LeftParen),
                ')' => tokens.push(Tokens::RightParen),
                '{' => tokens.push(Tokens::LeftBrace),
                '}' => tokens.push(Tokens::RightBrace),
                ',' => tokens.push(Tokens::Comma),
                '.' => tokens.push(Tokens::Dot),
                '-' => tokens.push(Tokens::Minus),
                '+' => tokens.push(Tokens::Plus),
                ';' => tokens.push(Tokens::Semicolon),
                '*' => tokens.push(Tokens::Star),

                '!' => tokens.push(self.match_next('=', Tokens::BangEqual, Tokens::Bang)),
                '=' => tokens.push(self.match_next('=', Tokens::EqualEqual, Tokens::Equal)),
                '<' => tokens.push(self.match_next('=', Tokens::LessEqual, Tokens::Less)),
                '>' => tokens.push(self.match_next('=', Tokens::GreaterEqual, Tokens::Greater)),

                '/' => {
                    if self.matches('/') {
                        while self.peek() != '\n' && !self.is_at_end() {
                            self.advance();
                        }
                    } else {
                        tokens.push(Tokens::Slash)
                    }
                }
                ' ' => (),
                '\r' => (),
                '\t' => (),
                '\n' => self.line += 1,

                '"' => match self.string() {
                    Ok(string) => tokens.push(Tokens::String(string)),
                    Err(e) => {
                        self.err = true;
                        errors.push(e)
                    }
                },

                _ => {
                    if c.is_ascii_digit() {
                        while self.peek().is_ascii_digit() {
                            self.advance();
                        }
                        let num = self
                            .source
                            .get(self.start as usize..self.current as usize)
                            .unwrap()
                            .parse::<i32>()
                            .unwrap();
                        tokens.push(Tokens::Number(num))
                    } else if c.is_alphabetic() || c == '_' {
                        while self.peek().is_alphabetic() || self.peek() == '_' {
                            self.advance();
                        }
                        let value = self
                            .source
                            .get(self.start as usize..self.current as usize)
                            .unwrap();
                        if self.keywords.contains_key(value) {
                            tokens.push(self.keywords.get(value).unwrap().clone());
                        } else {
                            tokens.push(Tokens::Ident(value.to_string()))
                        }
                    } else {
                        self.err = true;
                        errors.push(ScanErr {
                            line: self.line,
                            msg: format!("Unexpected character: {c}").to_string(),
                        });
                    }
                }
            }
        }
        match self.err {
            true => Err(errors),
            false => Ok(tokens),
        }
    }

    fn advance(&mut self) -> char {
        let result = self.at();
        self.current += 1;

        result
    }
    fn is_at_end(&self) -> bool {
        if self.current >= self.source.len() as i32 {
            true
        } else {
            false
        }
    }
    fn at(&self) -> char {
        self.source
            .chars()
            .nth(self.current as usize)
            .expect("valid ascii in source-code")
    }
    fn matches(&mut self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        };
        if self.at() != expected {
            return false;
        };

        self.current += 1;
        true
    }
    fn match_next(&mut self, expected: char, valid: Tokens, invalid: Tokens) -> Tokens {
        if self.matches(expected) {
            valid
        } else {
            invalid
        }
    }
    fn peek(&self) -> char {
        if self.is_at_end() {
            return '\0';
        };
        self.at()
    }

    fn string(&mut self) -> Result<String, ScanErr> {
        while self.peek() != '"' && !self.is_at_end() {
            if self.peek() == '\n' {
                self.line += 1;
            }
            self.advance();
        }
        if self.is_at_end() {
            return Err(ScanErr {
                line: self.line,
                msg: "Unterminated string".to_string(),
            });
        }
        self.advance();

        Ok(self
            .source
            .get(self.start as usize + 1..self.current as usize - 1)
            .expect("substring doesnt exist")
            .to_string())
    }
}

#[derive(Debug, Eq, PartialEq)]
struct ScanErr {
    line: i32,
    msg: String,
}

impl ScanErr {
    fn print_error(&self, pos: &str) {
        eprintln!("[line {} ] Error {pos}: {}", self.line, self.msg);
    }
}

fn sys_error(msg: &str, exit_code: i32) {
    eprintln!("rucc: {msg}");
    std::process::exit(exit_code);
}

fn main() {
    let mut had_error = false;
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
                err.print_error("");
            }
            // e.iter().map(|err| err.print_error(""));
            // .collect::<Vec<ScanErr>>();
            had_error = true;
        }
    }
    println!("{:?}", tokens);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_single_and_double_tokens() {
        let source = "!= = > == \n\n    ;";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::BangEqual,
            Tokens::Equal,
            Tokens::Greater,
            Tokens::EqualEqual,
            Tokens::Semicolon,
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn ignores_comments() {
        let source = "// this is a    comment\n\n!this";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![Tokens::Bang, Tokens::Ident("this".to_string())];
        assert_eq!(result, expected);
    }
    #[test]
    fn token_basic_math_expression() {
        let source = "3 + 1 / 4";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::Number(3),
            Tokens::Plus,
            Tokens::Number(1),
            Tokens::Slash,
            Tokens::Number(4),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn basic_math_double_digit_nums() {
        let source = "300 - 11 * 41";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::Number(300),
            Tokens::Minus,
            Tokens::Number(11),
            Tokens::Star,
            Tokens::Number(41),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn matches_keywords_and_strings() {
        let source = "int some = \"this is a string\"";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::Int,
            Tokens::Ident("some".to_string()),
            Tokens::Equal,
            Tokens::String("this is a string".to_string()),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn errors_on_unterminated_string() {
        let source = "int some = \"this is a string";
        let mut scanner = Scanner::new(&source);

        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![ScanErr {
            line: 1,
            msg: "Unterminated string".to_string(),
        }];
        assert_eq!(result, expected);
    }
    #[test]
    fn matches_complex_keywords() {
        let source = "int some_long;\nwhile (val >= 12) {*p = val}";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::Int,
            Tokens::Ident("some_long".to_string()),
            Tokens::Semicolon,
            Tokens::While,
            Tokens::LeftParen,
            Tokens::Ident("val".to_string()),
            Tokens::GreaterEqual,
            Tokens::Number(12),
            Tokens::RightParen,
            Tokens::LeftBrace,
            Tokens::Star,
            Tokens::Ident("p".to_string()),
            Tokens::Equal,
            Tokens::Ident("val".to_string()),
            Tokens::RightBrace,
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn detects_single_on_invalid_char() {
        let source = "int c = 0$";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![ScanErr {
            line: 1,
            msg: "Unexpected character: $".to_string(),
        }];
        assert_eq!(result, expected);
    }
    #[test]
    fn detects_mutliple_on_invalid_chars() {
        let source = "int c = 0$\n\n% ^";
        let mut scanner = Scanner::new(&source);
        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![
            ScanErr {
                line: 1,
                msg: "Unexpected character: $".to_string(),
            },
            ScanErr {
                line: 3,
                msg: "Unexpected character: %".to_string(),
            },
            ScanErr {
                line: 3,
                msg: "Unexpected character: ^".to_string(),
            },
        ];
        assert_eq!(result, expected);
    }
}
