use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, PartialEq, Clone)]
#[allow(dead_code)]
pub enum Tokens {
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

#[derive(Debug, Eq, PartialEq)]
pub struct ScanErr {
    line: i32,
    msg: String,
}

impl ScanErr {
    pub fn print_error(&self, pos: &str) {
        eprintln!("[line {} ] Error {pos}: {}", self.line, self.msg);
    }
}

pub struct Scanner<'a> {
    source: Peekable<Chars<'a>>,
    line: i32,
    keywords: HashMap<String, Tokens>,
    err: bool,
}
impl<'a> Scanner<'a> {
    pub fn new(source: Peekable<Chars<'a>>) -> Self {
        Scanner {
            source,
            line: 1,
            err: false,
            keywords: hash![
                ("int".to_string(), Tokens::Int),
                ("char".to_string(), Tokens::Char),
                ("if".to_string(), Tokens::If),
                ("else".to_string(), Tokens::Else),
                ("for".to_string(), Tokens::For),
                ("while".to_string(), Tokens::While),
                ("return".to_string(), Tokens::Return)
            ],
        }
    }

    fn match_next(&mut self, expected: char, if_match: Tokens, if_not: Tokens) -> Tokens {
        match self.source.next_if_eq(&expected) {
            Some(_v) => if_match,
            None => if_not,
        }
    }

    pub fn scan_token(&mut self) -> Result<Vec<Tokens>, Vec<ScanErr>> {
        let mut errors: Vec<ScanErr> = Vec::new();
        let mut tokens: Vec<Tokens> = Vec::new();

        while let Some(c) = self.source.next() {
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
                        let _: String = self
                            .source
                            .by_ref()
                            .take_while(|c| *c != '\n' && *c != '\0')
                            .collect::<String>(); // there has to be a better way to consume the iter
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
                        // Number
                        let mut num = String::new();
                        // have to prepend already consumned char
                        num.push(c);

                        while let Some(digit) = self.source.by_ref().next_if(|c| c.is_digit(10)) {
                            num.push(digit);
                        }
                        tokens.push(Tokens::Number(num.parse::<i32>().unwrap()));
                    } else if c.is_alphabetic() || c == '_' {
                        // Identifier
                        let mut value = String::new();
                        value.push(c);
                        while let Some(v) = self
                            .source
                            .by_ref()
                            .next_if(|c| c.is_alphabetic() || *c == '_')
                        {
                            value.push(v);
                        }
                        if self.keywords.contains_key(&value) {
                            tokens.push(self.keywords.get(&value).unwrap().clone());
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

    fn matches(&mut self, expected: char) -> bool {
        match self.source.peek() {
            Some(v) => {
                if *v != expected {
                    return false;
                }
            }
            None => return false,
        }
        self.source.next();
        true
    }

    fn string(&mut self) -> Result<String, ScanErr> {
        let mut last_char = '\0';
        let result = self
            .source
            .by_ref()
            .take_while(|c| {
                last_char = *c;
                *c != '"'
            })
            .collect::<String>();
        if last_char != '"' {
            return Err(ScanErr {
                line: self.line,
                msg: "Unterminated string".to_string(),
            });
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_single_and_double_tokens() {
        let source = "!= = > == \n\n    ;".chars().peekable();
        let mut scanner = Scanner::new(source);
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
        let source = "// this is a    comment\n\n!this".chars().peekable();
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![Tokens::Bang, Tokens::Ident("this".to_string())];
        assert_eq!(result, expected);
    }
    #[test]
    fn token_basic_math_expression() {
        let source = "3 + 1 / 4".chars().peekable();
        let mut scanner = Scanner::new(source);
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
        let source = "300 - 11 * 41".chars().peekable();
        let mut scanner = Scanner::new(source);
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
        let source = "int some = \"this is a string\"".chars().peekable();
        let mut scanner = Scanner::new(source);
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
        let source = "int some = \"this is a string".chars().peekable();
        let mut scanner = Scanner::new(source);

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
        let source = "int some_long;\nwhile (val >= 12) {*p = val}"
            .chars()
            .peekable();
        let mut scanner = Scanner::new(source);
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
        let source = "int c = 0$".chars().peekable();
        let mut scanner = Scanner::new(source);
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
        let source = "int c = 0$\n\n% ^".chars().peekable();
        let mut scanner = Scanner::new(source);
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
    #[test]
    fn can_handle_non_ascii_alphabet() {
        let source = "\nint ä = 123".chars().peekable();
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!(),
        };
        let expected = vec![
            Tokens::Int,
            Tokens::Ident("ä".to_string()),
            Tokens::Equal,
            Tokens::Number(123),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn errors_on_non_ascii_non_letters() {
        let source = "\nint ä ~ = 123".chars().peekable();
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![ScanErr {
            line: 2,
            msg: "Unexpected character: ~".to_string(),
        }];
        assert_eq!(result, expected);
    }
}
