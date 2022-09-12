use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum TokenType {
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
    For,
    If,
    Return,
    While,
    Print,

    Eof,
}
impl PartialEq for TokenType {
    // Allow enum-values to be the same even when their arguments differ:
    // TokenType::Number(2) == TokenType::Number(0)
    fn eq(&self, other: &Self) -> bool {
        let tag = std::mem::discriminant(self);
        let o_tag = std::mem::discriminant(other);

        tag == o_tag
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Tokens {
    pub token: TokenType,
    pub line_index: i32,
    pub column: i32,
    pub line_string: String,
}
impl Tokens {
    pub fn new(token: TokenType, line_index: i32, column: i32, line_string: String) -> Self {
        Tokens {
            token,
            line_index,
            column,
            line_string,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Error {
    pub line_index: i32,
    pub line_string: String,
    pub column: i32,
    pub msg: String,
}

impl Error {
    pub fn new(t: &Tokens, msg: &str) -> Self {
        Error {
            line_index: t.line_index,
            line_string: t.line_string.clone(),
            column: t.column,
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
}

pub struct Scanner<'a> {
    source: Peekable<Chars<'a>>,
    raw_source: Vec<String>,
    line: i32,
    column: i32,
    keywords: HashMap<String, TokenType>,
    err: bool,
}
impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        Scanner {
            source: source.chars().peekable(),
            raw_source: source
                .split("\n")
                .map(|s| s.to_string().clone())
                .collect::<Vec<String>>(),
            line: 1,
            column: 1,
            err: false,
            keywords: HashMap::from([
                ("int".to_string(), TokenType::Int),
                ("char".to_string(), TokenType::Char),
                ("if".to_string(), TokenType::If),
                ("else".to_string(), TokenType::Else),
                ("for".to_string(), TokenType::For),
                ("while".to_string(), TokenType::While),
                ("return".to_string(), TokenType::Return),
                ("print".to_string(), TokenType::Print),
            ]),
        }
    }

    fn match_next(&mut self, expected: char, if_match: TokenType, if_not: TokenType) -> TokenType {
        match self.source.next_if_eq(&expected) {
            Some(_v) => if_match,
            None => if_not,
        }
    }
    fn add_token(&mut self, tokens: &mut Vec<Tokens>, current_token: TokenType) {
        tokens.push(Tokens {
            token: current_token.clone(),
            line_index: self.line,
            column: self.column,
            line_string: self.raw_source[(self.line - 1) as usize].clone(),
        });
        self.column += Self::get_token_len(current_token);
    }
    fn get_token_len(token: TokenType) -> i32 {
        match token {
            TokenType::BangEqual
            | TokenType::EqualEqual
            | TokenType::GreaterEqual
            | TokenType::LessEqual => 2,
            TokenType::String(s) => (s.len() + 2) as i32,
            TokenType::Ident(s) => s.len() as i32,
            TokenType::Int | TokenType::For => 3,
            TokenType::Char | TokenType::Else => 4,
            TokenType::While | TokenType::Print => 5,
            TokenType::If => 2,
            TokenType::Return => 6,
            TokenType::Number(n) => n.to_string().len() as i32,
            _ => 1,
        }
    }
    pub fn scan_token(&mut self) -> Result<Vec<Tokens>, Vec<Error>> {
        let mut errors: Vec<Error> = Vec::new();
        let mut tokens: Vec<Tokens> = Vec::new();

        while let Some(c) = self.source.next() {
            match c {
                '(' => self.add_token(&mut tokens, TokenType::LeftParen),
                ')' => self.add_token(&mut tokens, TokenType::RightParen),
                '{' => self.add_token(&mut tokens, TokenType::LeftBrace),
                '}' => self.add_token(&mut tokens, TokenType::RightBrace),
                ',' => self.add_token(&mut tokens, TokenType::Comma),
                '.' => self.add_token(&mut tokens, TokenType::Dot),
                '-' => self.add_token(&mut tokens, TokenType::Minus),
                '+' => self.add_token(&mut tokens, TokenType::Plus),
                ';' => self.add_token(&mut tokens, TokenType::Semicolon),
                '*' => self.add_token(&mut tokens, TokenType::Star),

                '!' => {
                    let token = self.match_next('=', TokenType::BangEqual, TokenType::Bang);
                    self.add_token(&mut tokens, token);
                }
                '=' => {
                    let token = self.match_next('=', TokenType::EqualEqual, TokenType::Equal);
                    self.add_token(&mut tokens, token);
                }
                '<' => {
                    let token = self.match_next('=', TokenType::LessEqual, TokenType::Less);
                    self.add_token(&mut tokens, token);
                }
                '>' => {
                    let token = self.match_next('=', TokenType::GreaterEqual, TokenType::Greater);
                    self.add_token(&mut tokens, token);
                }

                '/' => {
                    if self.matches('/') {
                        // there has to be a better way to consume the iter without the first \n
                        while let Some(_) =
                            self.source.by_ref().next_if(|&c| c != '\n' && c != '\0')
                        {
                        }
                    } else {
                        self.add_token(&mut tokens, TokenType::Slash)
                    }
                }
                ' ' | '\r' | '\t' => self.column += 1,
                '\n' => {
                    self.line += 1;
                    self.column = 1
                }

                '"' => match self.string() {
                    Ok(string) => self.add_token(&mut tokens, TokenType::String(string.clone())),
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
                        self.add_token(&mut tokens, TokenType::Number(num.parse::<i32>().unwrap()));
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
                            self.add_token(&mut tokens, self.keywords.get(&value).unwrap().clone());
                        } else {
                            self.add_token(&mut tokens, TokenType::Ident(value.to_string()))
                        }
                    } else {
                        self.err = true;
                        errors.push(Error {
                            line_index: self.line,
                            line_string: self.raw_source[(self.line - 1) as usize].clone(),
                            column: self.column,
                            msg: format!("Unexpected character: {c}").to_string(),
                        });
                        self.column += 1;
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

    fn string(&mut self) -> Result<String, Error> {
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
            return Err(Error {
                line_index: self.line,
                line_string: self.raw_source[(self.line - 1) as usize].clone(),
                column: self.column,
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
        let source = "!= = > == \n\n    ;";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(TokenType::BangEqual, 1, 1, "!= = > == ".to_string()),
            Tokens::new(TokenType::Equal, 1, 4, "!= = > == ".to_string()),
            Tokens::new(TokenType::Greater, 1, 6, "!= = > == ".to_string()),
            Tokens::new(TokenType::EqualEqual, 1, 8, "!= = > == ".to_string()),
            Tokens::new(TokenType::Semicolon, 3, 5, "    ;".to_string()),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn ignores_comments() {
        let source = "// this is a    comment\n\n!this";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(TokenType::Bang, 3, 1, "!this".to_string()),
            Tokens::new(
                TokenType::Ident("this".to_string()),
                3,
                2,
                "!this".to_string(),
            ),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn token_basic_math_expression() {
        let source = "3 + 1 / 4";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(TokenType::Number(3), 1, 1, "3 + 1 / 4".to_string()),
            Tokens::new(TokenType::Plus, 1, 3, "3 + 1 / 4".to_string()),
            Tokens::new(TokenType::Number(1), 1, 5, "3 + 1 / 4".to_string()),
            Tokens::new(TokenType::Slash, 1, 7, "3 + 1 / 4".to_string()),
            Tokens::new(TokenType::Number(4), 1, 9, "3 + 1 / 4".to_string()),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn basic_math_double_digit_nums() {
        let source = "300 - 11 * 41";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(TokenType::Number(300), 1, 1, "300 - 11 * 41".to_string()),
            Tokens::new(TokenType::Minus, 1, 5, "300 - 11 * 41".to_string()),
            Tokens::new(TokenType::Number(11), 1, 7, "300 - 11 * 41".to_string()),
            Tokens::new(TokenType::Star, 1, 10, "300 - 11 * 41".to_string()),
            Tokens::new(TokenType::Number(41), 1, 12, "300 - 11 * 41".to_string()),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn matches_keywords_and_strings() {
        let source = "int some = \"this is a string\"";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(
                TokenType::Int,
                1,
                1,
                "int some = \"this is a string\"".to_string(),
            ),
            Tokens::new(
                TokenType::Ident("some".to_string()),
                1,
                5,
                "int some = \"this is a string\"".to_string(),
            ),
            Tokens::new(
                TokenType::Equal,
                1,
                10,
                "int some = \"this is a string\"".to_string(),
            ),
            Tokens::new(
                TokenType::String("this is a string".to_string()),
                1,
                12,
                "int some = \"this is a string\"".to_string(),
            ),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn matches_print_keyword() {
        let source = "print 2 +;";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(TokenType::Print, 1, 1, "print 2 +;".to_string()),
            Tokens::new(TokenType::Number(2), 1, 7, "print 2 +;".to_string()),
            Tokens::new(TokenType::Plus, 1, 9, "print 2 +;".to_string()),
            Tokens::new(TokenType::Semicolon, 1, 10, "print 2 +;".to_string()),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn errors_on_unterminated_string() {
        let source = "int some = \"this is a string";
        let mut scanner = Scanner::new(source);

        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![Error {
            line_index: 1,
            line_string: "int some = \"this is a string".to_string(),
            column: 12,
            msg: "Unterminated string".to_string(),
        }];
        assert_eq!(result, expected);
    }
    #[test]
    fn matches_complex_keywords() {
        let source = "int some_long;\nwhile (val >= 12) {*p = val}";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!("test"),
        };
        let expected = vec![
            Tokens::new(TokenType::Int, 1, 1, "int some_long;".to_string()),
            Tokens::new(
                TokenType::Ident("some_long".to_string()),
                1,
                5,
                "int some_long;".to_string(),
            ),
            Tokens::new(TokenType::Semicolon, 1, 14, "int some_long;".to_string()),
            Tokens::new(
                TokenType::While,
                2,
                1,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::LeftParen,
                2,
                7,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::Ident("val".to_string()),
                2,
                8,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::GreaterEqual,
                2,
                12,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::Number(12),
                2,
                15,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::RightParen,
                2,
                17,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::LeftBrace,
                2,
                19,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::Star,
                2,
                20,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::Ident("p".to_string()),
                2,
                21,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::Equal,
                2,
                23,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::Ident("val".to_string()),
                2,
                25,
                "while (val >= 12) {*p = val}".to_string(),
            ),
            Tokens::new(
                TokenType::RightBrace,
                2,
                28,
                "while (val >= 12) {*p = val}".to_string(),
            ),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn detects_single_on_invalid_char() {
        let source = "int c = 0$";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(_v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![Error {
            line_index: 1,
            column: 10,
            line_string: "int c = 0$".to_string(),
            msg: "Unexpected character: $".to_string(),
        }];
        assert_eq!(result, expected);
    }
    #[test]
    fn detects_mutliple_on_invalid_chars() {
        let source = "int c = 0$\n\n% ^";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![
            Error {
                line_index: 1,
                column: 10,
                line_string: "int c = 0$".to_string(),
                msg: "Unexpected character: $".to_string(),
            },
            Error {
                line_index: 3,
                column: 1,
                line_string: "% ^".to_string(),
                msg: "Unexpected character: %".to_string(),
            },
            Error {
                line_index: 3,
                column: 3,
                line_string: "% ^".to_string(),
                msg: "Unexpected character: ^".to_string(),
            },
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn can_handle_non_ascii_alphabet() {
        let source = "\nint ä = 123";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => v,
            Err(e) => panic!(),
        };
        let expected = vec![
            Tokens::new(TokenType::Int, 2, 1, "int ä = 123".to_string()),
            Tokens::new(
                TokenType::Ident("ä".to_string()),
                2,
                5,
                "int ä = 123".to_string(),
            ),
            Tokens::new(TokenType::Equal, 2, 8, "int ä = 123".to_string()), // ä len is 2 but thats fine because its the same when indexing
            Tokens::new(TokenType::Number(123), 2, 10, "int ä = 123".to_string()),
        ];
        assert_eq!(result, expected);
    }
    #[test]
    fn errors_on_non_ascii_non_letters() {
        let source = "\nint ä ~ = 123";
        let mut scanner = Scanner::new(source);
        let result = match scanner.scan_token() {
            Ok(v) => panic!(),
            Err(e) => e,
        };
        let expected = vec![Error {
            line_index: 2,
            column: 8,
            line_string: "int ä ~ = 123".to_string(),
            msg: "Unexpected character: ~".to_string(),
        }];
        assert_eq!(result, expected);
    }
}
