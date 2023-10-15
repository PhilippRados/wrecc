use compiler::consume_while;
use std::collections::HashMap;

use std::iter::Peekable;
use std::str::Chars;

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Hash,
    Include,
    Define,
    Defined,
    Undef,
    Ifdef,
    Ifndef,
    If,
    Elif,
    Else,
    Endif,
    String(String),
    CharLit(String),
    Ident(String),
    Newline,
    Whitespace(String),
    Comment(String),
    Other(char),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub column: i32,
    pub line: i32,
}
impl Token {
    pub fn len(&self) -> usize {
        match &self.kind {
            TokenKind::Newline => 0,
            TokenKind::Hash | TokenKind::Other(_) => 1,
            TokenKind::If => 2,
            TokenKind::Else | TokenKind::Elif => 4,
            TokenKind::Undef | TokenKind::Ifdef | TokenKind::Endif => 5,
            TokenKind::Define | TokenKind::Ifndef => 6,
            TokenKind::Include | TokenKind::Defined => 7,
            TokenKind::String(s)
            | TokenKind::CharLit(s)
            | TokenKind::Ident(s)
            | TokenKind::Whitespace(s)
            | TokenKind::Comment(s) => s.len(),
        }
    }
}
impl TokenKind {
    // returns string of all valid identifiers
    pub fn as_ident(&self) -> Option<String> {
        match self {
            TokenKind::Ident(_)
            | TokenKind::Include
            | TokenKind::Define
            | TokenKind::Defined
            | TokenKind::Undef
            | TokenKind::Ifdef
            | TokenKind::Ifndef
            | TokenKind::If
            | TokenKind::Elif
            | TokenKind::Else
            | TokenKind::Endif => Some(self.to_string()),
            _ => None,
        }
    }
}
impl ToString for TokenKind {
    fn to_string(&self) -> String {
        match self {
            TokenKind::Hash => "#".to_string(),
            TokenKind::Include => "include".to_string(),
            TokenKind::Define => "define".to_string(),
            TokenKind::Defined => "defined".to_string(),
            TokenKind::Undef => "undef".to_string(),
            TokenKind::Ifdef => "ifdef".to_string(),
            TokenKind::Ifndef => "ifndef".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Elif => "elif".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::Endif => "endif".to_string(),
            TokenKind::Newline => "\n".to_string(),
            TokenKind::Comment(s)
            | TokenKind::String(s)
            | TokenKind::CharLit(s)
            | TokenKind::Ident(s)
            | TokenKind::Whitespace(s) => s.to_string(),
            TokenKind::Other(c) => c.to_string(),
        }
    }
}

pub struct Scanner<'a> {
    source: Peekable<Chars<'a>>,
    directives: HashMap<&'static str, TokenKind>,
    column: i32,
    line: i32,
}
impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Scanner {
        Scanner {
            column: 1,
            line: 1,
            source: source.chars().peekable(),
            directives: HashMap::from([
                ("include", TokenKind::Include),
                ("define", TokenKind::Define),
                ("defined", TokenKind::Defined),
                ("undef", TokenKind::Undef),
                ("ifdef", TokenKind::Ifdef),
                ("ifndef", TokenKind::Ifndef),
                ("if", TokenKind::If),
                ("elif", TokenKind::Elif),
                ("else", TokenKind::Else),
                ("endif", TokenKind::Endif),
            ]),
        }
    }
    pub fn scan_token(mut self) -> Vec<Token> {
        let mut result = Vec::new();

        while let Some(c) = self.source.next() {
            let token = match c {
                '#' => self.token(TokenKind::Hash, None),
                '\n' => {
                    let token = self.token(TokenKind::Newline, None);
                    self.column = 1;
                    self.line += 1;

                    token
                }
                ' ' | '\t' => {
                    let more_whitespace =
                        consume_while(&mut self.source, |c| c == ' ' || c == '\t', false);

                    self.token(
                        TokenKind::Whitespace(c.to_string() + &more_whitespace),
                        None,
                    )
                }
                '"' => {
                    let (s, newlines) = self.string('"');

                    self.token(TokenKind::String(s), Some(newlines))
                }
                '\'' => {
                    let (s, newlines) = self.string('\'');

                    self.token(TokenKind::CharLit(s), Some(newlines))
                }
                '/' => {
                    let (comment, newlines) = self.consume_comment();

                    self.token(
                        if comment.is_empty() {
                            TokenKind::Other('/')
                        } else {
                            TokenKind::Comment(c.to_string() + &comment)
                        },
                        Some(newlines),
                    )
                }
                _ if c.is_alphabetic() || c == '_' => {
                    let ident = c.to_string()
                        + &consume_while(
                            &mut self.source,
                            |c| c.is_alphabetic() || c == '_' || c.is_ascii_digit(),
                            false,
                        );

                    self.token(
                        if let Some(directive) = self.directives.get(ident.as_str()) {
                            directive.clone()
                        } else {
                            TokenKind::Ident(ident)
                        },
                        None,
                    )
                }
                _ => self.token(TokenKind::Other(c), None),
            };

            result.push(token);
        }
        result
    }
    fn string(&mut self, c: char) -> (String, usize) {
        let mut result = String::from(c);
        let mut newlines = 0;
        let mut prev_char = '\0';

        while let Some(peeked) = self.source.peek() {
            match (prev_char, peeked) {
                ('\\', '\n') => {
                    let token = self.source.next().unwrap();
                    result.pop();
                    newlines += 1;
                    prev_char = token;
                }
                (_, '\n') => break,
                (..) if *peeked == c => {
                    result.push(self.source.next().unwrap());
                    break;
                }
                (..) => {
                    let token = self.source.next().unwrap();
                    result.push_str(&token.to_string());
                    prev_char = token;
                }
            }
        }
        (result, newlines)
    }
    fn consume_comment(&mut self) -> (String, usize) {
        let mut result = String::new();
        let mut newlines = 0;

        match self.source.next() {
            Some(c @ '/') => {
                result.push(c);
                result.push_str(&consume_while(
                    &mut self.source,
                    |c| c != '\n' && c != '\0',
                    false,
                ));
            }
            Some(c @ '*') => {
                result.push(c);
                while let Some(c) = self.source.next() {
                    result.push(c);
                    match c {
                        '\n' => {
                            newlines += 1;
                        }
                        '*' => match self.source.next() {
                            Some(c @ '/') => {
                                result.push(c);
                                break;
                            }
                            Some(c) => result.push(c),
                            None => (),
                        },
                        _ => (),
                    }
                }
            }
            Some(c) => result.push(c),
            None => (),
        }

        (result, newlines)
    }
    fn token(&mut self, kind: TokenKind, newlines: Option<usize>) -> Token {
        let token = Token {
            column: self.column,
            line: self.line,
            kind,
        };
        self.column += token.len() as i32;
        if let Some(newlines) = newlines {
            self.line += newlines as i32;
        }
        token
    }
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    fn setup(input: &str) -> Vec<Token> {
        Scanner::new(input).scan_token()
    }
    fn setup_tokenkind(input: &str) -> Vec<TokenKind> {
        setup(input).into_iter().map(|t| t.kind).collect()
    }
    fn setup_tok_line(input: &str) -> Vec<(TokenKind, i32)> {
        setup(input).into_iter().map(|t| (t.kind, t.line)).collect()
    }

    #[test]
    fn simple_pp_directive() {
        let actual = setup_tokenkind("#  include \"'some'\"");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::Whitespace("  ".to_string()),
            TokenKind::Include,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::String("\"'some'\"".to_string()),
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn string() {
        let actual = setup_tokenkind("#define \"some/* #*/define\"");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::Define,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::String("\"some/* #*/define\"".to_string()),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn ident() {
        let actual = setup_tokenkind("1first 2 some23: more");
        let expected = vec![
            TokenKind::Other('1'),
            TokenKind::Ident("first".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('2'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("some23".to_string()),
            TokenKind::Other(':'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("more".to_string()),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn macro_name() {
        let actual = setup_tokenkind("#define NULL((void *)0)");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::Define,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("NULL".to_string()),
            TokenKind::Other('('),
            TokenKind::Other('('),
            TokenKind::Ident("void".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('*'),
            TokenKind::Other(')'),
            TokenKind::Other('0'),
            TokenKind::Other(')'),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_escaped() {
        let actual = setup_tok_line(" \"some\\\n\\else\"");
        let expected = vec![
            (TokenKind::Whitespace(" ".to_string()), 1),
            (TokenKind::String("\"some\\else\"".to_string()), 1),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_multiple_escapes() {
        let actual = setup_tok_line(" \"some\\\n\nmore\"");
        let expected = vec![
            (TokenKind::Whitespace(" ".to_string()), 1),
            (TokenKind::String("\"some".to_string()), 1),
            (TokenKind::Newline, 2),
            (TokenKind::Ident("more".to_string()), 3),
            (TokenKind::String("\"".to_string()), 3),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_unescaped() {
        let actual = setup_tok_line(" \"some\nmore\"");
        let expected = vec![
            (TokenKind::Whitespace(" ".to_string()), 1),
            (TokenKind::String("\"some".to_string()), 1),
            (TokenKind::Newline, 1),
            (TokenKind::Ident("more".to_string()), 2),
            (TokenKind::String("\"".to_string()), 2),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn if_const_expr() {
        let actual = setup_tokenkind("#if 1 < num\n");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::If,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('1'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('<'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("num".to_string()),
            TokenKind::Newline,
        ];

        assert_eq!(actual, expected);
    }
}
