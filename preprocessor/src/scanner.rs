use compiler::consume_while;
use std::collections::HashMap;

use std::iter::Peekable;
use std::str::Chars;

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Hash,
    Include,
    Define,
    Defined,
    Undef,
    Ifdef,
    Ifndef,
    If,
    Endif,
    String(String, usize),
    Ident(String),
    Newline,
    Whitespace(String),
    Comment(String, usize),
    Other(char),
}
impl ToString for Token {
    fn to_string(&self) -> String {
        match self {
            Token::Hash => "#".to_string(),
            Token::Include => "include".to_string(),
            Token::Define => "define".to_string(),
            Token::Defined => "defined".to_string(),
            Token::Undef => "undef".to_string(),
            Token::Ifdef => "ifdef".to_string(),
            Token::Ifndef => "ifndef".to_string(),
            Token::If => "if".to_string(),
            Token::Endif => "endif".to_string(),
            Token::Newline => "\\n".to_string(),
            Token::Comment(s, _) | Token::String(s, _) | Token::Ident(s) | Token::Whitespace(s) => {
                s.to_string()
            }
            Token::Other(c) => c.to_string(),
        }
    }
}

pub struct Scanner<'a> {
    source: Peekable<Chars<'a>>,
    directives: HashMap<&'static str, Token>,
}
impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Scanner {
        Scanner {
            source: source.chars().peekable(),
            directives: HashMap::from([
                ("include", Token::Include),
                ("define", Token::Define),
                ("defined", Token::Defined),
                ("undef", Token::Undef),
                ("ifdef", Token::Ifdef),
                ("ifndef", Token::Ifndef),
                ("if", Token::If),
                ("endif", Token::Endif),
            ]),
        }
    }
    pub fn scan_token(mut self) -> Vec<Token> {
        let mut result = Vec::new();

        while let Some(c) = self.source.next() {
            let token = match c {
                '#' => Token::Hash,
                '\n' => Token::Newline,
                ' ' | '\t' => {
                    let more_whitespace =
                        consume_while(&mut self.source, |c| c == ' ' || c == '\t', false);

                    Token::Whitespace(c.to_string() + &more_whitespace)
                }
                '"' | '\'' => {
                    let (s, newlines) = self.string(c);

                    Token::String(s, newlines)
                }
                '/' => {
                    let (comment, newlines) = self.consume_comment();

                    if comment.is_empty() {
                        Token::Other('/')
                    } else {
                        Token::Comment(c.to_string() + &comment, newlines)
                    }
                }
                _ if c.is_alphabetic() || c == '_' => {
                    let ident = c.to_string()
                        + &consume_while(
                            &mut self.source,
                            |c| c.is_alphabetic() || c == '_' || c.is_ascii_digit(),
                            false,
                        );

                    if let Some(directive) = self.directives.get(ident.as_str()) {
                        directive.clone()
                    } else {
                        Token::Ident(ident)
                    }
                }
                _ => Token::Other(c),
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
                (..) if *peeked == matching_closing(c) => {
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
}

fn matching_closing(opening: char) -> char {
    match opening {
        '<' => '>',
        '\'' => '\'',
        '"' => '"',
        _ => unreachable!("invalid opening string indicator"),
    }
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    fn setup(input: &str) -> Vec<Token> {
        Scanner::new(input).scan_token()
    }

    #[test]
    fn simple_pp_directive() {
        let actual = setup("#  include \"'some'\"");
        let expected = vec![
            Token::Hash,
            Token::Whitespace("  ".to_string()),
            Token::Include,
            Token::Whitespace(" ".to_string()),
            Token::String("\"'some'\"".to_string(), 0),
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn string() {
        let actual = setup("#define \"some/* #*/define\"");
        let expected = vec![
            Token::Hash,
            Token::Define,
            Token::Whitespace(" ".to_string()),
            Token::String("\"some/* #*/define\"".to_string(), 0),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn ident() {
        let actual = setup("1first 2 some23: else");
        let expected = vec![
            Token::Other('1'),
            Token::Ident("first".to_string()),
            Token::Whitespace(" ".to_string()),
            Token::Other('2'),
            Token::Whitespace(" ".to_string()),
            Token::Ident("some23".to_string()),
            Token::Other(':'),
            Token::Whitespace(" ".to_string()),
            Token::Ident("else".to_string()),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn macro_name() {
        let actual = setup("#define NULL((void *)0)");
        let expected = vec![
            Token::Hash,
            Token::Define,
            Token::Whitespace(" ".to_string()),
            Token::Ident("NULL".to_string()),
            Token::Other('('),
            Token::Other('('),
            Token::Ident("void".to_string()),
            Token::Whitespace(" ".to_string()),
            Token::Other('*'),
            Token::Other(')'),
            Token::Other('0'),
            Token::Other(')'),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_escaped() {
        let actual = setup(" \"some\\\n\\else\"");
        let expected = vec![
            Token::Whitespace(" ".to_string()),
            Token::String("\"some\\else\"".to_string(), 1),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_multiple_escapes() {
        let actual = setup(" \"some\\\n\nelse\"");
        let expected = vec![
            Token::Whitespace(" ".to_string()),
            Token::String("\"some".to_string(), 1),
            Token::Newline,
            Token::Ident("else".to_string()),
            Token::String("\"".to_string(), 0),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_unescaped() {
        let actual = setup(" \"some\nelse\"");
        let expected = vec![
            Token::Whitespace(" ".to_string()),
            Token::String("\"some".to_string(), 0),
            Token::Newline,
            Token::Ident("else".to_string()),
            Token::String("\"".to_string(), 0),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn if_const_expr() {
        let actual = setup("#if 1 < num\n");
        let expected = vec![
            Token::Hash,
            Token::If,
            Token::Whitespace(" ".to_string()),
            Token::Other('1'),
            Token::Whitespace(" ".to_string()),
            Token::Other('<'),
            Token::Whitespace(" ".to_string()),
            Token::Ident("num".to_string()),
            Token::Newline,
        ];

        assert_eq!(actual, expected);
    }
}
