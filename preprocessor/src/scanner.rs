use compiler::consume_while;
use std::collections::HashMap;

use std::iter::Peekable;
use std::str::Chars;

#[derive(Clone, Debug)]
pub enum Token {
    Hash,
    Include,
    Define,
    String(String),
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
            Token::Newline => "\\n".to_string(),
            Token::Comment(s, _) | Token::String(s) | Token::Ident(s) | Token::Whitespace(s) => {
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
            directives: HashMap::from([("include", Token::Include), ("define", Token::Define)]),
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
                '"' | '\'' | '<' => {
                    let mut s = String::from(c);
                    s.push_str(&consume_while(
                        &mut self.source,
                        |ch| if c == '<' { ch != '>' } else { ch != c },
                        false,
                    ));
                    if let Some(c) = self.source.next() {
                        s.push(c)
                    }

                    Token::String(s)
                }
                '/' => {
                    let (comment, newlines) = self.consume_comment();

                    Token::Comment(c.to_string() + &comment, newlines)
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

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    #[test]
    fn parses_header_file() {
        let mut input = "here.h>\nint some;".chars().peekable();
        let actual = consume_while(&mut input, |c| c != '>' && c != '\n', false);

        let expected = "here.h";
        let expected_steam = ">\nint some;";

        assert_eq!(actual, expected);
        assert_eq!(input.collect::<String>(), expected_steam);
    }
}
