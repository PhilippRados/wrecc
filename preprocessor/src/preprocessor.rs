use compiler::Error;
use compiler::ErrorKind;
use compiler::Location;

use crate::preprocess;
use crate::Token;

use std::collections::HashMap;
use std::fs;
use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Preprocessor {
    tokens: Peekable<IntoIter<Token>>,
    errors: Vec<Error>,
    raw_source: Vec<String>,
    line: i32,
    column: i32,
    filename: String,
    defines: HashMap<String, String>,
}

impl Preprocessor {
    pub fn new<'a>(filename: &'a str, input: &'a str, tokens: Vec<Token>) -> Self {
        Preprocessor {
            tokens: tokens.into_iter().peekable(),
            raw_source: input
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
            errors: Vec::new(),
            line: 1,
            column: 1,
            filename: filename.to_string(),
            defines: HashMap::new(),
        }
    }

    fn paste_header(&mut self, file_path: &str) -> Result<String, ()> {
        // WARN: only temporary absolute path. /include will be found via PATH env var
        let abs_path =
            "/Users/philipprados/documents/coding/Rust/rucc/include/".to_string() + file_path;

        let data = fs::read_to_string(&abs_path).or_else(|_| {
            Err(self.error(Error::new(
                self,
                ErrorKind::InvalidHeader(file_path.to_string()),
            )))
        })?;

        let (data, defines) = preprocess(file_path, &data).or_else(|e| Err(self.errors(e)))?;

        // TODO: check what happens if two hashmaps have same key
        // if there were #defines defined in the included file, include them in current file too
        self.defines.extend(defines);

        let header_prologue = format!("#pro:{}\n", file_path);
        // TODO: maybe can use same marker token \n
        let header_epilogue = format!("#epi:{}\0", self.line_index());

        Ok(header_prologue + &data + &header_epilogue)
    }

    fn include(&mut self) -> Result<String, ()> {
        if let Some(Token::String(mut file, newlines)) = self.tokens.next() {
            self.line += newlines as i32;
            let kind = file.remove(0);

            match kind {
                '<' => {
                    let last = file.pop();

                    if let Some('>') = last {
                        self.paste_header(&file)
                    } else {
                        Err(self.error(Error::new(
                            self,
                            ErrorKind::Regular("Expected closing '>' after header file"),
                        )))
                    }
                }
                '"' => {
                    todo!()
                }
                _ => Err(self.error(Error::new(
                    self,
                    ErrorKind::Regular("Expected closing '>' after header file"),
                ))),
            }
        } else {
            Err(self.error(Error::new(
                self,
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            )))
        }
    }
    fn define(&mut self) {
        if let Some(Token::Ident(identifier)) = self.tokens.next() {
            self.skip_whitespace(true);
            let replace_with = self.fold_until_newline();

            self.defines.insert(identifier, replace_with);
        } else {
            self.error(Error::new(
                self,
                ErrorKind::Regular("Macro name must be valid identifier"),
            ))
        }
    }

    pub fn start(mut self) -> Result<(String, HashMap<String, String>), Vec<Error>> {
        let mut result = String::from("");

        while let Some(token) = self.tokens.next() {
            match token {
                Token::Hash if is_first_line_token(&result) => {
                    self.skip_whitespace(false);

                    match self.tokens.next() {
                        Some(Token::Include) => {
                            self.skip_whitespace(true);

                            if let Ok(s) = self.include() {
                                result.push_str(&s)
                            }
                        }
                        Some(Token::Define) => {
                            self.skip_whitespace(true);

                            self.define();
                        }
                        Some(directive) => self.error(Error::new(
                            &self,
                            ErrorKind::InvalidDirective(directive.to_string()),
                        )),
                        None => self.error(Error::new(
                            &self,
                            ErrorKind::Regular("Expected preprocessor directive following '#'"),
                        )),
                    }
                }
                Token::Newline => {
                    self.line += 1;
                    result.push('\n');
                }
                Token::Ident(s) => {
                    if let Some(replacement) = self.defines.get(&s) {
                        result.push_str(replacement)
                    } else {
                        result.push_str(&s)
                    }
                }
                Token::Other(c) => result.push(c),
                Token::Comment(s, newlines) | Token::String(s, newlines) => {
                    self.line += newlines as i32;
                    result.push_str(&s);
                }
                _ => result.push_str(&token.to_string()),
            }
        }

        if self.errors.is_empty() {
            Ok((result, self.defines))
        } else {
            Err(self.errors)
        }
    }
    fn error(&mut self, e: Error) {
        self.errors.push(e)
    }
    fn errors(&mut self, mut e: Vec<Error>) {
        self.errors.append(&mut e)
    }

    fn skip_whitespace(&mut self, required: bool) {
        let mut found = false;

        while let Some(token) = self.tokens.peek() {
            match token {
                Token::Whitespace(_) => {
                    self.tokens.next();
                    found = true;
                }
                Token::Other('\\') => {
                    let prev = self.tokens.next().unwrap();

                    if let Some(Token::Newline) = self.tokens.peek() {
                        self.line += 1;
                        self.tokens.next();
                    } else {
                        self.insert_token(prev);
                        if required && !found {
                            self.error(Error::new(
                                self,
                                ErrorKind::Regular(
                                    "Expect whitespace after preprocessing directive",
                                ),
                            ));
                        }
                        break;
                    }
                }
                _ if required && !found => {
                    self.error(Error::new(
                        self,
                        ErrorKind::Regular("Expect whitespace after preprocessing directive"),
                    ));
                    break;
                }
                _ => break,
            }
        }
    }

    fn fold_until_newline(&mut self) -> String {
        let mut result = String::new();
        let mut prev_token = Token::Newline;

        while let Some(token) = self.tokens.peek() {
            match (&prev_token, token) {
                (Token::Other('\\'), Token::Newline) => {
                    self.tokens.next();
                    result.pop();
                    self.line += 1;
                }
                (_, Token::Newline) => break,
                (.., t) => {
                    if let Token::String(_, newline) = t {
                        self.line += *newline as i32;
                    }
                    let token = self.tokens.next().unwrap();
                    result.push_str(&token.to_string());
                    prev_token = token.clone();
                }
            }
        }
        result
    }

    fn insert_token(&mut self, token: Token) {
        let mut start = vec![token];
        while let Some(t) = self.tokens.next() {
            start.push(t);
        }
        self.tokens = start.into_iter().peekable();
    }
}

impl Location for Preprocessor {
    fn line_index(&self) -> i32 {
        self.line
    }
    fn column(&self) -> i32 {
        self.column
    }
    fn line_string(&self) -> String {
        self.raw_source[(self.line - 1) as usize].clone()
    }
    fn filename(&self) -> String {
        self.filename.to_string()
    }
}

fn is_first_line_token(prev_tokens: &str) -> bool {
    for c in prev_tokens.chars().rev() {
        match c {
            '\n' => return true,
            ' ' | '\t' => (),
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;
    use crate::Scanner;

    fn scan(input: &str) -> Vec<Token> {
        Scanner::new(input).scan_token()
    }
    fn setup(input: &str) -> (Vec<Token>, Vec<Error>) {
        let tokens = scan(input);

        let mut pp = Preprocessor::new("", input, tokens);
        pp.skip_whitespace(true);

        (pp.tokens.collect(), pp.errors)
    }

    #[test]
    fn first_line_token() {
        assert_eq!(is_first_line_token(""), true);
        assert_eq!(is_first_line_token("\n  \t "), true);
        assert_eq!(is_first_line_token("\nint\n "), true);
        assert_eq!(is_first_line_token("\nint "), false);
        assert_eq!(is_first_line_token("+ "), false);
    }

    #[test]
    fn skips_multiline_whitespace() {
        let (tokens, errors) = setup("  \\\n \n#include");
        let expected = scan("\n#include");

        assert_eq!(tokens, expected);
        assert!(errors.is_empty());
    }

    #[test]
    fn skips_multiline_whitespace2() {
        let (tokens, errors) = setup("  \\\n\n#include");
        let expected = scan("\n#include");

        assert_eq!(tokens, expected);
        assert!(errors.is_empty());
    }

    #[test]
    fn skips_multiline_whitespace3() {
        let (tokens, errors) = setup(" \\include");
        let expected = scan("\\include");

        assert_eq!(tokens, expected);
        assert!(errors.is_empty());
    }

    #[test]
    fn skips_multiline_whitespace_error() {
        let (tokens, errors) = setup("\\\n#include");
        let expected = scan("#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors.len(), 1);
    }

    #[test]
    fn skips_multiline_whitespace_error2() {
        let (tokens, errors) = setup("\\some\n#include");
        let expected = scan("\\some\n#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors.len(), 1);
    }
}
