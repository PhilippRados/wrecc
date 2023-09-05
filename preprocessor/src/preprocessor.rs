use compiler::Error;
use compiler::ErrorKind;
use compiler::Location;

use crate::preprocess_included;
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
    ifs: Vec<Error>,
}

impl Preprocessor {
    pub fn new<'a>(
        filename: &'a str,
        input: &'a str,
        tokens: Vec<Token>,
        pre_defines: Option<HashMap<String, String>>,
    ) -> Self {
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
            ifs: vec![],
            defines: if let Some(defines) = pre_defines {
                defines
            } else {
                HashMap::new()
            },
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

        let (data, defines) = preprocess_included(file_path, &data, self.defines.clone())
            .or_else(|e| Err(self.errors(e)))?;

        self.defines.extend(defines);

        let header_prologue = format!("#pro:{}\n", file_path);
        let header_epilogue = format!("#epi:{}\0", self.line_index());

        Ok(header_prologue + &data + &header_epilogue)
    }

    fn include(&mut self) -> Result<String, ()> {
        self.skip_whitespace().or_else(|e| Err(self.error(e)))?;

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
                    ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
                ))),
            }
        } else {
            Err(self.error(Error::new(
                self,
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            )))
        }
    }
    fn define(&mut self) -> Result<(), Error> {
        self.skip_whitespace()?;

        if let Some(Token::Ident(identifier)) = self.tokens.next() {
            let _ = self.skip_whitespace();
            let replace_with = self.fold_until_newline();

            if self.defines.contains_key(&identifier) {
                Err(Error::new(
                    self,
                    ErrorKind::Redefinition("macro", identifier),
                ))
            } else {
                self.defines.insert(identifier, replace_with);
                Ok(())
            }
        } else {
            Err(Error::new(
                self,
                ErrorKind::Regular("Macro name must be valid identifier"),
            ))
        }
    }
    fn undef(&mut self) -> Result<(), Error> {
        self.skip_whitespace()?;

        if let Some(Token::Ident(identifier)) = self.tokens.next() {
            self.defines.remove(&identifier);
            Ok(())
        } else {
            Err(Error::new(
                self,
                ErrorKind::Regular("Macro name must be valid identifier"),
            ))
        }
    }
    fn ifdef(&mut self, if_kind: Token) -> Result<(), Error> {
        self.skip_whitespace()?;

        if let Some(Token::Ident(identifier)) = self.tokens.next() {
            self.ifs.push(Error::new(
                self,
                ErrorKind::UnterminatedIf(if_kind == Token::Ifdef),
            ));

            match (&if_kind, self.defines.contains_key(&identifier)) {
                // if matching conditional then continue processing tokens
                (Token::Ifdef, true) | (Token::Ifndef, false) => Ok(()),
                // if conditional doesn't match then skip all tokens until matching #endif
                (Token::Ifdef, false) | (Token::Ifndef, true) => {
                    let matching_endif = self.ifs.len();

                    while let Some(token) = self.tokens.next() {
                        match token {
                            Token::Newline => self.line += 1,
                            Token::Hash => {
                                let _ = self.skip_whitespace();
                                match self.tokens.next() {
                                    Some(Token::Endif) if self.ifs.len() == matching_endif => {
                                        // #ifs matching #endif
                                        self.ifs.pop();
                                        return Ok(());
                                    }
                                    Some(Token::Endif) => {
                                        // matches #if which was defined inside of the skipped #if block
                                        self.ifs.pop();
                                    }
                                    Some(Token::Ifdef | Token::Ifndef) => {
                                        self.ifs.push(Error::new(
                                            self,
                                            ErrorKind::UnterminatedIf(if_kind == Token::Ifdef),
                                        ));
                                    }
                                    _ => (),
                                }
                            }
                            _ => (),
                        }
                    }
                    // got to end of token-stream without finding matching #endif
                    Err(self.ifs.pop().unwrap())
                }
                _ => unreachable!(),
            }
        } else {
            Err(Error::new(
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
                    let _ = self.skip_whitespace();

                    let outcome = match self.tokens.next() {
                        Some(Token::Include) => {
                            if let Ok(s) = self.include() {
                                Ok(result.push_str(&s))
                            } else {
                                // include handles it's errors
                                continue;
                            }
                        }
                        Some(Token::Define) => self.define(),
                        Some(Token::Undef) => self.undef(),
                        Some(if_kind @ (Token::Ifdef | Token::Ifndef)) => self.ifdef(if_kind),
                        Some(Token::Endif) => {
                            if self.ifs.is_empty() {
                                Err(Error::new(
                                    &self,
                                    ErrorKind::Regular("Found '#endif' without matching '#if'"),
                                ))
                            } else {
                                self.ifs.pop();
                                Ok(())
                            }
                        }
                        Some(directive) => Err(Error::new(
                            &self,
                            ErrorKind::InvalidDirective(directive.to_string()),
                        )),
                        None => Err(Error::new(
                            &self,
                            ErrorKind::Regular("Expected preprocessor directive following '#'"),
                        )),
                    };

                    if let Err(e) = outcome {
                        self.error(e)
                    } else if !matches!(self.tokens.peek(), Some(Token::Newline)) {
                        self.error(Error::new(
                            &self,
                            ErrorKind::Regular(
                                "Found trailing tokens after preprocessor directive",
                            ),
                        ));
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
        if !self.ifs.is_empty() {
            self.errors(self.ifs.clone())
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

    fn skip_whitespace(&mut self) -> Result<(), Error> {
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
                        break;
                    }
                }
                _ => break,
            }
        }
        if found {
            Ok(())
        } else {
            Err(Error::new(
                self,
                ErrorKind::Regular("Expect whitespace after preprocessing directive"),
            ))
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
    fn setup(input: &str) -> (Vec<Token>, bool) {
        let tokens = scan(input);

        let mut pp = Preprocessor::new("", input, tokens, None);
        let result = pp.skip_whitespace();

        (pp.tokens.collect(), result.is_err())
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
        assert_eq!(errors, false);
    }

    #[test]
    fn skips_multiline_whitespace2() {
        let (tokens, errors) = setup("  \\\n\n#include");
        let expected = scan("\n#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, false);
    }

    #[test]
    fn skips_multiline_whitespace3() {
        let (tokens, errors) = setup(" \\include");
        let expected = scan("\\include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, false);
    }

    #[test]
    fn skips_multiline_whitespace_error() {
        let (tokens, errors) = setup("\\\n#include");
        let expected = scan("#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, true);
    }

    #[test]
    fn skips_multiline_whitespace_error2() {
        let (tokens, errors) = setup("\\some\n#include");
        let expected = scan("\\some\n#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, true);
    }
}
