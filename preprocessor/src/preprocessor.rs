use compiler::Error;
use compiler::ErrorKind;
use compiler::Location;
use compiler::Parser;
use compiler::Scanner;

use crate::preprocess_included;
use crate::Token;

use std::collections::HashMap;
use std::fs;
use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Preprocessor {
    tokens: Peekable<IntoIter<Token>>,
    raw_source: Vec<String>,
    line: i32,
    column: i32,
    filename: String,
    defines: HashMap<String, Vec<Token>>,
    ifs: Vec<Error>,
}

impl Preprocessor {
    pub fn new<'a>(
        filename: &'a str,
        input: &'a str,
        tokens: Vec<Token>,
        pre_defines: Option<HashMap<String, Vec<Token>>>,
    ) -> Self {
        Preprocessor {
            tokens: tokens.into_iter().peekable(),
            raw_source: input
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
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

    fn paste_header(&mut self, file_path: &str) -> Result<String, Error> {
        // WARN: only temporary absolute path. /include will be found via PATH env var
        let abs_path =
            "/Users/philipprados/documents/coding/Rust/rucc/include/".to_string() + file_path;

        let data = fs::read_to_string(&abs_path).or_else(|_| {
            Err(Error::new(
                self,
                ErrorKind::InvalidHeader(file_path.to_string()),
            ))
        })?;

        let (data, defines) = preprocess_included(file_path, &data, self.defines.clone())
            .or_else(|e| Err(Error::new_multiple(e)))?;

        self.defines.extend(defines);

        let header_prologue = format!("#pro:{}\n", file_path);
        let header_epilogue = format!("#epi:{}\0", self.line_index());

        Ok(header_prologue + &data + &header_epilogue)
    }

    fn include(&mut self) -> Result<String, Error> {
        self.skip_whitespace()?;

        if let Some(Token::String(mut file, newlines)) = self.tokens.next() {
            self.line += newlines as i32;
            let kind = file.remove(0);

            match kind {
                '<' => {
                    let last = file.pop();

                    if let Some('>') = last {
                        self.paste_header(&file)
                    } else {
                        Err(Error::new(
                            self,
                            ErrorKind::Regular("Expected closing '>' after header file"),
                        ))
                    }
                }
                '"' => {
                    todo!()
                }
                _ => Err(Error::new(
                    self,
                    ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
                )),
            }
        } else {
            Err(Error::new(
                self,
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            ))
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
    fn replace_macros(&self, macro_name: &str, replace_list: Vec<Token>) -> Vec<Token> {
        replace_list
            .into_iter()
            .flat_map(|t| {
                if t.to_string() != macro_name {
                    if let Some(replacement) = self.defines.get(&t.to_string()) {
                        // replace all macros in replacement
                        self.replace_macros(macro_name, replacement.clone())
                    } else {
                        vec![t]
                    }
                } else {
                    // can't further replace if replacement is current macro name
                    vec![t]
                }
            })
            .collect()
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
            // TODO: should this be prior to whitespace check so that #endif still has matching #if?
            self.ifs.push(Error::new(
                self,
                ErrorKind::UnterminatedIf(if_kind.to_string()),
            ));

            match (&if_kind, self.defines.contains_key(&identifier)) {
                (Token::Ifdef, true) | (Token::Ifndef, false) => Ok(()),
                (Token::Ifdef, false) | (Token::Ifndef, true) => self.skip_until_endif(),
                _ => unreachable!(),
            }
        } else {
            Err(Error::new(
                self,
                ErrorKind::Regular("Macro name must be valid identifier"),
            ))
        }
    }
    fn if_expr(&mut self, if_kind: Token) -> Result<(), Error> {
        self.ifs.push(Error::new(
            self,
            ErrorKind::UnterminatedIf(if_kind.to_string()),
        ));

        self.skip_whitespace()?;

        let cond = self.fold_until_newline();
        let cond = self.replace_define_expr(cond)?;

        if cond.is_empty() {
            return Err(Error::new(
                self,
                ErrorKind::Regular("'#if' directive expects expression"),
            ));
        }

        let value = self.pp_const_value(cond);

        match value {
            Ok(n) if n != 0 => Ok(()),
            Ok(_) => self.skip_until_endif(),
            Err(e) => Err(e),
        }
    }

    fn pp_const_value(&self, cond: String) -> Result<i64, Error> {
        let tokens = Scanner::new(&self.filename, &cond)
            .scan_token()
            .or_else(|errs| {
                Err(Error::new_multiple(
                    errs.into_iter().map(|e| Error::new(self, e.kind)).collect(),
                ))
            })?;
        let mut parser = Parser::new(tokens);
        let mut expr = parser
            .expression()
            .or_else(|e| Err(Error::new(self, e.kind)))?;

        if !parser.is_empty() {
            return Err(Error::new(
                self,
                ErrorKind::Regular("Trailing tokens in preprocessor expression"),
            ));
        }

        let value = expr.preprocessor_constant(self)?;

        Ok(value)
    }

    fn replace_define_expr(&mut self, cond: Vec<Token>) -> Result<String, Error> {
        let mut result = Vec::with_capacity(cond.len());
        let mut cond = cond.into_iter().peekable();

        while let Some(token) = cond.next() {
            match &token {
                Token::Defined => {
                    let _ = skip_whitespace(&mut cond, &mut self.line);

                    let open_paren = if let Some(Token::Other('(')) = cond.peek() {
                        cond.next();
                        true
                    } else {
                        false
                    };

                    let _ = skip_whitespace(&mut cond, &mut self.line);
                    if let Some(Token::Ident(identifier)) = cond.next() {
                        result.push(Token::Whitespace(" ".to_string()));
                        result.push(if self.defines.contains_key(&identifier) {
                            Token::Other('1')
                        } else {
                            Token::Other('0')
                        });
                        result.push(Token::Whitespace(" ".to_string()));

                        let _ = skip_whitespace(&mut cond, &mut self.line);
                        if open_paren && !matches!(cond.next(), Some(Token::Other(')'))) {
                            return Err(Error::new(
                                self,
                                ErrorKind::Regular("Expect closing ')' after 'defined'"),
                            ));
                        }
                    } else {
                        return Err(Error::new(
                            self,
                            ErrorKind::Regular("Expect identifier after 'defined'-operator"),
                        ));
                    }
                }
                Token::Ident(s) => {
                    // if ident is defined replace it
                    if let Some(replacement) = self.defines.get(s) {
                        let expanded_replacement = self.replace_macros(&s, replacement.clone());
                        result.extend(expanded_replacement)
                    } else {
                        result.push(token)
                    }
                }
                _ => result.push(token),
            }
        }
        // replace all identifiers with 0
        let result = result
            .into_iter()
            .map(|token| {
                if let Token::Ident(_) = token {
                    // hacky: insert whitespace so doesnt get appended to existing number
                    " 0 ".to_string()
                } else {
                    token.to_string()
                }
            })
            .collect();

        Ok(result)
    }
    fn skip_until_endif(&mut self) -> Result<(), Error> {
        while let Some(token) = self.tokens.next() {
            match token {
                Token::Hash => {
                    let _ = self.skip_whitespace();
                    match self.tokens.next() {
                        Some(Token::Endif) => {
                            self.ifs.pop();
                            return Ok(());
                        }
                        Some(Token::Ifdef | Token::Ifndef | Token::If) => {
                            self.ifs.push(Error::new(
                                self,
                                ErrorKind::UnterminatedIf(token.to_string()),
                            ));
                        }
                        _ => (),
                    }
                }
                Token::Newline => self.line += 1,
                Token::Comment(_, newlines) | Token::String(_, newlines) => {
                    self.line += newlines as i32;
                }
                _ => (),
            }
        }

        // got to end of token-stream without finding matching #endif
        Err(self.ifs.pop().unwrap())
    }

    pub fn start(&mut self) -> Result<(String, HashMap<String, Vec<Token>>), Vec<Error>> {
        let mut result = String::from("");
        let mut errors = Vec::new();

        while let Some(token) = self.tokens.next() {
            match token {
                Token::Hash if is_first_line_token(&result) => {
                    let _ = self.skip_whitespace();
                    let newlines = self.line;

                    let outcome = match self.tokens.next() {
                        Some(Token::Include) => match self.include() {
                            Ok(s) => Ok(result.push_str(&s)),
                            Err(e) => Err(e),
                        },
                        Some(Token::Define) => self.define(),
                        Some(Token::Undef) => self.undef(),
                        Some(token @ (Token::Ifdef | Token::Ifndef)) => self.ifdef(token),
                        Some(token @ Token::If) => self.if_expr(token),
                        Some(Token::Endif) => {
                            if self.ifs.is_empty() {
                                Err(Error::new(
                                    self,
                                    ErrorKind::Regular("Found '#endif' without matching '#if'"),
                                ))
                            } else {
                                self.ifs.pop();
                                Ok(())
                            }
                        }
                        Some(directive) => Err(Error::new(
                            self,
                            ErrorKind::InvalidDirective(directive.to_string()),
                        )),
                        None => Err(Error::new(
                            self,
                            ErrorKind::Regular("Expected preprocessor directive following '#'"),
                        )),
                    };

                    // if pp-directive more than one line, add marker for scanner
                    let pp_lines = self.line - newlines;
                    if pp_lines > 0 {
                        result.push_str(&format!("#line:{}\n", self.line));
                    }

                    if let Err(e) = outcome {
                        if let ErrorKind::Multiple(many_errors) = e.kind {
                            for e in many_errors {
                                errors.push(e)
                            }
                        } else {
                            errors.push(e)
                        }
                    } else if !matches!(self.tokens.peek(), Some(Token::Newline)) {
                        errors.push(Error::new(
                            self,
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
                        let expanded_replacement = self.replace_macros(&s, replacement.clone());
                        result.push_str(
                            &expanded_replacement
                                .into_iter()
                                .map(|t| t.to_string())
                                .collect::<String>(),
                        )
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
            errors.append(&mut self.ifs);
        }

        if errors.is_empty() {
            Ok((result, self.defines.clone()))
        } else {
            Err(errors)
        }
    }

    fn fold_until_newline(&mut self) -> Vec<Token> {
        let mut result = Vec::new();
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
                    if let Token::String(_, newline) | Token::Comment(_, newline) = t {
                        self.line += *newline as i32;
                    }
                    let token = self.tokens.next().unwrap();
                    result.push(token.clone());
                    prev_token = token;
                }
            }
        }
        result
    }
    // wrapper for easier access
    fn skip_whitespace(&mut self) -> Result<(), Error> {
        if let Err(_) = skip_whitespace(&mut self.tokens, &mut self.line) {
            Err(Error::new(
                self,
                ErrorKind::Regular("Expect whitespace after preprocessing directive"),
            ))
        } else {
            Ok(())
        }
    }
}

fn skip_whitespace(tokens: &mut Peekable<IntoIter<Token>>, line_index: &mut i32) -> Result<(), ()> {
    let mut found = false;

    while let Some(token) = tokens.peek() {
        match token {
            Token::Whitespace(_) => {
                tokens.next();
                found = true;
            }
            Token::Other('\\') => {
                let prev = tokens.next().unwrap();

                if let Some(Token::Newline) = tokens.peek() {
                    *line_index += 1;
                    tokens.next();
                } else {
                    insert_token(tokens, prev);
                    break;
                }
            }
            _ => break,
        }
    }
    if found {
        Ok(())
    } else {
        Err(())
    }
}
fn insert_token(tokens: &mut Peekable<IntoIter<Token>>, token: Token) {
    let mut start = vec![token];
    while let Some(t) = tokens.next() {
        start.push(t);
    }
    *tokens = start.into_iter().peekable();
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

    fn setup(input: &str) -> Preprocessor {
        let tokens = scan(input);

        Preprocessor::new("", input, tokens, None)
    }

    fn setup_macro_replacement(defined: HashMap<&str, &str>) -> HashMap<String, String> {
        let defined: HashMap<String, Vec<Token>> = defined
            .into_iter()
            .map(|(k, v)| (k.to_string(), scan(v)))
            .collect();
        let pp = Preprocessor::new("", "", Vec::new(), Some(defined.clone()));

        let mut result = HashMap::new();
        for (name, replace_list) in defined {
            result.insert(
                name.to_string(),
                pp.replace_macros(&name, replace_list)
                    .into_iter()
                    .map(|t| t.to_string())
                    .collect(),
            );
        }

        result
    }

    fn setup_whitespace_skip(input: &str) -> (Vec<Token>, bool) {
        let mut pp = setup(input);
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
        let (tokens, errors) = setup_whitespace_skip("  \\\n \n#include");
        let expected = scan("\n#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, false);
    }

    #[test]
    fn skips_multiline_whitespace2() {
        let (tokens, errors) = setup_whitespace_skip("  \\\n\n#include");
        let expected = scan("\n#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, false);
    }

    #[test]
    fn skips_multiline_whitespace3() {
        let (tokens, errors) = setup_whitespace_skip(" \\include");
        let expected = scan("\\include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, false);
    }

    #[test]
    fn skips_multiline_whitespace_error() {
        let (tokens, errors) = setup_whitespace_skip("\\\n#include");
        let expected = scan("#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, true);
    }

    #[test]
    fn skips_multiline_whitespace_error2() {
        let (tokens, errors) = setup_whitespace_skip("\\some\n#include");
        let expected = scan("\\some\n#include");

        assert_eq!(tokens, expected);
        assert_eq!(errors, true);
    }

    #[test]
    fn macro_replacements() {
        let actual = setup_macro_replacement(HashMap::from([
            ("num", "3"),
            ("foo", "num"),
            ("bar", "foo"),
        ]));
        let expected = HashMap::from([
            (String::from("num"), String::from("3")),
            (String::from("foo"), String::from("3")),
            (String::from("bar"), String::from("3")),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn macro_list_replacements() {
        let actual = setup_macro_replacement(HashMap::from([
            ("foo", "one two three"),
            ("some", "four foo six"),
            ("bar", "foo seven some"),
        ]));
        let expected = HashMap::from([
            (String::from("foo"), String::from("one two three")),
            (String::from("some"), String::from("four one two three six")),
            (
                String::from("bar"),
                String::from("one two three seven four one two three six"),
            ),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn cyclic_macros() {
        let actual = setup_macro_replacement(HashMap::from([("foo", "bar"), ("bar", "foo")]));
        let expected = HashMap::from([
            (String::from("foo"), String::from("foo")),
            (String::from("bar"), String::from("bar")),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn cyclic_macros2() {
        let actual = setup_macro_replacement(HashMap::from([("foo1", "bar"), ("bar", "foo2")]));
        let expected = HashMap::from([
            (String::from("foo1"), String::from("foo2")),
            (String::from("bar"), String::from("foo2")),
        ]);

        assert_eq!(actual, expected);
    }
}
