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
use std::path::{Path, PathBuf};
use std::vec::IntoIter;

struct IfDirective {
    location: Error,
    has_else: bool,
}

impl IfDirective {
    fn new(location: Error) -> Self {
        IfDirective { location, has_else: false }
    }
}

pub struct Preprocessor<'a> {
    tokens: Peekable<IntoIter<Token>>,
    raw_source: Vec<String>,
    line: i32,
    column: i32,
    filename: &'a Path,
    defines: HashMap<String, Vec<Token>>,
    ifs: Vec<IfDirective>,
    system_header_path: PathBuf,
}

impl<'a> Preprocessor<'a> {
    pub fn new(
        filename: &'a Path,
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
            filename,
            ifs: vec![],
            // WARN: only temporary absolute path. /include will be found via PATH env var.
            // Maybe has to be vector if there are multiple search paths
            system_header_path: PathBuf::from(
                "/Users/philipprados/documents/coding/Rust/wrecc/include/",
            ),
            defines: if let Some(defines) = pre_defines {
                defines
            } else {
                HashMap::new()
            },
        }
    }

    fn paste_header(&mut self, (file_path, data): (PathBuf, String)) -> Result<String, Error> {
        let (data, defines) = preprocess_included(&file_path, &data, self.defines.clone())
            .or_else(|e| Err(Error::new_multiple(e)))?;

        self.defines.extend(defines);

        let header_prologue = format!("#pro:{}\n", file_path.display());
        let header_epilogue = format!("#epi:{}\0", self.line_index());

        Ok(header_prologue + &data + &header_epilogue)
    }

    fn include(&mut self) -> Result<String, Error> {
        self.skip_whitespace()?;

        match self.tokens.next() {
            Some(Token::String(mut file, _)) => {
                file.remove(0);

                if let Some('"') = file.pop() {
                    let file_data = self.include_data(PathBuf::from(file), true)?;
                    self.paste_header(file_data)
                } else {
                    Err(Error::new(
                        self,
                        ErrorKind::Regular("Expected closing '\"' after header file"),
                    ))
                }
            }
            Some(Token::Other('<')) => {
                let file = self
                    .fold_until_token(Token::Other('>'))
                    .into_iter()
                    .map(|t| t.to_string())
                    .collect::<String>();
                let closing = self.tokens.next();

                if let Some(Token::Other('>')) = closing {
                    let file_data = self.include_data(PathBuf::from(file), false)?;
                    self.paste_header(file_data)
                } else {
                    Err(Error::new(
                        self,
                        ErrorKind::Regular("Expected closing '>' after header file"),
                    ))
                }
            }
            _ => Err(Error::new(
                self,
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            )),
        }
    }
    // first searches current directory (if search_local is set), otherwise searches system path
    // and returns the data it contains together with the filepath where it was found
    fn include_data(
        &self,
        file_path: PathBuf,
        search_local: bool,
    ) -> Result<(PathBuf, String), Error> {
        if search_local {
            let file_path = Path::new(&self.filename)
                .parent()
                .expect("empty filename")
                .join(&file_path);
            if let Ok(data) = fs::read_to_string(&file_path) {
                return Ok((file_path, data));
            }
        }
        let abs_system_path = self.system_header_path.join(&file_path);
        match fs::read_to_string(&abs_system_path) {
            Ok(data) => Ok((file_path, data)),
            Err(_) => Err(Error::new(
                self,
                ErrorKind::InvalidHeader(file_path.to_string_lossy().to_string()),
            )),
        }
    }
    fn define(&mut self) -> Result<(), Error> {
        self.skip_whitespace()?;

        match self.tokens.next().map(|t| t.as_ident()) {
            Some(Some(identifier)) => {
                let _ = self.skip_whitespace();
                let replace_with = self.fold_until_token(Token::Newline);
                let replace_with = trim_trailing_whitespace(replace_with);

                // same macro already exists but with different replacement-list
                if let Some(existing_replacement) = self.defines.get(&identifier) {
                    if existing_replacement != &replace_with {
                        return Err(Error::new(
                            self,
                            ErrorKind::Redefinition("macro", identifier),
                        ));
                    }
                }
                self.defines.insert(identifier, replace_with);
                Ok(())
            }
            _ => Err(Error::new(self, ErrorKind::InvalidMacroName)),
        }
    }
    fn replace_macros(&self, macro_name: &str, replace_list: Vec<Token>) -> Vec<Token> {
        replace_list
            .into_iter()
            .flat_map(|token| {
                match (token.to_string(), self.defines.get(&token.to_string())) {
                    (token_name, Some(replacement)) if token_name != macro_name => {
                        pad_whitespace(self.replace_macros(macro_name, replacement.clone()))
                    }
                    _ => {
                        // can't further replace if replacement is current macro name
                        vec![token]
                    }
                }
            })
            .collect()
    }
    fn undef(&mut self) -> Result<(), Error> {
        self.skip_whitespace()?;

        match self.tokens.next().map(|t| t.as_ident()) {
            Some(Some(identifier)) => {
                self.defines.remove(&identifier);
                Ok(())
            }
            _ => Err(Error::new(self, ErrorKind::InvalidMacroName)),
        }
    }
    fn ifdef(&mut self, if_kind: Token) -> Result<(), Error> {
        self.skip_whitespace()?;

        match self.tokens.next().map(|t| t.as_ident()) {
            Some(Some(identifier)) => {
                // TODO: should this be prior to whitespace check so that #endif still has matching #if?
                self.ifs.push(IfDirective::new(Error::new(
                    self,
                    ErrorKind::UnterminatedIf(if_kind.to_string()),
                )));

                match (&if_kind, self.defines.contains_key(&identifier)) {
                    (Token::Ifdef, true) | (Token::Ifndef, false) => Ok(()),
                    (Token::Ifdef, false) | (Token::Ifndef, true) => self.eval_else_branch(),
                    _ => unreachable!(),
                }
            }
            _ => Err(Error::new(self, ErrorKind::InvalidMacroName)),
        }
    }
    fn if_expr(&mut self, if_kind: Token) -> Result<(), Error> {
        self.ifs.push(IfDirective::new(Error::new(
            self,
            ErrorKind::UnterminatedIf(if_kind.to_string()),
        )));

        self.skip_whitespace()?;

        match self.eval_cond()? {
            true => Ok(()),
            false => self.eval_else_branch(),
        }
    }
    fn conditional_block(&mut self, token: Token) -> Result<(), Error> {
        if self.ifs.is_empty() {
            Err(Error::new(self, ErrorKind::MissingIf(token.to_string())))
        } else {
            let matching_if = self.ifs.last_mut().unwrap();

            match (matching_if.has_else, token) {
                (true, Token::Elif) => Err(Error::new(self, ErrorKind::ElifAfterElse)),
                (false, Token::Elif) => self.skip_branch(true).map(|_| ()),
                (true, Token::Else) => Err(Error::new(self, ErrorKind::DuplicateElse)),
                (false, Token::Else) => {
                    matching_if.has_else = true;
                    self.skip_branch(true).map(|_| ())
                }
                (_, Token::Endif) => {
                    self.ifs.pop();
                    Ok(())
                }
                _ => unreachable!("not conditional block token"),
            }
        }
    }

    // skips branch until another conditional block token that must be evaluated is reached
    fn eval_else_branch(&mut self) -> Result<(), Error> {
        loop {
            match self.skip_branch(false)? {
                Token::Elif => {
                    if self.eval_cond()? {
                        return Ok(());
                    }
                }
                Token::Else | Token::Endif => {
                    return Ok(());
                }
                _ => unreachable!("not #if token"),
            }
        }
    }

    fn eval_cond(&mut self) -> Result<bool, Error> {
        let cond = self.fold_until_token(Token::Newline);
        let cond = self.replace_define_expr(cond)?;

        if cond.is_empty() {
            return Err(Error::new(
                self,
                ErrorKind::Regular("'#if' directive expects expression"),
            ));
        }

        match self.pp_const_value(cond)? {
            0 => Ok(false),
            _ => Ok(true),
        }
    }

    fn pp_const_value(&self, cond: String) -> Result<i64, Error> {
        let tokens = Scanner::new(self.filename, &cond)
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
                    match cond.next().map(|t| t.as_ident()) {
                        Some(Some(identifier)) => {
                            let replacement = if self.defines.contains_key(&identifier) {
                                Token::Other('1')
                            } else {
                                Token::Other('0')
                            };
                            let replacement = pad_whitespace(vec![replacement]);

                            result.extend(replacement);

                            let _ = skip_whitespace(&mut cond, &mut self.line);
                            if open_paren && !matches!(cond.next(), Some(Token::Other(')'))) {
                                return Err(Error::new(
                                    self,
                                    ErrorKind::Regular("Expect closing ')' after 'defined'"),
                                ));
                            }
                        }
                        _ => {
                            return Err(Error::new(
                                self,
                                ErrorKind::Regular("Expect identifier after 'defined'-operator"),
                            ))
                        }
                    }
                }
                ident if ident.as_ident().is_some() => {
                    let identifier = ident.as_ident().unwrap();

                    // if ident is defined replace it
                    if let Some(replacement) = self.defines.get(&identifier) {
                        let expanded_replacement =
                            self.replace_macros(&identifier, replacement.clone());
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
                if let Some(_) = token.as_ident() {
                    // hacky: insert whitespace so doesnt get appended to existing number
                    " 0 ".to_string()
                } else {
                    token.to_string()
                }
            })
            .collect();

        Ok(result)
    }
    fn skip_branch(&mut self, skip_to_end: bool) -> Result<Token, Error> {
        let matching_if = self.ifs.len();

        while let Some(token) = self.tokens.next() {
            match token {
                Token::Hash => {
                    let _ = self.skip_whitespace();
                    match self.tokens.next() {
                        Some(Token::Endif) if self.ifs.len() == matching_if => {
                            self.ifs.pop();
                            return Ok(Token::Endif);
                        }
                        Some(Token::Endif) => {
                            self.ifs.pop();
                        }
                        Some(token @ (Token::Elif | Token::Else)) => {
                            let if_directive = self.ifs.last_mut().unwrap();
                            match (if_directive.has_else, &token) {
                                (true, Token::Elif) => {
                                    return Err(Error::new(self, ErrorKind::ElifAfterElse));
                                }
                                (true, Token::Else) => {
                                    return Err(Error::new(self, ErrorKind::DuplicateElse));
                                }
                                (false, Token::Else) => {
                                    if_directive.has_else = true;
                                }
                                _ => (),
                            }
                            if !skip_to_end {
                                return Ok(token);
                            }
                        }
                        Some(Token::Ifdef | Token::Ifndef | Token::If) => {
                            self.ifs.push(IfDirective::new(Error::new(
                                self,
                                ErrorKind::UnterminatedIf(token.to_string()),
                            )));
                        }
                        _ => (),
                    }
                }
                Token::Newline => self.line += 1,
                token => {
                    if let Some(newlines) = token.get_newlines() {
                        self.line += newlines;
                    }
                }
            }
        }

        // got to end of token-stream without finding matching #endif
        Err(self.ifs.pop().unwrap().location)
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
                        Some(token @ (Token::Elif | Token::Else | Token::Endif)) => {
                            self.conditional_block(token)
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
                ident if ident.as_ident().is_some() => {
                    let identifier = ident.as_ident().unwrap();

                    if let Some(replacement) = self.defines.get(&identifier) {
                        let expanded_replacement =
                            pad_whitespace(self.replace_macros(&identifier, replacement.clone()));

                        result.push_str(
                            &expanded_replacement
                                .into_iter()
                                .map(|t| t.to_string())
                                .collect::<String>(),
                        )
                    } else {
                        result.push_str(&identifier)
                    }
                }
                token => {
                    if let Some(newlines) = token.get_newlines() {
                        self.line += newlines;
                    }
                    result.push_str(&token.to_string())
                }
            }
        }

        if !self.ifs.is_empty() {
            errors.append(&mut self.ifs.iter().map(|i| i.location.clone()).collect());
        }

        if errors.is_empty() {
            Ok((result, self.defines.clone()))
        } else {
            Err(errors)
        }
    }

    // combines tokens until either an unescaped newline is reached or the token is found
    fn fold_until_token(&mut self, end: Token) -> Vec<Token> {
        let mut result = Vec::new();
        let mut prev_token = Token::Newline;

        while let Some(token) = self.tokens.peek() {
            match (&prev_token, token) {
                (Token::Other('\\'), Token::Newline) => {
                    prev_token = self.tokens.next().unwrap();
                    result.pop();
                    self.line += 1;
                }
                (_, Token::Newline) => break,
                (_, token) if token == &end => break,
                (.., t) => {
                    if let Some(newlines) = t.get_newlines() {
                        self.line += newlines;
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

// surrounds a list of tokens with additional whitespace to avoid them being glued together during stringification
fn pad_whitespace(tokens: Vec<Token>) -> Vec<Token> {
    let mut replaced = vec![Token::Whitespace(" ".to_string())];
    replaced.extend(tokens);
    replaced.push(Token::Whitespace(" ".to_string()));
    replaced
}

fn trim_trailing_whitespace(mut tokens: Vec<Token>) -> Vec<Token> {
    while let Some(Token::Whitespace(_)) = tokens.last() {
        tokens.pop();
    }
    tokens
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

impl<'a> Location for Preprocessor<'a> {
    fn line_index(&self) -> i32 {
        self.line
    }
    fn column(&self) -> i32 {
        self.column
    }
    fn line_string(&self) -> String {
        self.raw_source[(self.line - 1) as usize].clone()
    }
    fn filename(&self) -> PathBuf {
        self.filename.into()
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

        Preprocessor::new(Path::new(""), input, tokens, None)
    }

    fn setup_complete(input: &str) -> String {
        setup(input).start().unwrap().0
    }

    fn setup_complete_err(input: &str) -> Vec<ErrorKind> {
        if let Err(e) = setup(input).start() {
            e.into_iter().map(|e| e.kind).collect()
        } else {
            unreachable!()
        }
    }

    fn setup_macro_replacement(defined: HashMap<&str, &str>) -> HashMap<String, String> {
        let defined: HashMap<String, Vec<Token>> = defined
            .into_iter()
            .map(|(k, v)| (k.to_string(), scan(v)))
            .collect();
        let pp = Preprocessor::new(Path::new(""), "", Vec::new(), Some(defined.clone()));

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
            (String::from("foo"), String::from(" 3 ")),
            (String::from("bar"), String::from("  3  ")),
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
            (
                String::from("some"),
                String::from("four  one two three  six"),
            ),
            (
                String::from("bar"),
                String::from(" one two three  seven  four  one two three  six "),
            ),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn cyclic_macros() {
        let actual = setup_macro_replacement(HashMap::from([("foo", "bar"), ("bar", "foo")]));
        let expected = HashMap::from([
            (String::from("foo"), String::from(" foo ")),
            (String::from("bar"), String::from(" bar ")),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn cyclic_macros2() {
        let actual = setup_macro_replacement(HashMap::from([("foo1", "bar"), ("bar", "foo2")]));
        let expected = HashMap::from([
            (String::from("foo1"), String::from(" foo2 ")),
            (String::from("bar"), String::from("foo2")),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn fold_until_newline_escaped() {
        let actual = setup("1 2   \\\n\\3\n   \\\nwhat").fold_until_token(Token::Newline);
        let expected = scan("1 2   \\3");

        assert_eq!(actual, expected);
    }

    #[test]
    fn fold_until_newline_escaped2() {
        let actual = setup("1 2   \\\n\\\n3\n   \\\nwhat").fold_until_token(Token::Newline);
        let expected = scan("1 2   3");

        assert_eq!(actual, expected);
    }

    #[test]
    fn trim_trailing_whitespace_none() {
        let actual = trim_trailing_whitespace(scan("1 2"));
        let expected = scan("1 2");

        assert_eq!(actual, expected);
    }

    #[test]
    fn trim_trailing_whitespace_test() {
        let actual = trim_trailing_whitespace(scan("1 2  "));
        let expected = scan("1 2");

        assert_eq!(actual, expected);
    }
    #[test]
    fn trim_trailing_whitespace_multiple() {
        let input = vec![
            Token::Ident("some".to_string()),
            Token::Whitespace("  ".to_string()),
            Token::Other('1'),
            Token::Whitespace("  ".to_string()),
            Token::Whitespace(" ".to_string()),
        ];
        let actual = trim_trailing_whitespace(input);
        let expected = scan("some  1");

        assert_eq!(actual, expected);
    }

    #[test]
    fn skips_multiple_ifs() {
        let actual = setup_complete(
            "
#if 0
#if 1
char s = 'l';
#endif
char s = 'i';
#endif
char empty = 0;
",
        );
        let expected = "\n#line:7\n\nchar empty = 0;\n";

        assert_eq!(actual, expected);
    }
    #[test]
    fn skips_nested_ifs() {
        let actual = setup_complete(
            "
#if 1
#if 0
char s = 'l';
#endif
char s = 'i';
#endif
char empty = 0;
",
        );
        let expected = "\n\n#line:5\n\nchar s = 'i';\n\nchar empty = 0;\n";

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_ifs_single_endif() {
        let actual = setup_complete_err(
            "
#if 1
#if 0
char s = 'l';
char s = 'i';
#endif
char empty = 0;
",
        );

        assert!(matches!(actual[..], [ErrorKind::UnterminatedIf(_)]));
    }

    #[test]
    fn if_else() {
        let actual = setup_complete(
            "
#if 1
char s = 'l';
#else
char s = 'o';
#endif
#ifdef foo
char c = 1;
#else
char c = 2;
#endif
",
        );
        let expected = "\n\nchar s = 'l';\n#line:6\n\n#line:9\n\nchar c = 2;\n\n";

        assert_eq!(actual, expected);
    }

    #[test]
    fn if_elif() {
        let actual = setup_complete(
            "
#define foo
#if !defined foo
char s = 'l';
#elif 1
char s = 'o';
#elif !foo
char s = 's';
#endif
",
        );
        let expected = "\n\n#line:5\n\nchar s = 'o';\n#line:9\n\n";

        assert_eq!(actual, expected);
    }

    #[test]
    fn missing_ifs() {
        let actual = setup_complete_err(
            "
#if 1
char s = 'l';
#else
char s = 'i';
#endif
#elif nothing
#else
#endif
#ifndef foo
char empty = 0;
",
        );

        assert!(matches!(
            actual[..],
            [
                ErrorKind::MissingIf(_),
                ErrorKind::MissingIf(_),
                ErrorKind::MissingIf(_),
                ErrorKind::UnterminatedIf(_),
            ]
        ));
    }
    #[test]
    fn duplicate_else() {
        let actual = setup_complete_err(
            "
#if 1
char s = 's';
#if 1
#elif 0
char *s = 'o';
#else
char *s = 'n';
#else
char *s = 'm';
#endif
#endif
",
        );

        assert!(matches!(actual[..], [ErrorKind::DuplicateElse]));
    }

    #[test]
    fn nested_duplicate_else() {
        let actual = setup_complete_err(
            "
#if 1
char *s = 'if';
#else
char *s = 'else1';

#if 1
#else
char *s = 'elif';
#elif 0
#else
char *s = 'else2';
#endif

#else
#endif
",
        );

        assert!(matches!(
            actual[..],
            [
                ErrorKind::ElifAfterElse,
                ErrorKind::DuplicateElse,
                ErrorKind::DuplicateElse
            ]
        ));
    }
    #[test]
    fn skipped_if() {
        let actual = setup_complete(
            "
#if 0
#else
int only_this;
#endif
",
        );
        let expected = "\n#line:3\n\nint only_this;\n\n";

        assert_eq!(actual, expected);
    }

    #[test]
    fn keywords_as_idents() {
        let actual = setup_complete(
            "
#if include != 0
int skip_here;
#elif !defined(elif) + define
int only_this;
#endif
",
        );
        let expected = "\n#line:4\n\nint only_this;\n\n";

        assert_eq!(actual, expected);
    }
}
