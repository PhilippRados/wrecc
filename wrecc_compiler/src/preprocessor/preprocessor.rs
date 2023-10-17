use crate::compiler::common::error::*;
use crate::compiler::scanner::*;
use crate::compiler::wrecc_parser::{double_peek::*, parser::*};

use crate::preprocessor::scanner::{Token, TokenKind};
use crate::PPScanner;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

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
    tokens: DoublePeek<Token>,
    raw_source: Vec<String>,

    // current file being preprocessed
    filename: &'a Path,

    // #define's mapping identifier to list of tokens until newline
    defines: HashMap<String, Vec<TokenKind>>,

    // list of #if directives with last one being the most deeply nested
    ifs: Vec<IfDirective>,

    // path to custom system header files
    system_header_path: PathBuf,
}

impl<'a> Preprocessor<'a> {
    pub fn new(
        filename: &'a Path,
        input: &'a str,
        tokens: Vec<Token>,
        pre_defines: Option<HashMap<String, Vec<TokenKind>>>,
    ) -> Self {
        Preprocessor {
            tokens: DoublePeek::new(tokens),
            raw_source: input
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
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

    fn paste_header(
        &mut self,
        token: Token,
        (file_path, data): (PathBuf, String),
    ) -> Result<String, Error> {
        let (data, defines) = preprocess_included(&file_path, &data, self.defines.clone())
            .map_err(Error::new_multiple)?;

        self.defines.extend(defines);

        let header_prologue = format!("#pro:{}\n", file_path.display());
        let header_epilogue = format!("#epi:{}\0", token.line);

        Ok(header_prologue + &data + &header_epilogue)
    }

    fn include(&mut self, directive: Token) -> Result<String, Error> {
        self.skip_whitespace()?;

        if let Some(token) = self.tokens.next() {
            match token.kind.clone() {
                TokenKind::String(mut file) => {
                    file.remove(0);

                    if let Some('"') = file.pop() {
                        let file_data = self.include_data(&token, PathBuf::from(file), true)?;
                        self.paste_header(token, file_data)
                    } else {
                        Err(Error::new(
                            &self.location(&token),
                            ErrorKind::Regular("Expected closing '\"' after header file"),
                        ))
                    }
                }
                TokenKind::Other('<') => {
                    let file = self
                        .fold_until_token(TokenKind::Other('>'))
                        .into_iter()
                        .map(|t| t.kind.to_string())
                        .collect::<String>();
                    let closing = self.tokens.next().map(|t| t.kind);

                    if let Some(TokenKind::Other('>')) = closing {
                        let file_data = self.include_data(&token, PathBuf::from(file), false)?;
                        self.paste_header(token, file_data)
                    } else {
                        Err(Error::new(
                            &self.location(&token),
                            ErrorKind::Regular("Expected closing '>' after header file"),
                        ))
                    }
                }
                _ => Err(Error::new(
                    &self.location(&token),
                    ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
                )),
            }
        } else {
            Err(Error::new(
                &self.location(&directive),
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            ))
        }
    }
    // first searches current directory (if search_local is set), otherwise searches system path
    // and returns the data it contains together with the filepath where it was found
    fn include_data(
        &self,
        token: &Token,
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
        match fs::read_to_string(abs_system_path) {
            Ok(data) => Ok((file_path, data)),
            Err(_) => Err(Error::new(
                &self.location(token),
                ErrorKind::InvalidHeader(file_path.to_string_lossy().to_string()),
            )),
        }
    }
    fn define(&mut self, directive: Token) -> Result<(), Error> {
        self.skip_whitespace()?;

        if let Some(token) = self.tokens.next() {
            match token.kind.as_ident() {
                Some(identifier) => {
                    let _ = self.skip_whitespace();
                    let replace_with = self
                        .fold_until_token(TokenKind::Newline)
                        .into_iter()
                        .map(|t| t.kind)
                        .collect();
                    let replace_with = trim_trailing_whitespace(replace_with);

                    // same macro already exists but with different replacement-list
                    if let Some(existing_replacement) = self.defines.get(&identifier) {
                        if existing_replacement != &replace_with {
                            return Err(Error::new(
                                &self.location(&token),
                                ErrorKind::Redefinition("macro", identifier),
                            ));
                        }
                    }
                    self.defines.insert(identifier, replace_with);
                    Ok(())
                }
                _ => Err(Error::new(
                    &self.location(&token),
                    ErrorKind::InvalidMacroName,
                )),
            }
        } else {
            Err(Error::new(
                &self.location(&directive),
                ErrorKind::InvalidMacroName,
            ))
        }
    }
    fn replace_macros(&self, macro_name: &str, replace_list: Vec<TokenKind>) -> Vec<TokenKind> {
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
    fn undef(&mut self, directive: Token) -> Result<(), Error> {
        self.skip_whitespace()?;

        if let Some(token) = self.tokens.next() {
            match token.kind.as_ident() {
                Some(identifier) => {
                    self.defines.remove(&identifier);
                    Ok(())
                }
                _ => Err(Error::new(
                    &self.location(&token),
                    ErrorKind::InvalidMacroName,
                )),
            }
        } else {
            Err(Error::new(
                &self.location(&directive),
                ErrorKind::InvalidMacroName,
            ))
        }
    }
    fn ifdef(&mut self, if_kind: Token) -> Result<(), Error> {
        self.skip_whitespace()?;

        if let Some(token) = self.tokens.next() {
            match token.kind.as_ident() {
                Some(identifier) => {
                    // TODO: should this be prior to whitespace check so that #endif still has matching #if?
                    self.ifs.push(IfDirective::new(Error::new(
                        &self.location(&if_kind),
                        ErrorKind::UnterminatedIf(if_kind.kind.to_string()),
                    )));

                    match (&if_kind.kind, self.defines.contains_key(&identifier)) {
                        (TokenKind::Ifdef, true) | (TokenKind::Ifndef, false) => Ok(()),
                        (TokenKind::Ifdef, false) | (TokenKind::Ifndef, true) => {
                            self.eval_else_branch()
                        }
                        _ => unreachable!(),
                    }
                }
                _ => Err(Error::new(
                    &self.location(&token),
                    ErrorKind::InvalidMacroName,
                )),
            }
        } else {
            Err(Error::new(
                &self.location(&if_kind),
                ErrorKind::InvalidMacroName,
            ))
        }
    }
    fn if_expr(&mut self, if_kind: Token) -> Result<(), Error> {
        self.ifs.push(IfDirective::new(Error::new(
            &self.location(&if_kind),
            ErrorKind::UnterminatedIf(if_kind.kind.to_string()),
        )));

        self.skip_whitespace()?;

        match self.eval_cond(if_kind)? {
            true => Ok(()),
            false => self.eval_else_branch(),
        }
    }
    fn conditional_block(&mut self, token: Token) -> Result<(), Error> {
        if self.ifs.is_empty() {
            Err(Error::new(
                &self.location(&token),
                ErrorKind::MissingIf(token.kind.to_string()),
            ))
        } else {
            let matching_if = self.ifs.last_mut().unwrap();

            match (matching_if.has_else, &token.kind) {
                (true, TokenKind::Elif) => {
                    Err(Error::new(&self.location(&token), ErrorKind::ElifAfterElse))
                }
                (false, TokenKind::Elif) => self.skip_branch(true).map(|_| ()),
                (true, TokenKind::Else) => {
                    Err(Error::new(&self.location(&token), ErrorKind::DuplicateElse))
                }
                (false, TokenKind::Else) => {
                    matching_if.has_else = true;
                    self.skip_branch(true).map(|_| ())
                }
                (_, TokenKind::Endif) => {
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
            let token = self.skip_branch(false)?;
            match token.kind {
                TokenKind::Elif => {
                    if self.eval_cond(token)? {
                        return Ok(());
                    }
                }
                TokenKind::Else | TokenKind::Endif => {
                    return Ok(());
                }
                _ => unreachable!("not #if token"),
            }
        }
    }

    fn eval_cond(&mut self, if_kind: Token) -> Result<bool, Error> {
        let cond = self.fold_until_token(TokenKind::Newline);
        let cond = self.replace_define_expr(cond)?;

        if cond.is_empty() || cond.chars().all(char::is_whitespace) {
            return Err(Error::new(
                &self.location(&if_kind),
                ErrorKind::MissingExpression(if_kind.kind.to_string()),
            ));
        }

        match self.pp_const_value(if_kind, cond)? {
            0 => Ok(false),
            _ => Ok(true),
        }
    }

    fn pp_const_value(&self, if_kind: Token, cond: String) -> Result<i64, Error> {
        let tokens = Scanner::new(self.filename, &cond)
            .scan_token()
            .map_err(|errs| {
                Error::new_multiple(
                    errs.into_iter()
                        .map(|e| Error::new(&self.location(&if_kind), e.kind))
                        .collect(),
                )
            })?;
        let mut parser = Parser::new(tokens);
        let mut expr = parser
            .expression()
            .map_err(|e| Error::new(&self.location(&if_kind), e.kind))?;

        if !parser.is_empty() {
            return Err(Error::new(
                &self.location(&if_kind),
                ErrorKind::Regular("Trailing tokens in preprocessor expression"),
            ));
        }

        let value = expr.preprocessor_constant(&self.location(&if_kind))?;

        Ok(value)
    }

    fn replace_define_expr(&mut self, cond: Vec<Token>) -> Result<String, Error> {
        let mut result = Vec::with_capacity(cond.len());
        let mut cond = DoublePeek::new(cond);

        while let Some(token) = cond.next() {
            match &token.kind {
                TokenKind::Defined => {
                    skip_whitespace(&mut cond);

                    let open_paren = if let Ok(TokenKind::Other('(')) = cond.peek().map(|t| &t.kind)
                    {
                        cond.next()
                    } else {
                        None
                    };

                    skip_whitespace(&mut cond);
                    if let Some(token) = cond.next() {
                        match token.kind.as_ident() {
                            Some(identifier) => {
                                let replacement = if self.defines.contains_key(&identifier) {
                                    TokenKind::Other('1')
                                } else {
                                    TokenKind::Other('0')
                                };
                                let replacement = pad_whitespace(vec![replacement]);

                                result.extend(replacement);

                                skip_whitespace(&mut cond);

                                if let Some(open_paren) = open_paren {
                                    if !matches!(
                                        cond.next(),
                                        Some(Token { kind: TokenKind::Other(')'), .. })
                                    ) {
                                        return Err(Error::new(
                                            &self.location(&open_paren),
                                            ErrorKind::Regular(
                                                "Expect matching closing ')' after 'defined'",
                                            ),
                                        ));
                                    }
                                }
                            }
                            _ => {
                                return Err(Error::new(
                                    &self.location(&token),
                                    ErrorKind::Regular(
                                        "Expect identifier after 'defined'-operator",
                                    ),
                                ))
                            }
                        }
                    } else {
                        return Err(Error::new(
                            &self.location(&token),
                            ErrorKind::Regular("Expect identifier after 'defined'-operator"),
                        ));
                    }
                }
                _ => {
                    if let Some(identifier) = token.kind.as_ident() {
                        // if ident is defined replace it
                        if let Some(replacement) = self.defines.get(&identifier) {
                            let expanded_replacement =
                                self.replace_macros(&identifier, replacement.clone());
                            result.extend(expanded_replacement)
                        } else {
                            result.push(token.kind)
                        }
                    } else {
                        result.push(token.kind)
                    }
                }
            }
        }
        // replace all identifiers with 0
        let result = result
            .into_iter()
            .map(|token| {
                if token.as_ident().is_some() {
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
            if let TokenKind::Hash = token.kind {
                let _ = self.skip_whitespace();

                if let Some(token) = self.tokens.next() {
                    match token.kind {
                        TokenKind::Endif if self.ifs.len() == matching_if => {
                            self.ifs.pop();
                            return Ok(token);
                        }
                        TokenKind::Endif => {
                            self.ifs.pop();
                        }
                        TokenKind::Elif | TokenKind::Else => {
                            let if_directive = self.ifs.last_mut().unwrap();
                            match (if_directive.has_else, &token.kind) {
                                (true, TokenKind::Elif) => {
                                    return Err(Error::new(
                                        &self.location(&token),
                                        ErrorKind::ElifAfterElse,
                                    ));
                                }
                                (true, TokenKind::Else) => {
                                    return Err(Error::new(
                                        &self.location(&token),
                                        ErrorKind::DuplicateElse,
                                    ));
                                }
                                (false, TokenKind::Else) => {
                                    if_directive.has_else = true;
                                }
                                _ => (),
                            }
                            if !skip_to_end {
                                return Ok(token);
                            }
                        }
                        TokenKind::Ifdef | TokenKind::Ifndef | TokenKind::If => {
                            self.ifs.push(IfDirective::new(Error::new(
                                &self.location(&token),
                                ErrorKind::UnterminatedIf(token.kind.to_string()),
                            )));
                        }
                        _ => (),
                    }
                }
            }
        }

        // got to end of token-stream without finding matching #endif
        Err(self.ifs.pop().unwrap().location)
    }

    pub fn start(mut self) -> Result<(String, HashMap<String, Vec<TokenKind>>), Vec<Error>> {
        let mut result = String::from("");
        let mut errors = Vec::new();
        let mut prev_line = 1;

        while let Some(token) = self.tokens.next() {
            match token.kind {
                TokenKind::Hash if is_first_line_token(&result) => {
                    let _ = self.skip_whitespace();

                    let outcome = if let Some(directive) = self.tokens.next() {
                        match directive.kind {
                            TokenKind::Include => match self.include(directive) {
                                Ok(s) => Ok(result.push_str(&s)),
                                Err(e) => Err(e),
                            },
                            TokenKind::Define => self.define(directive),
                            TokenKind::Undef => self.undef(directive),
                            TokenKind::Ifdef | TokenKind::Ifndef => self.ifdef(directive),
                            TokenKind::If => self.if_expr(directive),
                            TokenKind::Elif | TokenKind::Else | TokenKind::Endif => {
                                self.conditional_block(directive)
                            }
                            _ => Err(Error::new(
                                &self.location(&directive),
                                ErrorKind::InvalidDirective(directive.kind.to_string()),
                            )),
                        }
                    } else {
                        Err(Error::new(
                            &self.location(&token),
                            ErrorKind::Regular("Expected preprocessor directive following '#'"),
                        ))
                    };

                    if let Err(e) = outcome {
                        if let ErrorKind::Multiple(many_errors) = e.kind {
                            for e in many_errors {
                                errors.push(e)
                            }
                        } else {
                            errors.push(e)
                        }
                    } else {
                        if let Ok(peeked) = self.tokens.peek() {
                            if !matches!(peeked.kind, TokenKind::Newline) {
                                errors.push(Error::new(
                                    &self.location(peeked),
                                    ErrorKind::Regular(
                                        "Found trailing tokens after preprocessor directive",
                                    ),
                                ))
                            }
                        }
                    }
                }
                TokenKind::Newline => {
                    if (token.line - prev_line) > 1 {
                        result.push_str(&format!("#line:{}\n", token.line));
                    }
                    prev_line = token.line;
                    result.push('\n');
                }
                _ => {
                    if let Some(identifier) = token.kind.as_ident() {
                        if let Some(replacement) = self.defines.get(&identifier) {
                            let expanded_replacement = pad_whitespace(
                                self.replace_macros(&identifier, replacement.clone()),
                            );

                            result.push_str(
                                &expanded_replacement
                                    .into_iter()
                                    .map(|t| t.to_string())
                                    .collect::<String>(),
                            )
                        } else {
                            result.push_str(&identifier)
                        }
                    } else {
                        result.push_str(&token.kind.to_string())
                    }
                }
            }
        }

        if !self.ifs.is_empty() {
            errors.append(&mut self.ifs.iter().map(|i| i.location.clone()).collect());
        }

        if errors.is_empty() {
            Ok((result, self.defines))
        } else {
            Err(errors)
        }
    }

    // combines tokens until either an unescaped newline is reached or the token is found
    fn fold_until_token(&mut self, end: TokenKind) -> Vec<Token> {
        let mut result = Vec::new();

        while let Ok(token) = self.tokens.peek() {
            match &token.kind {
                TokenKind::Newline => break,
                token if token == &end => break,
                _ => {
                    result.push(self.tokens.next().unwrap());
                }
            }
        }
        result
    }

    // wrapper for easier access
    fn skip_whitespace(&mut self) -> Result<(), Error> {
        if !skip_whitespace(&mut self.tokens) {
            if let Ok(token) = self.tokens.peek() {
                Err(Error::new(
                    &self.location(token),
                    ErrorKind::Regular("Expect whitespace after preprocessing directive"),
                ))
            } else {
                Err(Error::eof("Expected whitespace"))
            }
        } else {
            Ok(())
        }
    }
    // helper function since token holds column and line information but can't hold filename info
    fn location(&self, token: &Token) -> Loc {
        Loc {
            line: token.line,
            column: token.column,
            line_string: self.raw_source[(token.line - 1) as usize].clone(),
            filename: self.filename.into(),
        }
    }
}

// Preprocesses given input file if input file nested inside root-file
fn preprocess_included(
    filename: &Path,
    source: &str,
    defines: HashMap<String, Vec<TokenKind>>,
) -> Result<(String, HashMap<String, Vec<TokenKind>>), Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens, Some(defines)).start()
}

// surrounds a list of tokens with additional whitespace to avoid them being glued together during stringification
fn pad_whitespace(tokens: Vec<TokenKind>) -> Vec<TokenKind> {
    let mut replaced = vec![TokenKind::Whitespace(" ".to_string())];
    replaced.extend(tokens);
    replaced.push(TokenKind::Whitespace(" ".to_string()));
    replaced
}

fn trim_trailing_whitespace(mut tokens: Vec<TokenKind>) -> Vec<TokenKind> {
    while let Some(TokenKind::Whitespace(_)) = tokens.last() {
        tokens.pop();
    }
    tokens
}

fn skip_whitespace(tokens: &mut DoublePeek<Token>) -> bool {
    if let Ok(Token { kind: TokenKind::Whitespace(_), .. }) = tokens.peek() {
        tokens.next();
        true
    } else {
        false
    }
}

struct Loc {
    line: i32,
    column: i32,
    line_string: String,
    filename: PathBuf,
}
impl Location for Loc {
    fn line_index(&self) -> i32 {
        self.line
    }
    fn column(&self) -> i32 {
        self.column
    }
    fn line_string(&self) -> String {
        self.line_string.clone()
    }
    fn filename(&self) -> PathBuf {
        self.filename.clone()
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

    fn scan(input: &str) -> Vec<TokenKind> {
        PPScanner::new(input)
            .scan_token()
            .into_iter()
            .map(|t| t.kind)
            .collect()
    }

    fn setup(input: &str) -> Preprocessor {
        let tokens = PPScanner::new(input).scan_token();

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
        let defined: HashMap<String, Vec<TokenKind>> = defined
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

    fn setup_whitespace_skip(input: &str) -> (Vec<TokenKind>, bool) {
        let mut pp = setup(input);
        let result = pp.skip_whitespace();

        (
            pp.tokens.to_vec().into_iter().map(|t| t.kind).collect(),
            result.is_err(),
        )
    }
    fn setup_fold_until_newline(input: &str) -> Vec<TokenKind> {
        setup(input)
            .fold_until_token(TokenKind::Newline)
            .into_iter()
            .map(|t| t.kind)
            .collect()
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
        let actual = setup_fold_until_newline("1 2   \\\n\\3\n   \\\nwhat");
        let expected = scan("1 2   \\3");

        assert_eq!(actual, expected);
    }

    #[test]
    fn fold_until_newline_escaped2() {
        let actual = setup_fold_until_newline("1 2   \\\n\\\n3\n   \\\nwhat");
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
            TokenKind::Ident("some".to_string()),
            TokenKind::Whitespace("  ".to_string()),
            TokenKind::Other('1'),
            TokenKind::Whitespace("  ".to_string()),
            TokenKind::Whitespace(" ".to_string()),
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
