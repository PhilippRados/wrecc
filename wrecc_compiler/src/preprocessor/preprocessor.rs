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
// same as preprocessor::scanner::Token but with added filename since scanner doesn't that information
#[derive(Clone)]
pub struct PPToken {
    pub kind: TokenKind,
    pub column: i32,
    pub line: i32,
    pub line_string: String,
    pub filename: PathBuf,
}
impl PPToken {
    fn from(token: &Token, filename: &Path) -> Self {
        PPToken {
            filename: filename.into(),
            kind: token.kind.clone(),
            column: token.column,
            line: token.line,
            line_string: token.line_string.clone(),
        }
    }
}
impl Location for PPToken {
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

pub struct Preprocessor<'a> {
    tokens: DoublePeek<Token>,

    // current file being preprocessed
    filename: &'a Path,

    // #define's mapping identifier to list of tokens until newline
    defines: HashMap<String, Vec<Token>>,

    // list of #if directives with last one being the most deeply nested
    ifs: Vec<IfDirective>,

    // path to custom system header files
    system_header_path: PathBuf,
}

impl<'a> Preprocessor<'a> {
    pub fn new(
        filename: &'a Path,
        tokens: Vec<Token>,
        pre_defines: Option<HashMap<String, Vec<Token>>>,
    ) -> Self {
        Preprocessor {
            tokens: DoublePeek::new(tokens),
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
        (file_path, data): (PathBuf, String),
    ) -> Result<Vec<PPToken>, Error> {
        let (data, defines) = preprocess_included(&file_path, data, self.defines.clone())
            .map_err(Error::new_multiple)?;

        self.defines.extend(defines);

        Ok(data)
    }

    fn include(&mut self, directive: Token) -> Result<Vec<PPToken>, Error> {
        self.skip_whitespace()?;

        if let Some(token) = self.tokens.next() {
            match token.kind.clone() {
                TokenKind::String(mut file) => {
                    file.remove(0);

                    if let Some('"') = file.pop() {
                        let file_data = self.include_data(token, PathBuf::from(file), true)?;
                        self.paste_header(file_data)
                    } else {
                        Err(Error::new(
                            &PPToken::from(&token, self.filename),
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
                        let file_data = self.include_data(token, PathBuf::from(file), false)?;
                        self.paste_header(file_data)
                    } else {
                        Err(Error::new(
                            &PPToken::from(&token, self.filename),
                            ErrorKind::Regular("Expected closing '>' after header file"),
                        ))
                    }
                }
                _ => Err(Error::new(
                    &PPToken::from(&token, self.filename),
                    ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
                )),
            }
        } else {
            Err(Error::new(
                &PPToken::from(&directive, self.filename),
                ErrorKind::Regular("Expected opening '<' or '\"' after include directive"),
            ))
        }
    }
    // first searches current directory (if search_local is set), otherwise searches system path
    // and returns the data it contains together with the filepath where it was found
    fn include_data(
        &self,
        token: Token,
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
                &PPToken::from(&token, self.filename),
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
                    let replace_with = self.fold_until_token(TokenKind::Newline);
                    let replace_with = trim_trailing_whitespace(replace_with);

                    // same macro already exists but with different replacement-list
                    if let Some(existing_replacement) = self.defines.get(&identifier) {
                        if as_kind(existing_replacement) != as_kind(&replace_with) {
                            return Err(Error::new(
                                &PPToken::from(&token, self.filename),
                                ErrorKind::Redefinition("macro", identifier),
                            ));
                        }
                    }
                    self.defines.insert(identifier, replace_with);
                    Ok(())
                }
                _ => Err(Error::new(
                    &PPToken::from(&token, self.filename),
                    ErrorKind::InvalidMacroName,
                )),
            }
        } else {
            Err(Error::new(
                &PPToken::from(&directive, self.filename),
                ErrorKind::InvalidMacroName,
            ))
        }
    }
    fn replace_macros(&self, macro_name: Token, replace_list: Vec<Token>) -> Vec<Token> {
        replace_list
            .into_iter()
            .flat_map(|token| {
                match (
                    token.kind.to_string(),
                    self.defines.get(&token.kind.to_string()),
                ) {
                    (token_name, Some(replacement))
                        if token_name != macro_name.kind.as_ident().unwrap() =>
                    {
                        let replacement = replacement
                            .iter()
                            .map(|replace_t| Token {
                                kind: replace_t.kind.clone(),
                                ..macro_name.clone()
                            })
                            .collect::<Vec<Token>>();

                        pad_whitespace(self.replace_macros(macro_name.clone(), replacement))
                    }
                    _ => {
                        // can't further replace if replacement is current macro name
                        vec![Token { kind: token.kind, ..macro_name.clone() }]
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
                    &PPToken::from(&token, self.filename),
                    ErrorKind::InvalidMacroName,
                )),
            }
        } else {
            Err(Error::new(
                &PPToken::from(&directive, self.filename),
                ErrorKind::InvalidMacroName,
            ))
        }
    }

    fn ifdef(&mut self, if_kind: Token) -> Result<(), Error> {
        self.ifs.push(IfDirective::new(Error::new(
            &PPToken::from(&if_kind, self.filename),
            ErrorKind::UnterminatedIf(if_kind.kind.to_string()),
        )));

        self.skip_whitespace()?;

        if let Some(token) = self.tokens.next() {
            match token.kind.as_ident() {
                Some(identifier) => match (&if_kind.kind, self.defines.contains_key(&identifier)) {
                    (TokenKind::Ifdef, true) | (TokenKind::Ifndef, false) => Ok(()),
                    (TokenKind::Ifdef, false) | (TokenKind::Ifndef, true) => {
                        match (self.has_trailing_tokens(), self.eval_else_branch()) {
                            (Err(e1), Err(e2)) => Err(Error::new_multiple(vec![e1, e2])),
                            (Err(e), _) | (_, Err(e)) => Err(e),
                            (..) => Ok(()),
                        }
                    }
                    _ => unreachable!(),
                },
                _ => Err(Error::new(
                    &PPToken::from(&token, self.filename),
                    ErrorKind::InvalidMacroName,
                )),
            }
        } else {
            Err(Error::new(
                &PPToken::from(&if_kind, self.filename),
                ErrorKind::InvalidMacroName,
            ))
        }
    }
    fn if_expr(&mut self, if_kind: Token) -> Result<(), Error> {
        self.ifs.push(IfDirective::new(Error::new(
            &PPToken::from(&if_kind, self.filename),
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
                &PPToken::from(&token, self.filename),
                ErrorKind::MissingIf(token.kind.to_string()),
            ))
        } else {
            let matching_if = self.ifs.last_mut().unwrap();

            match (matching_if.has_else, &token.kind) {
                (true, TokenKind::Elif) => Err(Error::new(
                    &PPToken::from(&token, self.filename),
                    ErrorKind::ElifAfterElse,
                )),
                (false, TokenKind::Elif) => self.skip_branch(true).map(|_| ()),
                (true, TokenKind::Else) => Err(Error::new(
                    &PPToken::from(&token, self.filename),
                    ErrorKind::DuplicateElse,
                )),
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
                TokenKind::Else | TokenKind::Endif => return self.has_trailing_tokens(),
                _ => unreachable!("not #if token"),
            }
        }
    }

    fn eval_cond(&mut self, if_kind: Token) -> Result<bool, Error> {
        let cond = self.fold_until_token(TokenKind::Newline);
        let cond = self.replace_define_expr(cond)?;

        if cond.is_empty()
            || cond
                .iter()
                .all(|t| matches!(t.kind, TokenKind::Whitespace(_)))
        {
            return Err(Error::new(
                &PPToken::from(&if_kind, self.filename),
                ErrorKind::MissingExpression(if_kind.kind.to_string()),
            ));
        }

        match self.pp_const_value(if_kind, cond)? {
            0 => Ok(false),
            _ => Ok(true),
        }
    }

    fn pp_const_value(&self, if_kind: Token, cond: Vec<Token>) -> Result<i64, Error> {
        let cond = cond
            .into_iter()
            .map(|t| PPToken::from(&t, self.filename))
            .collect();
        let tokens = Scanner::new(cond)
            .scan_token()
            .map_err(Error::new_multiple)?;
        let mut parser = Parser::new(tokens);
        let mut expr = parser.expression().map_err(|mut err| {
            if let ErrorKind::Eof(msg) = err.kind {
                err.kind = ErrorKind::Regular(msg)
            }
            err
        })?;

        if let Some(token) = parser.has_elements() {
            return Err(Error::new(
                token,
                ErrorKind::TrailingTokens("preprocessor expression"),
            ));
        }

        let value = expr.preprocessor_constant(&PPToken::from(&if_kind, self.filename))?;

        Ok(value)
    }

    fn replace_define_expr(&mut self, cond: Vec<Token>) -> Result<Vec<Token>, Error> {
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
                                result.push(if self.defines.contains_key(&identifier) {
                                    Token {
                                        kind: TokenKind::Number("1".to_string()),
                                        ..token
                                    }
                                } else {
                                    Token {
                                        kind: TokenKind::Number("0".to_string()),
                                        ..token
                                    }
                                });

                                skip_whitespace(&mut cond);

                                if let Some(open_paren) = open_paren {
                                    if !matches!(
                                        cond.next(),
                                        Some(Token { kind: TokenKind::Other(')'), .. })
                                    ) {
                                        return Err(Error::new(
                                            &PPToken::from(&open_paren, self.filename),
                                            ErrorKind::Regular(
                                                "Expect matching closing ')' after 'defined'",
                                            ),
                                        ));
                                    }
                                }
                            }
                            _ => {
                                return Err(Error::new(
                                    &PPToken::from(&token, self.filename),
                                    ErrorKind::Regular(
                                        "Expect identifier after 'defined'-operator",
                                    ),
                                ))
                            }
                        }
                    } else {
                        return Err(Error::new(
                            &PPToken::from(&token, self.filename),
                            ErrorKind::Regular("Expect identifier after 'defined'-operator"),
                        ));
                    }
                }
                _ => {
                    if let Some(identifier) = token.kind.as_ident() {
                        // if ident is defined replace it
                        if let Some(replacement) = self.defines.get(&identifier) {
                            let expanded_replacement =
                                pad_whitespace(self.replace_macros(token, replacement.clone()));
                            result.extend(expanded_replacement)
                        } else {
                            result.push(token)
                        }
                    } else {
                        result.push(token)
                    }
                }
            }
        }
        // replace all identifiers with 0
        let result = result
            .into_iter()
            .map(|token| {
                if token.kind.as_ident().is_some() {
                    Token {
                        kind: TokenKind::Number("0".to_string()),
                        ..token
                    }
                } else {
                    token
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
                                        &PPToken::from(&token, self.filename),
                                        ErrorKind::ElifAfterElse,
                                    ));
                                }
                                (true, TokenKind::Else) => {
                                    return Err(Error::new(
                                        &PPToken::from(&token, self.filename),
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
                                &PPToken::from(&token, self.filename),
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

    pub fn start(mut self) -> Result<(Vec<PPToken>, HashMap<String, Vec<Token>>), Vec<Error>> {
        let mut result = PPResult::new(self.filename);
        let mut errors = Vec::new();

        while let Some(token) = self.tokens.next() {
            match token.kind {
                TokenKind::Hash if is_first_line_token(&result.inner) => {
                    let _ = self.skip_whitespace();

                    let outcome = if let Some(directive) = self.tokens.next() {
                        match directive.kind {
                            TokenKind::Include => match self.include(directive) {
                                Ok(s) => Ok(s.into_iter().for_each(|t| result.inner.push(t))),
                                Err(e) => Err(e),
                            },
                            TokenKind::Define => self.define(directive),
                            TokenKind::Undef => self.undef(directive),
                            TokenKind::Ifdef | TokenKind::Ifndef => self.ifdef(directive),
                            TokenKind::If => self.if_expr(directive),
                            TokenKind::Elif => self.conditional_block(directive),
                            TokenKind::Else | TokenKind::Endif => {
                                if let Err(e) = self.has_trailing_tokens() {
                                    errors.push(e);
                                }
                                self.conditional_block(directive)
                            }
                            _ => Err(Error::new(
                                &PPToken::from(&directive, self.filename),
                                ErrorKind::InvalidDirective(directive.kind.to_string()),
                            )),
                        }
                    } else {
                        Err(Error::new(
                            &PPToken::from(&token, self.filename),
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
                    } else if let Err(e) = self.has_trailing_tokens() {
                        errors.push(e);
                    }
                }
                _ => {
                    if let Some(identifier) = token.kind.as_ident() {
                        if let Some(replacement) = self.defines.get(&identifier) {
                            let expanded_replacement =
                                pad_whitespace(self.replace_macros(token, replacement.clone()));

                            result.append(expanded_replacement)
                        } else {
                            result.push(token)
                        }
                    } else {
                        result.push(token)
                    }
                }
            }
        }

        if !self.ifs.is_empty() {
            errors.append(&mut self.ifs.iter().map(|i| i.location.clone()).collect());
        }

        if errors.is_empty() {
            Ok((result.inner, self.defines))
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
            match self.tokens.peek() {
                Ok(token) => Err(Error::new(
                    &PPToken::from(token, self.filename),
                    ErrorKind::Regular("Expect whitespace after preprocessing directive"),
                )),
                Err((Some(eof_token), _)) => Err(Error::new(
                    &PPToken::from(&eof_token, self.filename),
                    ErrorKind::Eof("Expected whitespace, "),
                )),
                _ => Err(Error::eof("Expected whitespace")),
            }
        } else {
            Ok(())
        }
    }
    fn has_trailing_tokens(&mut self) -> Result<(), Error> {
        let trailing = self.fold_until_token(TokenKind::Newline);
        let trailing: Vec<&Token> = trailing
            .iter()
            .filter(|t| !matches!(t.kind, TokenKind::Whitespace(_)))
            .collect();

        if trailing.is_empty() {
            Ok(())
        } else {
            Err(Error::new(
                &PPToken::from(trailing[0], self.filename),
                ErrorKind::TrailingTokens("preprocessor directive"),
            ))
        }
    }
}
struct PPResult {
    inner: Vec<PPToken>,
    filename: PathBuf,
}
impl PPResult {
    fn new(filename: &Path) -> Self {
        PPResult {
            inner: Vec::new(),
            filename: filename.into(),
        }
    }
    fn push(&mut self, token: Token) {
        self.inner.push(PPToken::from(&token, &self.filename));
    }
    fn append(&mut self, tokens: Vec<Token>) {
        tokens.into_iter().for_each(|t| self.push(t))
    }
}

// Preprocesses given input file if input file nested inside root-file
fn preprocess_included(
    filename: &Path,
    source: String,
    defines: HashMap<String, Vec<Token>>,
) -> Result<(Vec<PPToken>, HashMap<String, Vec<Token>>), Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();

    Preprocessor::new(filename, tokens, Some(defines)).start()
}

fn as_kind(tokens: &[Token]) -> Vec<&TokenKind> {
    tokens.iter().map(|t| &t.kind).collect()
}

fn trim_trailing_whitespace(mut tokens: Vec<Token>) -> Vec<Token> {
    if let Some(Token { kind: TokenKind::Whitespace(_), .. }) = tokens.last() {
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

// TODO: find a better solution
// adds whitespace to avoid glued tokens caused by macro replacements
// #define bar >
// 1 >bar= shouldn't be replaced to >>= because compiler thinks thats single token
// instead: > > =
fn pad_whitespace(mut tokens: Vec<Token>) -> Vec<Token> {
    if let Some(Token { kind: TokenKind::Other(_), .. }) = tokens.first() {
        tokens.insert(0, Token::placeholder_whitespace())
    }
    if let Some(Token { kind: TokenKind::Other(_), .. }) = tokens.last() {
        tokens.push(Token::placeholder_whitespace())
    }
    tokens
}

fn is_first_line_token(prev_tokens: &[PPToken]) -> bool {
    for token in prev_tokens.iter().rev() {
        match &token.kind {
            TokenKind::Newline => return true,
            TokenKind::Whitespace(_) => (),
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    fn scan(input: &str) -> Vec<Token> {
        PPScanner::new(input.to_string()).scan_token()
    }

    fn setup(input: &str) -> Preprocessor {
        let tokens = PPScanner::new(input.to_string()).scan_token();

        Preprocessor::new(Path::new(""), tokens, None)
    }

    fn setup_complete(input: &str) -> String {
        setup(input)
            .start()
            .unwrap()
            .0
            .into_iter()
            .map(|t| t.kind.to_string())
            .collect()
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
        let pp = Preprocessor::new(Path::new(""), Vec::new(), Some(defined.clone()));

        let mut result = HashMap::new();
        for (name, replace_list) in defined {
            result.insert(
                name.to_string(),
                pp.replace_macros(
                    Token {
                        kind: TokenKind::Ident(name),
                        column: 1,
                        line: 1,
                        line_string: "".to_string(),
                    },
                    replace_list,
                )
                .into_iter()
                .map(|t| t.kind.to_string())
                .collect(),
            );
        }

        result
    }

    #[test]
    fn first_line_token() {
        let to_pp_tok = |input: &str| {
            scan(input)
                .into_iter()
                .map(|t| PPToken::from(&t, Path::new("")))
                .collect::<Vec<_>>()
        };
        assert_eq!(is_first_line_token(&to_pp_tok("")), true);
        assert_eq!(is_first_line_token(&to_pp_tok("\n  \t ")), true);
        assert_eq!(is_first_line_token(&to_pp_tok("\nint\n ")), true);
        assert_eq!(is_first_line_token(&to_pp_tok("\nint ")), false);
        assert_eq!(is_first_line_token(&to_pp_tok("+ ")), false);
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
        let expected = "\n\nchar empty = 0;\n";

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
        let expected = "\n\n\nchar s = 'i';\n\nchar empty = 0;\n";

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
        let expected = "\n\nchar s = 'l';\n\n\nchar c = 2;\n\n";

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
        let expected = "\n\n\nchar s = 'o';\n\n";

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
        let expected = "\n\nint only_this;\n\n";

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
        let expected = "\n\nint only_this;\n\n";

        assert_eq!(actual, expected);
    }
    #[test]
    fn trailing_tokens() {
        let actual = setup_complete(
            "
#ifdef some   /* hallo */
if_branch
#else   \\
    // doesnt matter
else_branch
#endif
",
        );
        let expected = "\n\nelse_branch\n\n";

        assert_eq!(actual, expected);
    }
    #[test]
    fn trailing_tokens_err() {
        let actual = setup_complete_err(
            "
        #ifdef some    12
        #elif 1 +
        #endif",
        );

        assert!(matches!(
            actual[..],
            [
                ErrorKind::TrailingTokens("preprocessor directive"),
                ErrorKind::Regular("Expected expression"),
            ]
        ));
    }
    #[test]
    fn trailing_tokens_skipped_branch() {
        let actual = setup_complete_err(
            r#"
        #ifdef some    12
        #endif"#,
        );

        assert!(matches!(
            actual[..],
            [ErrorKind::TrailingTokens("preprocessor directive")]
        ));
    }
}
