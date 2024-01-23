use crate::compiler::common::{error::*, token::*};
use crate::preprocessor::scanner::TokenKind as PPKind;
use crate::PPToken;
use std::collections::HashMap;
use std::iter::Peekable;

// Converts preprocessor tokens into compiler tokens
pub struct Scanner<'a> {
    // source used for iterating
    source: Peekable<std::vec::IntoIter<PPToken>>,

    keywords: HashMap<&'a str, TokenType>,
}
impl<'a> Scanner<'a> {
    pub fn new(source: Vec<PPToken>) -> Self {
        Scanner {
            source: source.into_iter().peekable(),
            keywords: HashMap::from([
                ("void", TokenType::Void),
                ("int", TokenType::Int),
                ("long", TokenType::Long),
                ("char", TokenType::Char),
                ("struct", TokenType::Struct),
                ("union", TokenType::Union),
                ("enum", TokenType::Enum),
                ("typedef", TokenType::TypeDef),
                ("if", TokenType::If),
                ("switch", TokenType::Switch),
                ("case", TokenType::Case),
                ("default", TokenType::Default),
                ("else", TokenType::Else),
                ("for", TokenType::For),
                ("while", TokenType::While),
                ("do", TokenType::Do),
                ("break", TokenType::Break),
                ("continue", TokenType::Continue),
                ("sizeof", TokenType::Sizeof),
                ("return", TokenType::Return),
                ("goto", TokenType::Goto),
            ]),
        }
    }

    fn match_next(&mut self, expected: char, if_match: TokenType, if_not: TokenType) -> TokenType {
        match self.matches(expected) {
            true => if_match,
            false => if_not,
        }
    }
    pub fn scan_token(&mut self) -> Result<Vec<Token>, Vec<Error>> {
        let mut errors: Vec<Error> = Vec::new();
        let mut tokens = ScanResult(Vec::new());

        while let Some(pp_token) = self.source.next() {
            match pp_token.kind {
                PPKind::Other(c) => {
                    match c {
                        '[' => tokens.push(pp_token, TokenType::LeftBracket),
                        ']' => tokens.push(pp_token, TokenType::RightBracket),
                        '(' => tokens.push(pp_token, TokenType::LeftParen),
                        ')' => tokens.push(pp_token, TokenType::RightParen),
                        '{' => tokens.push(pp_token, TokenType::LeftBrace),
                        '}' => tokens.push(pp_token, TokenType::RightBrace),
                        ',' => tokens.push(pp_token, TokenType::Comma),
                        ';' => tokens.push(pp_token, TokenType::Semicolon),
                        '~' => tokens.push(pp_token, TokenType::Tilde),
                        '?' => tokens.push(pp_token, TokenType::Question),
                        ':' => tokens.push(pp_token, TokenType::Colon),
                        '.' => {
                            if let Some(PPToken { kind: PPKind::Other('.'), .. }) =
                                self.source.peek()
                            {
                                let second_token = self.source.next().unwrap();
                                if self.matches('.') {
                                    tokens.push(pp_token, TokenType::Ellipsis);
                                } else {
                                    // since only single lookahead have to add two seperate dots
                                    tokens.push(pp_token, TokenType::Dot);
                                    tokens.push(second_token, TokenType::Dot);
                                }
                            } else {
                                tokens.push(pp_token, TokenType::Dot)
                            }
                        }
                        '-' => {
                            let mut token = TokenType::Minus;
                            if self.matches('-') {
                                token = TokenType::MinusMinus;
                            } else if self.matches('=') {
                                token = TokenType::MinusEqual;
                            } else if self.matches('>') {
                                token = TokenType::Arrow;
                            }
                            tokens.push(pp_token, token);
                        }
                        '+' => {
                            let mut token = TokenType::Plus;
                            if self.matches('+') {
                                token = TokenType::PlusPlus;
                            } else if self.matches('=') {
                                token = TokenType::PlusEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '|' => {
                            let mut token = TokenType::Pipe;
                            if self.matches('|') {
                                token = TokenType::PipePipe;
                            } else if self.matches('=') {
                                token = TokenType::PipeEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '&' => {
                            let mut token = TokenType::Amp;
                            if self.matches('&') {
                                token = TokenType::AmpAmp;
                            } else if self.matches('=') {
                                token = TokenType::AmpEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '<' => {
                            let mut token = TokenType::Less;
                            if self.matches('<') {
                                token = self.match_next(
                                    '=',
                                    TokenType::LessLessEqual,
                                    TokenType::LessLess,
                                );
                            } else if self.matches('=') {
                                token = TokenType::LessEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '>' => {
                            let mut token = TokenType::Greater;
                            if self.matches('>') {
                                token = self.match_next(
                                    '=',
                                    TokenType::GreaterGreaterEqual,
                                    TokenType::GreaterGreater,
                                );
                            } else if self.matches('=') {
                                token = TokenType::GreaterEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '^' => {
                            let token = self.match_next('=', TokenType::XorEqual, TokenType::Xor);
                            tokens.push(pp_token, token);
                        }
                        '*' => {
                            let token = self.match_next('=', TokenType::StarEqual, TokenType::Star);
                            tokens.push(pp_token, token);
                        }
                        '%' => {
                            let token = self.match_next('=', TokenType::ModEqual, TokenType::Mod);
                            tokens.push(pp_token, token);
                        }

                        '!' => {
                            let token = self.match_next('=', TokenType::BangEqual, TokenType::Bang);
                            tokens.push(pp_token, token);
                        }
                        '=' => {
                            let token =
                                self.match_next('=', TokenType::EqualEqual, TokenType::Equal);
                            tokens.push(pp_token, token);
                        }

                        '/' => {
                            let token =
                                self.match_next('=', TokenType::SlashEqual, TokenType::Slash);
                            tokens.push(pp_token, token);
                        }
                        _ => {
                            errors.push(Error::new(&pp_token, ErrorKind::UnexpectedChar(c)));
                        }
                    }
                }
                PPKind::String(ref s) => {
                    let mut s = s.clone();
                    let first = s.remove(0);
                    assert_eq!(first, '"');

                    if let Some('"') = s.pop() {
                        tokens.push(pp_token, TokenType::String(s))
                    } else {
                        errors.push(Error::new(&pp_token.clone(), ErrorKind::UnterminatedString))
                    }
                }
                PPKind::CharLit(ref c) => match self.char_lit(&pp_token, c.clone()) {
                    Ok(char) => tokens.push(pp_token, TokenType::CharLit(char as i8)),
                    Err(e) => errors.push(e),
                },
                PPKind::Number(ref num) => match num.parse::<i64>() {
                    Ok(n) => tokens.push(pp_token, TokenType::Number(n)),
                    Err(e) => {
                        errors.push(Error::new(
                            &pp_token.clone(),
                            ErrorKind::InvalidNumber(e.kind().clone()),
                        ));
                    }
                },
                PPKind::Ident(_)
                | PPKind::Include
                | PPKind::If
                | PPKind::Ifdef
                | PPKind::Ifndef
                | PPKind::Else
                | PPKind::Elif
                | PPKind::Endif
                | PPKind::Undef
                | PPKind::Define
                | PPKind::Defined => {
                    let ident = pp_token.kind.to_string();
                    if let Some(kw) = self.keywords.get(ident.as_str()) {
                        tokens.push(pp_token, kw.clone());
                    } else {
                        tokens.push(pp_token.clone(), TokenType::Ident(ident))
                    }
                }
                PPKind::Hash => errors.push(Error::new(&pp_token, ErrorKind::UnexpectedChar('#'))),
                PPKind::Whitespace(_) | PPKind::Newline => (),
            }
        }
        if errors.is_empty() {
            Ok(tokens.0)
        } else {
            Err(errors)
        }
    }
    fn matches(&mut self, expected: char) -> bool {
        match self.source.peek() {
            Some(PPToken { kind: PPKind::Other(c), .. }) => {
                if *c != expected {
                    return false;
                }
            }
            _ => return false,
        }
        self.source.next();
        true
    }
    fn char_lit(&mut self, pp_token: &PPToken, char: String) -> Result<char, Error> {
        let mut char_iter = char.chars();

        let first = char_iter.next();
        assert_eq!(first, Some('\''));

        let mut c = char_iter
            .next()
            .ok_or(Error::new(pp_token, ErrorKind::Eof("character literal")))?;

        if c == '\\' {
            let char_to_escape = char_iter
                .next()
                .ok_or(Error::new(pp_token, ErrorKind::Eof("character literal")))?;
            c = self.escape_char(char_to_escape).ok_or(Error::new(
                pp_token,
                ErrorKind::InvalidEscape(char_to_escape),
            ))?;
        }
        if !matches!(char_iter.next(), Some('\'')) {
            return Err(Error::new(pp_token, ErrorKind::CharLiteralQuotes));
        }
        if !c.is_ascii() {
            return Err(Error::new(pp_token, ErrorKind::CharLiteralAscii(c)));
        };

        Ok(c)
    }
    fn escape_char(&mut self, char_to_escape: char) -> Option<char> {
        match char_to_escape {
            '0' => Some('\0'),
            'n' => Some('\n'),
            'r' => Some('\r'),
            't' => Some('\t'),
            '\\' => Some('\\'),
            '\'' => Some('\''),
            '\"' => Some('\"'),
            _ => None,
        }
    }
}

struct ScanResult(Vec<Token>);
impl ScanResult {
    fn push(&mut self, pp_token: PPToken, new_kind: TokenType) {
        self.0.push(Token::new(
            new_kind,
            pp_token.line,
            pp_token.column,
            pp_token.line_string,
            pp_token.filename,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::preprocess;
    use std::path::{Path, PathBuf};

    fn setup_generic(input: &str) -> Vec<Token> {
        let pp_tokens = preprocess(Path::new(""), input.to_string()).unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        if let Ok(tokens) = scanner.scan_token() {
            tokens
        } else {
            unreachable!("want to test successfull scan")
        }
    }
    fn setup_generic_err(input: &str) -> Vec<Error> {
        let pp_tokens = preprocess(Path::new(""), input.to_string()).unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        if let Err(errs) = scanner.scan_token() {
            errs
        } else {
            unreachable!("want to test errors")
        }
    }
    fn test_token(token: TokenType, line_index: i32, column: i32, line_string: &str) -> Token {
        Token {
            token,
            line_index,
            column,
            line_string: line_string.to_string(),
            filename: PathBuf::new(),
        }
    }

    // helper functions when other token-information isn't necessary
    fn setup(input: &str) -> Vec<TokenType> {
        setup_generic(input).into_iter().map(|e| e.token).collect()
    }

    fn setup_err(input: &str) -> Vec<ErrorKind> {
        setup_generic_err(input)
            .into_iter()
            .map(|e| e.kind)
            .collect()
    }

    #[test]
    fn basic_single_and_double_tokens() {
        let actual = setup_generic("!= = > == \n\n    ;");
        let expected = vec![
            test_token(TokenType::BangEqual, 1, 1, "!= = > == "),
            test_token(TokenType::Equal, 1, 4, "!= = > == "),
            test_token(TokenType::Greater, 1, 6, "!= = > == "),
            test_token(TokenType::EqualEqual, 1, 8, "!= = > == "),
            test_token(TokenType::Semicolon, 3, 5, "    ;"),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn ignores_comments() {
        let actual = setup_generic("// this is a    comment\n\n!this");
        let expected = vec![
            test_token(TokenType::Bang, 3, 1, "!this"),
            test_token(TokenType::Ident("this".to_string()), 3, 2, "!this"),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn token_basic_math_expression() {
        let actual = setup("3 + 1 / 4");
        let expected = vec![
            TokenType::Number(3),
            TokenType::Plus,
            TokenType::Number(1),
            TokenType::Slash,
            TokenType::Number(4),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn basic_math_double_digit_nums() {
        let actual = setup("300 - 11 * 41");
        let expected = vec![
            TokenType::Number(300),
            TokenType::Minus,
            TokenType::Number(11),
            TokenType::Star,
            TokenType::Number(41),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn matches_keywords_and_strings() {
        let actual = setup("int some = \"this is a string\"");
        let expected = vec![
            TokenType::Int,
            TokenType::Ident("some".to_string()),
            TokenType::Equal,
            TokenType::String("this is a string".to_string()),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn errors_on_unterminated_string() {
        let actual = setup_err("int some = \"this is a string");
        let expected = vec![ErrorKind::UnterminatedString];

        assert_eq!(actual, expected);
    }
    #[test]
    fn matches_complex_keywords() {
        let actual = setup_generic("int some_long;\nwhile (val >= 12) {*p = val}");
        let expected = vec![
            test_token(TokenType::Int, 1, 1, "int some_long;"),
            test_token(
                TokenType::Ident("some_long".to_string()),
                1,
                5,
                "int some_long;",
            ),
            test_token(TokenType::Semicolon, 1, 14, "int some_long;"),
            test_token(TokenType::While, 2, 1, "while (val >= 12) {*p = val}"),
            test_token(TokenType::LeftParen, 2, 7, "while (val >= 12) {*p = val}"),
            test_token(
                TokenType::Ident("val".to_string()),
                2,
                8,
                "while (val >= 12) {*p = val}",
            ),
            test_token(
                TokenType::GreaterEqual,
                2,
                12,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenType::Number(12), 2, 15, "while (val >= 12) {*p = val}"),
            test_token(TokenType::RightParen, 2, 17, "while (val >= 12) {*p = val}"),
            test_token(TokenType::LeftBrace, 2, 19, "while (val >= 12) {*p = val}"),
            test_token(TokenType::Star, 2, 20, "while (val >= 12) {*p = val}"),
            test_token(
                TokenType::Ident("p".to_string()),
                2,
                21,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenType::Equal, 2, 23, "while (val >= 12) {*p = val}"),
            test_token(
                TokenType::Ident("val".to_string()),
                2,
                25,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenType::RightBrace, 2, 28, "while (val >= 12) {*p = val}"),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn detects_single_on_invalid_char() {
        let actual = setup_err("int c = 0$");
        let expected = vec![ErrorKind::UnexpectedChar('$')];

        assert_eq!(actual, expected);
    }
    #[test]
    fn detects_mutliple_on_invalid_chars() {
        let actual = setup_generic_err("int c = 0$\n\n‘ ∞");
        let expected = vec![
            Error {
                line_index: 1,
                column: 10,
                filename: PathBuf::from(""),
                line_string: "int c = 0$".to_string(),
                kind: ErrorKind::UnexpectedChar('$'),
            },
            Error {
                line_index: 3,
                column: 1,
                filename: PathBuf::from(""),
                line_string: "‘ ∞".to_string(),
                kind: ErrorKind::UnexpectedChar('‘'),
            },
            Error {
                line_index: 3,
                column: 3,
                filename: PathBuf::from(""),
                line_string: "‘ ∞".to_string(),
                kind: ErrorKind::UnexpectedChar('∞'),
            },
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn can_handle_non_ascii_alphabet() {
        let actual = setup_generic("\nint ä = 123");
        let expected = vec![
            test_token(TokenType::Int, 2, 1, "int ä = 123"),
            test_token(TokenType::Ident("ä".to_string()), 2, 5, "int ä = 123"),
            test_token(TokenType::Equal, 2, 8, "int ä = 123"), // ä len is 2 but thats fine because its the same when indexing
            test_token(TokenType::Number(123), 2, 10, "int ä = 123"),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn errors_on_non_ascii_non_letters() {
        let actual = setup_generic_err("\nint ä @ = 123");
        let expected = vec![Error {
            line_index: 2,
            column: 8,
            filename: PathBuf::from(""),
            line_string: "int ä @ = 123".to_string(),
            kind: ErrorKind::UnexpectedChar('@'),
        }];
        assert_eq!(actual, expected);
    }
    #[test]
    fn char_literal() {
        let actual = setup("char some = '1'");
        let expected = vec![
            TokenType::Char,
            TokenType::Ident("some".to_string()),
            TokenType::Equal,
            TokenType::CharLit('1' as i8),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn char_literal_len_greater_1() {
        let actual = setup_err("char some = '12'; ''");
        let expected = vec![ErrorKind::CharLiteralQuotes, ErrorKind::CharLiteralQuotes];

        assert_eq!(actual, expected);
    }

    #[test]
    fn ellipsis_dot_distinction() {
        let actual = setup(".....;...");
        let expected = vec![
            TokenType::Ellipsis,
            TokenType::Dot,
            TokenType::Dot,
            TokenType::Semicolon,
            TokenType::Ellipsis,
        ];
        assert_eq!(actual, expected);
    }

    #[test]
    fn handle_newline_string() {
        let input: String = vec!['"', 'h', 'a', '\\', 'n', 'l', '"']
            .into_iter()
            .collect();

        let pp_tokens = preprocess(Path::new(""), input).unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        let actual: Vec<TokenType> = scanner
            .scan_token()
            .unwrap()
            .into_iter()
            .map(|e| e.token)
            .collect();

        let expected = vec![TokenType::String("ha\\nl".to_string())];

        assert_eq!(actual, expected);
    }

    #[test]
    fn handle_multiline_string() {
        let input: String = vec!['"', 'h', 'a', '\\', '\n', 'l', '"']
            .into_iter()
            .collect();

        let pp_tokens = preprocess(Path::new(""), input).unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        let actual: Vec<TokenType> = scanner
            .scan_token()
            .unwrap()
            .into_iter()
            .map(|e| e.token)
            .collect();
        let expected = vec![TokenType::String("hal".to_string())];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_err() {
        let input: String = vec!['"', 'h', 'a', '\n', 'l', '"'].into_iter().collect();

        let actual = setup_generic_err(&input);
        let expected = vec![
            Error {
                line_index: 1,
                column: 1,
                filename: PathBuf::new(),
                line_string: "\"ha".to_string(),
                kind: ErrorKind::UnterminatedString,
            },
            Error {
                line_index: 2,
                line_string: "l\"".to_string(),
                column: 2,
                filename: PathBuf::new(),
                kind: ErrorKind::UnterminatedString,
            },
        ];

        assert_eq!(actual, expected);
    }
}
