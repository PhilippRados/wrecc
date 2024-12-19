//! Converts [preprocessor-tokens](PPToken) into [compiler-tokens](Token)

use crate::compiler::common::{error::*, token::*};
use crate::preprocessor::scanner::TokenKind as PPKind;
use crate::PPToken;
use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

pub struct Scanner<'a> {
    // Source used for iterating
    source: Peekable<std::vec::IntoIter<PPToken>>,

    // Reserved keywords which cannot be an identifier
    keywords: HashMap<&'a str, TokenKind>,
}
impl<'a> Scanner<'a> {
    pub fn new(source: Vec<PPToken>) -> Self {
        Scanner {
            source: source.into_iter().peekable(),
            keywords: HashMap::from([
                ("void", TokenKind::Void),
                ("unsigned", TokenKind::Unsigned),
                ("signed", TokenKind::Signed),
                ("int", TokenKind::Int),
                ("long", TokenKind::Long),
                ("char", TokenKind::Char),
                ("short", TokenKind::Short),
                ("struct", TokenKind::Struct),
                ("union", TokenKind::Union),
                ("enum", TokenKind::Enum),
                ("typedef", TokenKind::TypeDef),
                ("extern", TokenKind::Extern),
                ("static", TokenKind::Static),
                ("auto", TokenKind::Auto),
                ("register", TokenKind::Register),
                ("inline", TokenKind::Inline),
                ("const", TokenKind::Const),
                ("volatile", TokenKind::Volatile),
                ("restrict", TokenKind::Restrict),
                ("if", TokenKind::If),
                ("switch", TokenKind::Switch),
                ("case", TokenKind::Case),
                ("default", TokenKind::Default),
                ("else", TokenKind::Else),
                ("for", TokenKind::For),
                ("while", TokenKind::While),
                ("do", TokenKind::Do),
                ("break", TokenKind::Break),
                ("continue", TokenKind::Continue),
                ("sizeof", TokenKind::Sizeof),
                ("return", TokenKind::Return),
                ("goto", TokenKind::Goto),
            ]),
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
    fn match_next(&mut self, expected: char, if_match: TokenKind, if_not: TokenKind) -> TokenKind {
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
                        '[' => tokens.push(pp_token, TokenKind::LeftBracket),
                        ']' => tokens.push(pp_token, TokenKind::RightBracket),
                        '(' => tokens.push(pp_token, TokenKind::LeftParen),
                        ')' => tokens.push(pp_token, TokenKind::RightParen),
                        '{' => tokens.push(pp_token, TokenKind::LeftBrace),
                        '}' => tokens.push(pp_token, TokenKind::RightBrace),
                        ',' => tokens.push(pp_token, TokenKind::Comma),
                        ';' => tokens.push(pp_token, TokenKind::Semicolon),
                        '~' => tokens.push(pp_token, TokenKind::Tilde),
                        '?' => tokens.push(pp_token, TokenKind::Question),
                        ':' => tokens.push(pp_token, TokenKind::Colon),
                        '.' => {
                            if let Some(PPToken { kind: PPKind::Other('.'), .. }) = self.source.peek() {
                                let second_token = self.source.next().unwrap();
                                if self.matches('.') {
                                    tokens.push(pp_token, TokenKind::Ellipsis);
                                } else {
                                    // since only single lookahead have to add two seperate dots
                                    tokens.push(pp_token, TokenKind::Dot);
                                    tokens.push(second_token, TokenKind::Dot);
                                }
                            } else {
                                tokens.push(pp_token, TokenKind::Dot)
                            }
                        }
                        '-' => {
                            let mut token = TokenKind::Minus;
                            if self.matches('-') {
                                token = TokenKind::MinusMinus;
                            } else if self.matches('=') {
                                token = TokenKind::MinusEqual;
                            } else if self.matches('>') {
                                token = TokenKind::Arrow;
                            }
                            tokens.push(pp_token, token);
                        }
                        '+' => {
                            let mut token = TokenKind::Plus;
                            if self.matches('+') {
                                token = TokenKind::PlusPlus;
                            } else if self.matches('=') {
                                token = TokenKind::PlusEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '|' => {
                            let mut token = TokenKind::Pipe;
                            if self.matches('|') {
                                token = TokenKind::PipePipe;
                            } else if self.matches('=') {
                                token = TokenKind::PipeEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '&' => {
                            let mut token = TokenKind::Amp;
                            if self.matches('&') {
                                token = TokenKind::AmpAmp;
                            } else if self.matches('=') {
                                token = TokenKind::AmpEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '<' => {
                            let mut token = TokenKind::Less;
                            if self.matches('<') {
                                token =
                                    self.match_next('=', TokenKind::LessLessEqual, TokenKind::LessLess);
                            } else if self.matches('=') {
                                token = TokenKind::LessEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '>' => {
                            let mut token = TokenKind::Greater;
                            if self.matches('>') {
                                token = self.match_next(
                                    '=',
                                    TokenKind::GreaterGreaterEqual,
                                    TokenKind::GreaterGreater,
                                );
                            } else if self.matches('=') {
                                token = TokenKind::GreaterEqual;
                            }
                            tokens.push(pp_token, token);
                        }
                        '^' => {
                            let token = self.match_next('=', TokenKind::XorEqual, TokenKind::Xor);
                            tokens.push(pp_token, token);
                        }
                        '*' => {
                            let token = self.match_next('=', TokenKind::StarEqual, TokenKind::Star);
                            tokens.push(pp_token, token);
                        }
                        '%' => {
                            let token = self.match_next('=', TokenKind::ModEqual, TokenKind::Mod);
                            tokens.push(pp_token, token);
                        }

                        '!' => {
                            let token = self.match_next('=', TokenKind::BangEqual, TokenKind::Bang);
                            tokens.push(pp_token, token);
                        }
                        '=' => {
                            let token = self.match_next('=', TokenKind::EqualEqual, TokenKind::Equal);
                            tokens.push(pp_token, token);
                        }

                        '/' => {
                            let token = self.match_next('=', TokenKind::SlashEqual, TokenKind::Slash);
                            tokens.push(pp_token, token);
                        }
                        _ => {
                            errors.push(Error::new(&pp_token, ErrorKind::UnexpectedChar(c)));
                        }
                    }
                }
                PPKind::String(ref s) => {
                    let mut string = String::new();

                    match self.string_lit(&pp_token, s.clone()) {
                        Ok(s) => string.push_str(&s),
                        Err(e) => errors.push(e),
                    }

                    // concatenate springs which are only seperated by whitespace or newline
                    while let Some(PPKind::String(_) | PPKind::Whitespace(_) | PPKind::Newline) =
                        self.source.peek().map(|t| &t.kind)
                    {
                        match self.source.next().map(|t| t.kind) {
                            Some(PPKind::String(s)) => match self.string_lit(&pp_token, s) {
                                Ok(s) => string.push_str(&s),
                                Err(e) => errors.push(e),
                            },
                            Some(PPKind::Newline | PPKind::Whitespace(_)) => (),
                            _ => unreachable!("just peeked"),
                        }
                    }
                    tokens.push(pp_token, TokenKind::String(string))
                }
                PPKind::CharLit(ref s) => match self.char_lit(&pp_token, s) {
                    Ok(char) => tokens.push(pp_token, TokenKind::CharLit(char)),
                    Err(e) => errors.push(e),
                },
                PPKind::Number(ref num, ref suffix) => match self.num_lit(&pp_token, num, suffix) {
                    Ok((num, radix, suffix)) => {
                        tokens.push(pp_token, TokenKind::Number(num, radix, suffix))
                    }
                    Err(e) => errors.push(e),
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
                        tokens.push(pp_token.clone(), TokenKind::Ident(ident))
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
    fn num_lit(
        &mut self,
        pp_token: &PPToken,
        num: &String,
        suffix: &String,
    ) -> Result<(u64, Radix, Option<IntSuffix>), Error> {
        let mut num_iter = num.chars().peekable();
        let (n, radix) = if num.len() > 1 && num_iter.next_if(|c| *c == '0').is_some() {
            if num_iter.next_if(|c| *c == 'x' || *c == 'X').is_some() {
                (u64::from_str_radix(&num_iter.collect::<String>(), 16), Radix::Hex)
            } else {
                (
                    u64::from_str_radix(&num_iter.collect::<String>(), 8),
                    Radix::Octal,
                )
            }
        } else {
            (num.parse::<u64>(), Radix::Decimal)
        };

        let n = n.map_err(|e| {
            Error::new(
                pp_token,
                ErrorKind::InvalidNumber(e.kind().clone(), radix.to_string()),
            )
        })?;

        let suffix = match suffix.as_str() {
            "u" | "U" => Some(IntSuffix::U),
            "l" | "L" => Some(IntSuffix::L),
            "ul" | "Ul" | "uL" | "UL" | "lu" | "lU" | "Lu" | "LU" => Some(IntSuffix::UL),
            "ll" | "LL" => Some(IntSuffix::LL),
            "ull" | "Ull" | "uLL" | "ULL" | "llu" | "llU" | "LLu" | "LLU" => Some(IntSuffix::ULL),
            "" => None,
            _ => {
                return Err(Error::new(
                    pp_token,
                    ErrorKind::InvalidIntSuffix(suffix.to_string()),
                ))
            }
        };

        Ok((n, radix, suffix))
    }
    fn string_lit(&mut self, pp_token: &PPToken, mut string: String) -> Result<String, Error> {
        let first = string.remove(0);
        assert_eq!(first, '"');

        if let Some('"') = string.pop() {
            let mut chars = string.chars().peekable();
            let mut string = Vec::new();

            while let Some(c) = chars.next() {
                let c = self.parse_char(pp_token, c, &mut chars, true)?;
                string.push(c);
            }

            Ok(string.into_iter().collect())
        } else {
            Err(Error::new(&pp_token.clone(), ErrorKind::UnterminatedString))
        }
    }
    fn char_lit(&mut self, pp_token: &PPToken, char_string: &str) -> Result<char, Error> {
        let mut char_iter = char_string.chars().peekable();

        let first = char_iter.next();
        assert_eq!(first, Some('\''));

        let c = char_iter
            .next()
            .ok_or(Error::new(pp_token, ErrorKind::Eof("expected character literal")))?;

        let c = self.parse_char(pp_token, c, &mut char_iter, false)?;

        if !matches!(char_iter.next(), Some('\'')) {
            return Err(Error::new(pp_token, ErrorKind::CharLiteralQuotes));
        }

        Ok(c)
    }
    fn parse_char(
        &mut self,
        pp_token: &PPToken,
        c: char,
        char_iter: &mut Peekable<Chars>,
        is_string: bool,
    ) -> Result<char, Error> {
        if c == '\\' {
            let char_string = char_iter.clone().collect::<String>();
            let char_to_escape = char_iter
                .next()
                .ok_or(Error::new(pp_token, ErrorKind::Eof("expected character literal")))?;
            self.escape_char(char_to_escape, char_iter)
                .ok_or(Error::new(pp_token, ErrorKind::InvalidEscape(char_string)))
        } else if c.is_ascii() || is_string {
            // strings can contain non-ascii chars
            Ok(c)
        } else {
            // doesn't apply to escaped chars since they can are in
            // range [0;255] which is valid while valid ascii is only [0;127]
            Err(Error::new(pp_token, ErrorKind::CharLiteralAscii(c)))
        }
    }
    fn escape_char(&mut self, char_to_escape: char, char_iter: &mut Peekable<Chars>) -> Option<char> {
        match char_to_escape {
            'a' => Some('\x07'),
            'b' => Some('\x08'),
            'f' => Some('\x0C'),
            'n' => Some('\n'),
            'r' => Some('\r'),
            't' => Some('\t'),
            'v' => Some('\x0B'),
            '\\' => Some('\\'),
            '"' => Some('\"'),
            '\'' => Some('\''),
            '?' => Some('?'),
            c if c.is_digit(8) => {
                let mut octal = String::from(c);
                while let Some(c) = char_iter.peek() {
                    if c.is_digit(8) {
                        octal.push(char_iter.next().unwrap());
                    } else {
                        break;
                    }
                }
                // should only contain upto three octal literals
                if octal.len() > 3 {
                    return None;
                }

                let dec = u8::from_str_radix(&octal, 8).ok()?;
                let c = char::from_u32(dec as u32)?;

                Some(c)
            }
            c if c == 'x' => {
                // Hexadecimal escape sequences have no length limit and terminate at the first
                // character that is not a valid hexadecimal digit. Resulting literal should fit in char type
                let mut hex = String::new();
                while let Some(c) = char_iter.peek() {
                    if c.is_digit(16) {
                        hex.push(char_iter.next().unwrap());
                    } else {
                        break;
                    }
                }
                let dec = u8::from_str_radix(&hex, 16).ok()?;
                let c = char::from_u32(dec as u32)?;

                Some(c)
            }
            _ => None,
        }
    }
}

struct ScanResult(Vec<Token>);
impl ScanResult {
    fn push(&mut self, pp_token: PPToken, new_kind: TokenKind) {
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
        let pp_tokens = preprocess(
            Path::new(""),
            &Vec::new(),
            &Vec::new(),
            &HashMap::new(),
            input.to_string(),
        )
        .unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        if let Ok(tokens) = scanner.scan_token() {
            tokens
        } else {
            unreachable!("want to test successfull scan")
        }
    }
    fn setup_generic_err(input: &str) -> Vec<Error> {
        let pp_tokens = preprocess(
            Path::new(""),
            &Vec::new(),
            &Vec::new(),
            &HashMap::new(),
            input.to_string(),
        )
        .unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        if let Err(errs) = scanner.scan_token() {
            errs
        } else {
            unreachable!("want to test errors")
        }
    }
    fn test_token(token: TokenKind, line_index: i32, column: i32, line_string: &str) -> Token {
        Token {
            kind: token,
            line_index,
            column,
            line_string: line_string.to_string(),
            filename: PathBuf::new(),
        }
    }

    // helper functions when other token-information isn't necessary
    fn setup(input: &str) -> Vec<TokenKind> {
        setup_generic(input).into_iter().map(|e| e.kind).collect()
    }

    fn setup_err(input: &str) -> Vec<ErrorKind> {
        setup_generic_err(input).into_iter().map(|e| e.kind).collect()
    }

    #[test]
    fn basic_single_and_double_tokens() {
        let actual = setup_generic("!= = > == \n\n    ;");
        let expected = vec![
            test_token(TokenKind::BangEqual, 1, 1, "!= = > == "),
            test_token(TokenKind::Equal, 1, 4, "!= = > == "),
            test_token(TokenKind::Greater, 1, 6, "!= = > == "),
            test_token(TokenKind::EqualEqual, 1, 8, "!= = > == "),
            test_token(TokenKind::Semicolon, 3, 5, "    ;"),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn ignores_comments() {
        let actual = setup_generic("// this is a    comment\n\n!this");
        let expected = vec![
            test_token(TokenKind::Bang, 3, 1, "!this"),
            test_token(TokenKind::Ident("this".to_string()), 3, 2, "!this"),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn token_basic_math_expression() {
        let actual = setup("3 + 1 / -4");
        let expected = vec![
            TokenKind::Number(3, Radix::Decimal, None),
            TokenKind::Plus,
            TokenKind::Number(1, Radix::Decimal, None),
            TokenKind::Slash,
            TokenKind::Minus,
            TokenKind::Number(4, Radix::Decimal, None),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn basic_math_double_digit_nums() {
        let actual = setup("300 - 11 * 41");
        let expected = vec![
            TokenKind::Number(300, Radix::Decimal, None),
            TokenKind::Minus,
            TokenKind::Number(11, Radix::Decimal, None),
            TokenKind::Star,
            TokenKind::Number(41, Radix::Decimal, None),
        ];
        assert_eq!(actual, expected);
    }
    #[test]
    fn matches_keywords_and_strings() {
        let actual = setup("int some = \"this is a string\"");
        let expected = vec![
            TokenKind::Int,
            TokenKind::Ident("some".to_string()),
            TokenKind::Equal,
            TokenKind::String("this is a string".to_string()),
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
            test_token(TokenKind::Int, 1, 1, "int some_long;"),
            test_token(TokenKind::Ident("some_long".to_string()), 1, 5, "int some_long;"),
            test_token(TokenKind::Semicolon, 1, 14, "int some_long;"),
            test_token(TokenKind::While, 2, 1, "while (val >= 12) {*p = val}"),
            test_token(TokenKind::LeftParen, 2, 7, "while (val >= 12) {*p = val}"),
            test_token(
                TokenKind::Ident("val".to_string()),
                2,
                8,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenKind::GreaterEqual, 2, 12, "while (val >= 12) {*p = val}"),
            test_token(
                TokenKind::Number(12, Radix::Decimal, None),
                2,
                15,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenKind::RightParen, 2, 17, "while (val >= 12) {*p = val}"),
            test_token(TokenKind::LeftBrace, 2, 19, "while (val >= 12) {*p = val}"),
            test_token(TokenKind::Star, 2, 20, "while (val >= 12) {*p = val}"),
            test_token(
                TokenKind::Ident("p".to_string()),
                2,
                21,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenKind::Equal, 2, 23, "while (val >= 12) {*p = val}"),
            test_token(
                TokenKind::Ident("val".to_string()),
                2,
                25,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenKind::RightBrace, 2, 28, "while (val >= 12) {*p = val}"),
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
            test_token(TokenKind::Int, 2, 1, "int ä = 123"),
            test_token(TokenKind::Ident("ä".to_string()), 2, 5, "int ä = 123"),
            test_token(TokenKind::Equal, 2, 8, "int ä = 123"), // ä len is 2 but thats fine because its the same when indexing
            test_token(TokenKind::Number(123, Radix::Decimal, None), 2, 10, "int ä = 123"),
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
    fn char_assign() {
        let actual = setup("char some = '1'");
        let expected = vec![
            TokenKind::Char,
            TokenKind::Ident("some".to_string()),
            TokenKind::Equal,
            TokenKind::CharLit('1'),
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
    fn non_ascii_char() {
        assert!(matches!(setup_err("'ü'")[0], ErrorKind::CharLiteralAscii(_)));
    }

    #[test]
    fn non_ascii_string() {
        // non ascii value in string is fine but in char is not
        assert_eq!(setup("\"hallö\"")[0], TokenKind::String("hallö".to_string()));
    }

    #[test]
    fn ellipsis_dot_distinction() {
        let actual = setup(".....;...");
        let expected = vec![
            TokenKind::Ellipsis,
            TokenKind::Dot,
            TokenKind::Dot,
            TokenKind::Semicolon,
            TokenKind::Ellipsis,
        ];
        assert_eq!(actual, expected);
    }

    #[test]
    fn handle_newline_string() {
        let input: String = vec!['"', 'h', 'a', '\\', 'n', 'l', '"'].into_iter().collect();
        let actual = setup(&input);

        let expected = vec![TokenKind::String("ha\nl".to_string())];

        assert_eq!(actual, expected);
    }

    #[test]
    fn handle_multiline_string() {
        let input: String = vec!['"', 'h', 'a', '\\', '\n', 'l', '"'].into_iter().collect();
        let actual = setup(&input);

        let expected = vec![TokenKind::String("hal".to_string())];

        assert_eq!(actual, expected);
    }
    #[test]
    fn whitespace_seperated_string() {
        let actual = setup(
            "
     \"one\"       \" two\"
\"three\"
",
        );

        let expected = vec![TokenKind::String("one twothree".to_string())];

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

    #[test]
    fn int_suffix() {
        assert_eq!(
            setup("1L")[0],
            TokenKind::Number(1, Radix::Decimal, Some(IntSuffix::L))
        );
        assert_eq!(
            setup("1LU")[0],
            TokenKind::Number(1, Radix::Decimal, Some(IntSuffix::UL))
        );
        assert_eq!(
            setup("1Ul")[0],
            TokenKind::Number(1, Radix::Decimal, Some(IntSuffix::UL))
        );
        assert_eq!(
            setup("1llU")[0],
            TokenKind::Number(1, Radix::Decimal, Some(IntSuffix::ULL))
        );
        assert_eq!(
            setup("1 l"),
            [
                TokenKind::Number(1, Radix::Decimal, None),
                TokenKind::Ident("l".to_string())
            ]
        );

        assert!(matches!(setup_err("1UU")[0], ErrorKind::InvalidIntSuffix(..)));
        assert!(matches!(setup_err("1lLu")[0], ErrorKind::InvalidIntSuffix(..)));
        assert!(matches!(setup_err("1p")[0], ErrorKind::InvalidIntSuffix(..)));
    }

    #[test]
    fn num_literals() {
        assert!(matches!(
            setup("0")[0],
            TokenKind::Number(0, Radix::Decimal, None)
        ));
        assert!(matches!(
            setup("07132")[0],
            TokenKind::Number(3674, Radix::Octal, None)
        ));
        assert!(matches!(
            setup("0X1aA")[0],
            TokenKind::Number(426, Radix::Hex, None)
        ));
        assert!(matches!(
            setup("0xffffffff")[0],
            TokenKind::Number(4294967295, Radix::Hex, None)
        ));

        assert!(matches!(setup_err("08")[0], ErrorKind::InvalidNumber(_, "octal")));
    }

    #[test]
    fn escaped_char() {
        assert_eq!(setup("'\\''")[0], TokenKind::CharLit(39 as char));
        assert_eq!(setup("'\\077'")[0], TokenKind::CharLit(63 as char));
        // octal 377 is the upper limit (is 255 in decimal which is 1 Byte)
        assert_eq!(setup("'\\377'")[0], TokenKind::CharLit(255 as char));

        // octal 400 is 256 and thus too big
        assert!(matches!(setup_err("'\\400'")[0], ErrorKind::InvalidEscape(_)));
        assert!(matches!(setup_err("'\\0000'")[0], ErrorKind::InvalidEscape(_)));

        assert_eq!(setup("'\\xFF'")[0], TokenKind::CharLit(255 as char));
        // 0x100 == 256
        assert!(matches!(setup_err("'\\x100'")[0], ErrorKind::InvalidEscape(_)));
    }
}
