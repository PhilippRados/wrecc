use crate::common::{error::*, token::*};
use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

pub struct Scanner<'a> {
    source: Peekable<Chars<'a>>,
    pub raw_source: Vec<String>,
    // line number of source after preprocessor
    pub actual_line: i32,
    // line number of unpreprocessed source
    pub original_line: i32,
    pub column: i32,
    pub filenames: Vec<String>,
    keywords: HashMap<&'a str, TokenType>,
}
impl<'a> Scanner<'a> {
    pub fn new(filename: &'a str, source: &'a str) -> Self {
        Scanner {
            source: source.chars().peekable(),
            raw_source: source
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
            filenames: vec![filename.to_string()],
            actual_line: 1,
            original_line: 1,
            column: 1,
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
        match self.source.next_if_eq(&expected) {
            Some(_) => if_match,
            None => if_not,
        }
    }
    fn add_token(&mut self, tokens: &mut Vec<Token>, current_token: TokenType) {
        tokens.push(Token::new(
            current_token.clone(),
            self.line_index(),
            self.column(),
            self.line_string(),
            self.filename(),
        ));
        self.column += current_token.len() as i32;
    }
    pub fn scan_token(&mut self) -> Result<Vec<Token>, Vec<Error>> {
        let mut errors: Vec<Error> = Vec::new();
        let mut tokens: Vec<Token> = Vec::new();

        while let Some(c) = self.source.next() {
            match c {
                '[' => self.add_token(&mut tokens, TokenType::LeftBracket),
                ']' => self.add_token(&mut tokens, TokenType::RightBracket),
                '(' => self.add_token(&mut tokens, TokenType::LeftParen),
                ')' => self.add_token(&mut tokens, TokenType::RightParen),
                '{' => self.add_token(&mut tokens, TokenType::LeftBrace),
                '}' => self.add_token(&mut tokens, TokenType::RightBrace),
                ',' => self.add_token(&mut tokens, TokenType::Comma),
                ';' => self.add_token(&mut tokens, TokenType::Semicolon),
                '~' => self.add_token(&mut tokens, TokenType::Tilde),
                '?' => self.add_token(&mut tokens, TokenType::Question),
                ':' => self.add_token(&mut tokens, TokenType::Colon),
                '.' => {
                    if self.matches('.') {
                        if self.matches('.') {
                            self.add_token(&mut tokens, TokenType::Ellipsis);
                        } else {
                            // since only single lookahead have to add two seperate dots
                            self.add_token(&mut tokens, TokenType::Dot);
                            self.add_token(&mut tokens, TokenType::Dot);
                        }
                    } else {
                        self.add_token(&mut tokens, TokenType::Dot)
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
                    self.add_token(&mut tokens, token);
                }
                '+' => {
                    let mut token = TokenType::Plus;
                    if self.matches('+') {
                        token = TokenType::PlusPlus;
                    } else if self.matches('=') {
                        token = TokenType::PlusEqual;
                    }
                    self.add_token(&mut tokens, token);
                }
                '|' => {
                    let mut token = TokenType::Pipe;
                    if self.matches('|') {
                        token = TokenType::PipePipe;
                    } else if self.matches('=') {
                        token = TokenType::PipeEqual;
                    }
                    self.add_token(&mut tokens, token);
                }
                '&' => {
                    let mut token = TokenType::Amp;
                    if self.matches('&') {
                        token = TokenType::AmpAmp;
                    } else if self.matches('=') {
                        token = TokenType::AmpEqual;
                    }
                    self.add_token(&mut tokens, token);
                }
                '<' => {
                    let mut token = TokenType::Less;
                    if self.matches('<') {
                        token = self.match_next('=', TokenType::LessLessEqual, TokenType::LessLess);
                    } else if self.matches('=') {
                        token = TokenType::LessEqual;
                    }
                    self.add_token(&mut tokens, token);
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
                    self.add_token(&mut tokens, token);
                }
                '^' => {
                    let token = self.match_next('=', TokenType::XorEqual, TokenType::Xor);
                    self.add_token(&mut tokens, token);
                }
                '*' => {
                    let token = self.match_next('=', TokenType::StarEqual, TokenType::Star);
                    self.add_token(&mut tokens, token);
                }
                '%' => {
                    let token = self.match_next('=', TokenType::ModEqual, TokenType::Mod);
                    self.add_token(&mut tokens, token);
                }

                '!' => {
                    let token = self.match_next('=', TokenType::BangEqual, TokenType::Bang);
                    self.add_token(&mut tokens, token);
                }
                '=' => {
                    let token = self.match_next('=', TokenType::EqualEqual, TokenType::Equal);
                    self.add_token(&mut tokens, token);
                }

                '/' => {
                    if self.matches('/') {
                        consume_while(&mut self.source, |c| c != '\n' && c != '\0', false);
                    } else if self.matches('*') {
                        // parse multiline comment
                        self.column += 2;
                        while let Some(c) = self.source.next() {
                            match c {
                                '\n' => {
                                    self.newline();
                                }
                                '*' if self.matches('/') => {
                                    self.column += 2;
                                    break;
                                }
                                _ => self.column += 1,
                            }
                        }
                    } else {
                        let token = self.match_next('=', TokenType::SlashEqual, TokenType::Slash);
                        self.add_token(&mut tokens, token);
                    }
                }
                ' ' | '\r' | '\t' => self.column += 1,
                '\n' => self.newline(),

                '"' => match self.string() {
                    Ok(string) => self.add_token(&mut tokens, TokenType::String(string.clone())),
                    Err(e) => errors.push(e),
                },
                '\'' => match self.char_lit() {
                    Ok(char) => self.add_token(&mut tokens, TokenType::CharLit(char as i8)),
                    Err(e) => errors.push(e),
                },
                '#' => {
                    // to properly locate error in header-file need to change source-file and index when showing error
                    match consume_while(&mut self.source, |c| c != ':' && c != '\n', true).as_ref()
                    {
                        "pro" => {
                            let header_name = consume_while(&mut self.source, |c| c != '\n', true);

                            self.actual_line += 1;
                            self.original_line = 1;
                            self.filenames.push(header_name);
                        }
                        "epi" => {
                            let num = consume_while(&mut self.source, |c| c != '\0', true);

                            self.original_line = num.parse::<i32>().unwrap();
                            self.filenames.pop();
                        }
                        "line" => {
                            let num = consume_while(&mut self.source, |c| c != '\n', true);

                            self.actual_line += 1;
                            self.original_line = num.parse::<i32>().unwrap();
                        }
                        other => {
                            errors.push(Error::new(self, ErrorKind::UnexpectedChar(c)));
                            self.column += other.len() as i32;
                        }
                    }
                    self.column = 1;
                }

                _ => {
                    if c.is_ascii_digit() {
                        // Number
                        let num = c.to_string()
                            + &consume_while(&mut self.source, |c| c.is_ascii_digit(), false);

                        match num.parse::<i64>() {
                            Ok(n) => self.add_token(&mut tokens, TokenType::Number(n)),
                            Err(e) => {
                                errors.push(Error::new(
                                    self,
                                    ErrorKind::InvalidNumber(e.kind().clone()),
                                ));
                                self.column += num.len() as i32;
                                continue;
                            }
                        }
                    } else if c.is_alphabetic() || c == '_' {
                        // Identifier
                        let ident = c.to_string()
                            + &consume_while(
                                &mut self.source,
                                |c| c.is_alphabetic() || c == '_' || c.is_ascii_digit(),
                                false,
                            );

                        if let Some(kw) = self.keywords.get(ident.as_str()) {
                            self.add_token(&mut tokens, kw.clone());
                        } else {
                            // use 0 as placeholder value for symbol table index
                            self.add_token(&mut tokens, TokenType::Ident(ident, 0))
                        }
                    } else {
                        errors.push(Error::new(self, ErrorKind::UnexpectedChar(c)));

                        let c = format!("{}", c);
                        let raw_c = format!("{:?}", c);
                        let raw_c = &raw_c[1..raw_c.len() - 1];

                        // If character printable then length is 1, if not it's 0
                        let len: i32 = (c == raw_c).into();

                        self.column += len;
                    }
                }
            }
        }
        if errors.is_empty() {
            Ok(tokens)
        } else {
            Err(errors)
        }
    }
    fn newline(&mut self) {
        self.actual_line += 1;
        self.original_line += 1;
        self.column = 1
    }

    fn matches(&mut self, expected: char) -> bool {
        match self.source.peek() {
            Some(v) => {
                if *v != expected {
                    return false;
                }
            }
            None => return false,
        }
        self.source.next();
        true
    }
    fn char_lit(&mut self) -> Result<char, Error> {
        let mut char = self
            .source
            .next()
            .ok_or(Error::new(self, ErrorKind::Eof("character literal")))?;
        if char == '\\' {
            let char_to_escape = self
                .source
                .next()
                .ok_or(Error::new(self, ErrorKind::Eof("character literal")))?;
            char = match self.escape_char(char_to_escape) {
                Ok(c) => c,
                Err(e) => {
                    consume_while(&mut self.source, |c| c != '\'', true);
                    return Err(e);
                }
            }
        }
        if !self.matches('\'') {
            // finish parsing the char so that scanner synchronizes
            consume_while(&mut self.source, |c| c != '\'', true);
            return Err(Error::new(self, ErrorKind::CharLiteralQuotes));
        }
        if !char.is_ascii() {
            return Err(Error::new(self, ErrorKind::CharLiteralAscii(char)));
        };

        Ok(char)
    }
    fn escape_char(&mut self, char_to_escape: char) -> Result<char, Error> {
        match char_to_escape {
            '0' => Ok('\0'),
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            't' => Ok('\t'),
            '\\' => Ok('\\'),
            '\'' => Ok('\''),
            '\"' => Ok('\"'),
            _ => Err(Error::new(self, ErrorKind::InvalidEscape(char_to_escape))),
        }
    }

    fn string(&mut self) -> Result<String, Error> {
        let mut last_char = '\0';
        let mut result = String::new();

        while let Some(c) = self.source.next() {
            if c == '"' {
                last_char = c;
                break;
            }
            // handle multiline-strings
            if c == '\n' {
                if last_char == '\\' {
                    self.newline();

                    last_char = c;
                    result.pop();
                } else {
                    let err = Err(Error::new(self, ErrorKind::UnterminatedString));
                    self.newline();

                    return err;
                }
            } else {
                last_char = c;
                result.push(c);
            }
        }

        if last_char != '"' {
            return Err(Error::new(self, ErrorKind::UnterminatedString));
        }

        Ok(result)
    }
}

// Consumes the char-string until an expected character is found.
// if included flag is true then iterator also consumes expected char but expected char isnt included in return String
pub fn consume_while<F>(source: &mut Peekable<Chars>, mut predicate: F, included: bool) -> String
where
    F: FnMut(char) -> bool,
{
    let mut consumed = String::new();

    match included {
        true => consumed = source.by_ref().take_while(|c| predicate(*c)).collect(),
        false => {
            while let Some(v) = source.by_ref().next_if(|c| predicate(*c)) {
                consumed.push(v);
            }
        }
    }

    consumed
}

impl<'a> Location for Scanner<'a> {
    fn line_index(&self) -> i32 {
        self.original_line
    }
    fn column(&self) -> i32 {
        self.column
    }
    fn line_string(&self) -> String {
        self.raw_source[(self.actual_line - 1) as usize].clone()
    }

    fn filename(&self) -> String {
        self.filenames.last().unwrap().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_generic(input: &str) -> Vec<Token> {
        let mut scanner = Scanner::new("", input);
        if let Ok(tokens) = scanner.scan_token() {
            tokens
        } else {
            unreachable!("want to test successfull scan")
        }
    }
    fn setup_generic_err(input: &str) -> Vec<Error> {
        let mut scanner = Scanner::new("", input);
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
            filename: "".to_string(),
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
            test_token(TokenType::Ident("this".to_string(), 0), 3, 2, "!this"),
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
            TokenType::Ident("some".to_string(), 0),
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
                TokenType::Ident("some_long".to_string(), 0),
                1,
                5,
                "int some_long;",
            ),
            test_token(TokenType::Semicolon, 1, 14, "int some_long;"),
            test_token(TokenType::While, 2, 1, "while (val >= 12) {*p = val}"),
            test_token(TokenType::LeftParen, 2, 7, "while (val >= 12) {*p = val}"),
            test_token(
                TokenType::Ident("val".to_string(), 0),
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
                TokenType::Ident("p".to_string(), 0),
                2,
                21,
                "while (val >= 12) {*p = val}",
            ),
            test_token(TokenType::Equal, 2, 23, "while (val >= 12) {*p = val}"),
            test_token(
                TokenType::Ident("val".to_string(), 0),
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
                filename: String::from(""),
                line_string: "int c = 0$".to_string(),
                kind: ErrorKind::UnexpectedChar('$'),
            },
            Error {
                line_index: 3,
                column: 1,
                filename: String::from(""),
                line_string: "‘ ∞".to_string(),
                kind: ErrorKind::UnexpectedChar('‘'),
            },
            Error {
                line_index: 3,
                column: 3,
                filename: String::from(""),
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
            test_token(TokenType::Ident("ä".to_string(), 0), 2, 5, "int ä = 123"),
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
            filename: String::from(""),
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
            TokenType::Ident("some".to_string(), 0),
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
    fn consume_while_included() {
        let mut input = "pro: <here.h>".chars().peekable();
        let actual = consume_while(&mut input, |c| c != ':', true);

        let expected = "pro";
        let expected_steam = " <here.h>";

        assert_eq!(actual, expected);
        assert_eq!(input.collect::<String>(), expected_steam);
    }
    #[test]
    fn consume_while_excluded() {
        let mut input = "pro: <here.h>".chars().peekable();
        let actual = consume_while(&mut input, |c| c != ':', false);

        let expected = "pro";
        let expected_steam = ": <here.h>";

        assert_eq!(actual, expected);
        assert_eq!(input.collect::<String>(), expected_steam);
    }

    #[test]
    fn handle_newline_string() {
        let input: String = vec!['"', 'h', 'a', '\\', 'n', 'l', '"']
            .into_iter()
            .collect();

        let mut scanner = Scanner::new("", &input);
        let actual: Vec<TokenType> = scanner
            .scan_token()
            .unwrap()
            .into_iter()
            .map(|e| e.token)
            .collect();

        let expected = vec![TokenType::String("ha\\nl".to_string())];

        assert_eq!(actual, expected);

        // doesn't increase line_index if newline in string
        assert_eq!(scanner.actual_line, 1);
    }

    #[test]
    fn handle_multiline_string() {
        let input: String = vec!['"', 'h', 'a', '\\', '\n', 'l', '"']
            .into_iter()
            .collect();

        let mut scanner = Scanner::new("", &input);
        let actual: Vec<TokenType> = scanner
            .scan_token()
            .unwrap()
            .into_iter()
            .map(|e| e.token)
            .collect();
        let expected = vec![TokenType::String("hal".to_string())];

        assert_eq!(actual, expected);

        // increases line_index if multiline-string
        assert_eq!(scanner.actual_line, 2);
    }
    #[test]
    fn multiline_string_err() {
        let input: String = vec!['"', 'h', 'a', '\n', 'l', '"'].into_iter().collect();

        let actual = setup_generic_err(&input);
        let expected = vec![
            Error {
                line_index: 1,
                column: 1,
                filename: String::from(""),
                line_string: "\"ha".to_string(),
                kind: ErrorKind::UnterminatedString,
            },
            Error {
                line_index: 2,
                line_string: "l\"".to_string(),
                column: 2,
                filename: "".to_string(),
                kind: ErrorKind::UnterminatedString,
            },
        ];

        assert_eq!(actual, expected);
    }
}
