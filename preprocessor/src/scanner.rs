use compiler::DoublePeek;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Hash,
    Include,
    Define,
    Defined,
    Undef,
    Ifdef,
    Ifndef,
    If,
    Elif,
    Else,
    Endif,
    String(String),
    CharLit(String),
    Ident(String),
    Newline,
    Whitespace(String),
    Comment(String),
    Other(char),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub column: i32,
    pub line: i32,
}
impl Token {
    pub fn len(&self) -> usize {
        match &self.kind {
            TokenKind::Newline => 0,
            TokenKind::Hash | TokenKind::Other(_) => 1,
            TokenKind::If => 2,
            TokenKind::Else | TokenKind::Elif => 4,
            TokenKind::Undef | TokenKind::Ifdef | TokenKind::Endif => 5,
            TokenKind::Define | TokenKind::Ifndef => 6,
            TokenKind::Include | TokenKind::Defined => 7,
            TokenKind::String(s)
            | TokenKind::CharLit(s)
            | TokenKind::Ident(s)
            | TokenKind::Whitespace(s)
            | TokenKind::Comment(s) => s.len(),
        }
    }
}
impl TokenKind {
    // returns string of all valid identifiers
    pub fn as_ident(&self) -> Option<String> {
        match self {
            TokenKind::Ident(_)
            | TokenKind::Include
            | TokenKind::Define
            | TokenKind::Defined
            | TokenKind::Undef
            | TokenKind::Ifdef
            | TokenKind::Ifndef
            | TokenKind::If
            | TokenKind::Elif
            | TokenKind::Else
            | TokenKind::Endif => Some(self.to_string()),
            _ => None,
        }
    }
}
impl ToString for TokenKind {
    fn to_string(&self) -> String {
        match self {
            TokenKind::Hash => "#".to_string(),
            TokenKind::Include => "include".to_string(),
            TokenKind::Define => "define".to_string(),
            TokenKind::Defined => "defined".to_string(),
            TokenKind::Undef => "undef".to_string(),
            TokenKind::Ifdef => "ifdef".to_string(),
            TokenKind::Ifndef => "ifndef".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Elif => "elif".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::Endif => "endif".to_string(),
            TokenKind::Newline => "\n".to_string(),
            TokenKind::Comment(s)
            | TokenKind::String(s)
            | TokenKind::CharLit(s)
            | TokenKind::Ident(s)
            | TokenKind::Whitespace(s) => s.to_string(),
            TokenKind::Other(c) => c.to_string(),
        }
    }
}

pub struct Scanner {
    source: DoublePeek<char>,
    directives: HashMap<&'static str, TokenKind>,
    column: i32,
    line: i32,
}
impl Scanner {
    pub fn new(source: &str) -> Scanner {
        Scanner {
            column: 1,
            line: 1,
            source: DoublePeek::new(source.chars().collect::<Vec<char>>()),
            directives: HashMap::from([
                ("include", TokenKind::Include),
                ("define", TokenKind::Define),
                ("defined", TokenKind::Defined),
                ("undef", TokenKind::Undef),
                ("ifdef", TokenKind::Ifdef),
                ("ifndef", TokenKind::Ifndef),
                ("if", TokenKind::If),
                ("elif", TokenKind::Elif),
                ("else", TokenKind::Else),
                ("endif", TokenKind::Endif),
            ]),
        }
    }
    pub fn scan_token(mut self) -> Vec<Token> {
        let mut result = Vec::new();

        while let Some(c) = self.source.next() {
            match c {
                '#' => self.add_token(&mut result, TokenKind::Hash, None),
                '\n' => {
                    let token = self.add_token(&mut result, TokenKind::Newline, None);
                    self.column = 1;
                    self.line += 1;

                    token
                }
                ' ' | '\t' => {
                    let (whitespace, newlines) =
                        self.consume_until(&c.to_string(), |ch| ch != ' ' && ch != '\t', false);

                    self.add_token(
                        &mut result,
                        TokenKind::Whitespace(whitespace),
                        Some(newlines),
                    )
                }
                '"' => {
                    let (s, newlines) = self.consume_until("\"", |ch| ch == '"', true);

                    self.add_token(&mut result, TokenKind::String(s), Some(newlines))
                }
                '\'' => {
                    let (s, newlines) = self.consume_until("'", |ch| ch == '\'', true);

                    self.add_token(&mut result, TokenKind::CharLit(s), Some(newlines))
                }
                '/' if matches!(self.source.peek(), Ok('/')) => {
                    self.source.next();
                    let (comment, newlines) =
                        self.consume_until("//", |ch| ch == '\n' && ch == '\0', false);

                    self.add_token(&mut result, TokenKind::Comment(comment), Some(newlines))
                }
                '/' if matches!(self.source.peek(), Ok('*')) => {
                    self.source.next();
                    let (comment, newlines) = self.multiline_comment();

                    self.add_token(&mut result, TokenKind::Comment(comment), Some(newlines))
                }
                _ if c.is_alphabetic() || c == '_' => {
                    let (ident, newlines) = self.consume_until(
                        &c.to_string(),
                        |c| !c.is_alphabetic() && c != '_' && !c.is_ascii_digit(),
                        false,
                    );
                    let ident = if let Some(directive) = self.directives.get(ident.as_str()) {
                        directive.clone()
                    } else {
                        TokenKind::Ident(ident)
                    };

                    self.add_token(&mut result, ident, Some(newlines))
                }
                '\\' if matches!(self.source.peek(), Ok('\n')) => {
                    // skip over escaped newline
                    self.source.next();
                    self.line += 1;
                    self.column = 1;
                }
                _ => self.add_token(&mut result, TokenKind::Other(c), None),
            }
        }
        result
    }
    fn consume_until<F>(
        &mut self,
        start: &str,
        mut predicate: F,
        is_string: bool,
    ) -> (String, usize)
    where
        F: FnMut(char) -> bool,
    {
        let mut result = String::from(start);
        let mut newlines = 0;

        while let Ok(peeked) = self.source.peek() {
            match peeked {
                '\\' if matches!(self.source.double_peek(), Ok('\n')) => {
                    self.source.next();
                    self.source.next();
                    self.column = 1;
                    newlines += 1;
                }
                '\n' => break,
                _ if predicate(*peeked) => {
                    if is_string {
                        result.push(self.source.next().unwrap());
                    }
                    break;
                }
                _ => {
                    result.push(self.source.next().unwrap());
                }
            }
        }
        (result, newlines)
    }
    fn multiline_comment(&mut self) -> (String, usize) {
        let mut result = String::from("/*");
        let mut newlines = 0;

        while let Ok(peeked) = self.source.peek() {
            match peeked {
                '*' if matches!(self.source.double_peek(), Ok('/')) => {
                    result.push(self.source.next().unwrap());
                    result.push(self.source.next().unwrap());
                    break;
                }
                _ => {
                    if *peeked == '\n' {
                        newlines += 1;
                        self.column = 1;
                    }
                    result.push(self.source.next().unwrap());
                }
            }
        }
        (result, newlines)
    }
    fn add_token(&mut self, result: &mut Vec<Token>, kind: TokenKind, newlines: Option<usize>) {
        let token = Token {
            column: self.column,
            line: self.line,
            kind,
        };
        self.column += token.len() as i32;
        if let Some(newlines) = newlines {
            self.line += newlines as i32;
        }
        result.push(token);
    }
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    fn setup(input: &str) -> Vec<Token> {
        Scanner::new(input).scan_token()
    }
    fn setup_tokenkind(input: &str) -> Vec<TokenKind> {
        setup(input).into_iter().map(|t| t.kind).collect()
    }
    fn setup_tok_line(input: &str) -> Vec<(TokenKind, i32)> {
        setup(input).into_iter().map(|t| (t.kind, t.line)).collect()
    }

    #[test]
    fn simple_pp_directive() {
        let actual = setup_tokenkind("#  include \"'some'\"");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::Whitespace("  ".to_string()),
            TokenKind::Include,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::String("\"'some'\"".to_string()),
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn string() {
        let actual = setup_tokenkind("#define \"some/* #*/define\"");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::Define,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::String("\"some/* #*/define\"".to_string()),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn ident() {
        let actual = setup_tokenkind("1first 2 some23: more");
        let expected = vec![
            TokenKind::Other('1'),
            TokenKind::Ident("first".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('2'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("some23".to_string()),
            TokenKind::Other(':'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("more".to_string()),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn macro_name() {
        let actual = setup_tokenkind("#define NULL((void *)0)");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::Define,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("NULL".to_string()),
            TokenKind::Other('('),
            TokenKind::Other('('),
            TokenKind::Ident("void".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('*'),
            TokenKind::Other(')'),
            TokenKind::Other('0'),
            TokenKind::Other(')'),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_escaped() {
        let actual = setup_tok_line(" \"some\\\n\\else\"");
        let expected = vec![
            (TokenKind::Whitespace(" ".to_string()), 1),
            (TokenKind::String("\"some\\else\"".to_string()), 1),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_multiple_escapes() {
        let actual = setup_tok_line(" \"some\\\n\nmore\"");
        let expected = vec![
            (TokenKind::Whitespace(" ".to_string()), 1),
            (TokenKind::String("\"some".to_string()), 1),
            (TokenKind::Newline, 2),
            (TokenKind::Ident("more".to_string()), 3),
            (TokenKind::String("\"".to_string()), 3),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_string_unescaped() {
        let actual = setup_tok_line(" \"some\nmore\"");
        let expected = vec![
            (TokenKind::Whitespace(" ".to_string()), 1),
            (TokenKind::String("\"some".to_string()), 1),
            (TokenKind::Newline, 1),
            (TokenKind::Ident("more".to_string()), 2),
            (TokenKind::String("\"".to_string()), 2),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn if_const_expr() {
        let actual = setup_tokenkind("#if 1 < num\n");
        let expected = vec![
            TokenKind::Hash,
            TokenKind::If,
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('1'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('<'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("num".to_string()),
            TokenKind::Newline,
        ];

        assert_eq!(actual, expected);
    }
}
