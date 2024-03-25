use crate::compiler::parser::double_peek::DoublePeek;
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
    Newline,
    String(String),
    CharLit(String),
    Ident(String),
    Number(String),
    Whitespace(String),
    Other(char),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub column: i32,
    pub line: i32,
    pub line_string: String,
}
impl Token {
    pub fn placeholder_whitespace() -> Self {
        Token {
            kind: TokenKind::Whitespace(" ".to_string()),
            column: 1,
            line: 1,
            line_string: "".to_string(),
        }
    }
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
            | TokenKind::Number(s)
            | TokenKind::CharLit(s)
            | TokenKind::Ident(s)
            | TokenKind::Whitespace(s) => s.len(),
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
            TokenKind::Number(s)
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
    raw_source: Vec<String>,
}
impl Scanner {
    pub fn new(source: String) -> Scanner {
        Scanner {
            column: 1,
            line: 1,
            raw_source: source
                .replace('\t', " ")
                .split('\n')
                .map(|s| s.to_string())
                .collect::<Vec<String>>(),
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
                    self.add_token(&mut result, TokenKind::Newline, None);
                    self.column = 1;
                    self.line += 1;
                }
                ' ' | '\t' => {
                    let (whitespace, loc) =
                        self.consume_until(&c.to_string(), |ch, _| ch != ' ' && ch != '\t', false);

                    self.add_token(&mut result, TokenKind::Whitespace(whitespace), Some(loc));
                }
                '"' => {
                    let (s, loc) = self.consume_until("\"", |ch, escaped| ch == '"' && !escaped, true);

                    self.add_token(&mut result, TokenKind::String(s), Some(loc));
                }
                '\'' => {
                    let (s, loc) = self.consume_until("'", |ch, escaped| ch == '\'' && !escaped, true);

                    self.add_token(&mut result, TokenKind::CharLit(s), Some(loc));
                }
                '/' if matches!(self.source.peek(), Some('/')) => {
                    self.source.next();
                    let (_, (newlines, col)) =
                        self.consume_until("//", |ch, _| ch == '\n' && ch == '\0', false);

                    self.line += newlines;
                    self.column = col;
                }
                '/' if matches!(self.source.peek(), Some('*')) => {
                    self.source.next();
                    let (newlines, col) = self.multiline_comment();

                    self.line += newlines;
                    self.column = col;
                }
                _ if c.is_alphabetic() || c == '_' => {
                    let (ident, loc) = self.consume_until(
                        &c.to_string(),
                        |c, _| !c.is_alphabetic() && c != '_' && !c.is_ascii_digit(),
                        false,
                    );
                    let ident = if let Some(directive) = self.directives.get(ident.as_str()) {
                        directive.clone()
                    } else {
                        TokenKind::Ident(ident)
                    };

                    self.add_token(&mut result, ident, Some(loc));
                }
                _ if c.is_ascii_digit() => {
                    let (number, loc) =
                        self.consume_until(&c.to_string(), |c, _| !c.is_ascii_digit(), false);

                    self.add_token(&mut result, TokenKind::Number(number), Some(loc));
                }
                '\\' if matches!(self.source.peek(), Some('\n')) => {
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
        consume_last: bool,
    ) -> (String, (i32, i32))
    where
        F: FnMut(char, bool) -> bool,
    {
        let mut result = String::from(start);
        let mut newlines = 0;
        let mut column = self.column + start.len() as i32;

        while let Some(peeked) = self.source.peek() {
            // if last chars are an uneven amount of backslashes then is escaped
            let is_escaped = (result.chars().rev().take_while(|c| *c == '\\').count() % 2) != 0;
            match peeked {
                '\\' if matches!(self.source.double_peek(), Some('\n')) => {
                    self.source.next();
                    self.source.next();
                    column = 1;
                    newlines += 1;
                }
                '\n' => break,
                _ if predicate(*peeked, is_escaped) => {
                    if consume_last {
                        column += 1;
                        result.push(self.source.next().unwrap());
                    }
                    break;
                }
                _ => {
                    column += 1;
                    result.push(self.source.next().unwrap());
                }
            }
        }
        (result, (newlines, column))
    }
    fn multiline_comment(&mut self) -> (i32, i32) {
        let (mut newlines, mut column) = (0, self.column + 2);

        while let Some(peeked) = self.source.peek() {
            match peeked {
                '*' if matches!(self.source.double_peek(), Some('/')) => {
                    self.source.next();
                    self.source.next();
                    column += 2;
                    break;
                }
                _ => {
                    if *peeked == '\n' {
                        newlines += 1;
                        column = 1;
                    } else {
                        column += 1;
                    }
                    self.source.next();
                }
            }
        }
        (newlines, column)
    }
    fn add_token(&mut self, result: &mut Vec<Token>, kind: TokenKind, location: Option<(i32, i32)>) {
        let token = Token {
            column: self.column,
            line: self.line,
            line_string: self.raw_source[(self.line - 1) as usize].clone(),
            kind,
        };
        if let Some((newlines, column)) = location {
            self.column = column;
            self.line += newlines;
        } else {
            self.column += token.len() as i32;
        }
        result.push(token);
    }
}

impl DoublePeek<char> {
    pub fn peek(&self) -> Option<&char> {
        self.inner.front()
    }
    pub fn double_peek(&self) -> Option<&char> {
        self.inner.get(1)
    }
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    fn setup(input: &str) -> Vec<Token> {
        Scanner::new(input.to_string()).scan_token()
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
            TokenKind::Number("1".to_string()),
            TokenKind::Ident("first".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Number("2".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("some23".to_string()),
            TokenKind::Other(':'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("more".to_string()),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn escaped_char() {
        let actual = setup_tokenkind("char c = '\'';");
        let expected = vec![
            TokenKind::Ident("char".to_string()),
            TokenKind::Ident("c".to_string()),
            TokenKind::Other('='),
            TokenKind::CharLit("\\'".to_string()),
        ];
    }

    #[test]
    fn escaped_string() {
        let actual = setup_tokenkind("char *c = \"s   \\\"  else\";");
        let expected = vec![
            TokenKind::Ident("char".to_string()),
            TokenKind::Ident("c".to_string()),
            TokenKind::Other('='),
            TokenKind::String("s   \"  else".to_string()),
        ];
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
            TokenKind::Number("0".to_string()),
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
            TokenKind::Number("1".to_string()),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Other('<'),
            TokenKind::Whitespace(" ".to_string()),
            TokenKind::Ident("num".to_string()),
            TokenKind::Newline,
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn skips_multiline_whitespace() {
        let actual = setup_tok_line("  \\\n \n#include");
        let expected = vec![
            (TokenKind::Whitespace("   ".to_string()), 1),
            (TokenKind::Newline, 2),
            (TokenKind::Hash, 3),
            (TokenKind::Include, 3),
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn skips_multiline_whitespace2() {
        let actual = setup_tokenkind("\\\n  \\\n\n#include");
        let expected = vec![
            TokenKind::Whitespace("  ".to_string()),
            TokenKind::Newline,
            TokenKind::Hash,
            TokenKind::Include,
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn backslash_without_escape() {
        let actual = setup_tokenkind("\\some\n#include");
        let expected = vec![
            TokenKind::Other('\\'),
            TokenKind::Ident("some".to_string()),
            TokenKind::Newline,
            TokenKind::Hash,
            TokenKind::Include,
        ];

        assert_eq!(actual, expected);
    }

    #[test]
    fn escpaped_newline() {
        let actual = setup_tokenkind("1 2   \\\n\\3\n   \\\nwhat");
        let expected = setup_tokenkind("1 2   \\3\n   what");

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiline_comment() {
        let actual = setup_tokenkind("1 /*2   \\\n\\\n3\n   \\*/\nwhat");
        let expected = setup_tokenkind("1 \nwhat");

        assert_eq!(actual, expected);
    }

    #[test]
    fn escaped_newline_single_comment() {
        let actual = setup_tokenkind("hello # // what is \\\n this 3\n  end");
        let expected = setup_tokenkind("hello # \n  end");

        assert_eq!(actual, expected);
    }

    #[test]
    fn numbers_and_idents() {
        let actual = setup_tokenkind("12323_hello12_2;");
        let expected = vec![
            TokenKind::Number("12323".to_string()),
            TokenKind::Ident("_hello12_2".to_string()),
            TokenKind::Other(';'),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_ident() {
        let actual = setup_tok_line("He\\\n12lo\\\n what \\\nit");
        let expected = vec![
            (TokenKind::Ident("He12lo".to_string()), 1),
            (TokenKind::Whitespace(" ".to_string()), 3),
            (TokenKind::Ident("what".to_string()), 3),
            (TokenKind::Whitespace(" ".to_string()), 3),
            (TokenKind::Ident("it".to_string()), 4),
        ];

        assert_eq!(actual, expected);
    }
    #[test]
    fn multiline_number() {
        let actual = setup_tok_line("123\\\n32\n12\\3\\\n4");
        let expected = vec![
            (TokenKind::Number("12332".to_string()), 1),
            (TokenKind::Newline, 2),
            (TokenKind::Number("12".to_string()), 3),
            (TokenKind::Other('\\'), 3),
            (TokenKind::Number("34".to_string()), 3),
        ];

        assert_eq!(actual, expected);
    }
}
