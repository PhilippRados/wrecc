use crate::common::types::Types;
use std::fmt::Display;

#[derive(PartialEq, Clone, Debug)]
pub enum TokenKind {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Comma,
    Dot,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Plus,
    PlusPlus,
    Minus,
    MinusMinus,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Amp,
    AmpAmp,
    PipePipe,

    // Literals.
    Ident,
    String,
    CharLit,
    Number,

    // Keywords.
    Void,
    Int,
    Char,
    Else,
    For,
    If,
    Return,
    While,
    Print,

    Eof,
}

impl From<&TokenType> for TokenKind {
    fn from(token: &TokenType) -> Self {
        match token {
            TokenType::LeftParen => TokenKind::LeftParen,
            TokenType::RightParen => TokenKind::RightParen,
            TokenType::LeftBrace => TokenKind::LeftBrace,
            TokenType::RightBrace => TokenKind::RightBrace,
            TokenType::LeftBracket => TokenKind::LeftBracket,
            TokenType::RightBracket => TokenKind::RightBracket,
            TokenType::Comma => TokenKind::Comma,
            TokenType::Dot => TokenKind::Dot,
            TokenType::Minus => TokenKind::Minus,
            TokenType::Plus => TokenKind::Plus,
            TokenType::Semicolon => TokenKind::Semicolon,
            TokenType::Slash => TokenKind::Slash,
            TokenType::Star => TokenKind::Star,
            TokenType::Bang => TokenKind::Bang,
            TokenType::BangEqual => TokenKind::BangEqual,
            TokenType::Equal => TokenKind::Equal,
            TokenType::EqualEqual => TokenKind::EqualEqual,
            TokenType::Greater => TokenKind::Greater,
            TokenType::GreaterEqual => TokenKind::GreaterEqual,
            TokenType::Less => TokenKind::Less,
            TokenType::LessEqual => TokenKind::LessEqual,
            TokenType::Ident(_) => TokenKind::Ident,
            TokenType::String(_) => TokenKind::String,
            TokenType::Number(_) => TokenKind::Number,
            TokenType::Else => TokenKind::Else,
            TokenType::For => TokenKind::For,
            TokenType::If => TokenKind::If,
            TokenType::Print => TokenKind::Print,
            TokenType::Return => TokenKind::Return,
            TokenType::While => TokenKind::While,
            TokenType::Eof => TokenKind::Eof,
            TokenType::PlusPlus => TokenKind::PlusPlus,
            TokenType::MinusMinus => TokenKind::MinusMinus,
            TokenType::Amp => TokenKind::Amp,
            TokenType::AmpAmp => TokenKind::AmpAmp,
            TokenType::PipePipe => TokenKind::PipePipe,
            TokenType::CharLit(_) => TokenKind::CharLit,
            TokenType::Char => TokenKind::Char,
            TokenType::Int => TokenKind::Int,
            TokenType::Void => TokenKind::Void,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Comma,
    Dot,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Plus,
    PlusPlus,
    Minus,
    MinusMinus,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Amp,
    AmpAmp,
    PipePipe,

    // Literals.
    Ident(String),
    String(String),
    CharLit(i8),
    Number(i32),

    // Keywords.
    Void,
    Int,
    Char,
    Else,
    For,
    If,
    Return,
    While,
    Print,

    Eof,
}
impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TokenType::LeftParen => "')'",
                TokenType::RightParen => "')'",
                TokenType::LeftBrace => "'{'",
                TokenType::RightBrace => "'}'",
                TokenType::LeftBracket => "'['",
                TokenType::RightBracket => "']'",
                TokenType::Comma => "','",
                TokenType::Dot => "'.'",
                TokenType::Minus => "'-'",
                TokenType::MinusMinus => "'--'",
                TokenType::Plus => "'+'",
                TokenType::PlusPlus => "'++'",
                TokenType::Semicolon => "';'",
                TokenType::Slash => "'/'",
                TokenType::Star => "'*'",
                TokenType::Bang => "'!'",
                TokenType::BangEqual => "'!='",
                TokenType::Amp => "'&'",
                TokenType::AmpAmp => "'&&'",
                TokenType::PipePipe => "'||'",
                TokenType::Char => "'char'",
                TokenType::CharLit(_) => "'char'",
                TokenType::Int => "'int'",
                TokenType::Equal => "'='",
                TokenType::EqualEqual => "'=='",
                TokenType::Greater => "'>'",
                TokenType::GreaterEqual => "'>='",
                TokenType::Less => "'<'",
                TokenType::LessEqual => "'<='",
                TokenType::Ident(_) => "identifier",
                TokenType::String(_) => "string",
                TokenType::Number(_) => "number",
                TokenType::Else => "'else'",
                TokenType::For => "'for'",
                TokenType::If => "'if'",
                TokenType::Print => "'print'",
                TokenType::Return => "'return'",
                TokenType::While => "'while'",
                TokenType::Eof => "<EOF>",
                TokenType::Void => "'void'",
            }
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub token: TokenType,
    pub line_index: i32,
    pub column: i32,
    pub line_string: String,
}
impl Token {
    pub fn new(token: TokenType, line_index: i32, column: i32, line_string: String) -> Self {
        Token {
            token,
            line_index,
            column,
            line_string,
        }
    }
    pub fn unwrap_string(&self) -> String {
        match &self.token {
            TokenType::Ident(s) => s.clone(),
            TokenType::String(s) => s.clone(),
            _ => panic!("cant unwrap string on {} token", self.token),
        }
    }
    pub fn unwrap_num(&self) -> i32 {
        match &self.token {
            TokenType::Number(n) => *n,
            _ => panic!("cant unwrap number on {} token", self.token),
        }
    }
    pub fn unwrap_char(&self) -> i8 {
        match &self.token {
            TokenType::CharLit(c) => *c,
            _ => panic!("cant unwrap char on {} token", self.token),
        }
    }
    pub fn is_type(&self) -> bool {
        Types::into_vec().contains(&TokenKind::from(&self.token))
    }
    pub fn into_type(self) -> Types {
        assert!(self.is_type());

        match self.token {
            TokenType::Int => Types::Int,
            TokenType::Char => Types::Char,
            TokenType::Void => Types::Void,
            _ => unreachable!("only types are checked"),
        }
    }
}
