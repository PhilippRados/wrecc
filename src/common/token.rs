use crate::common::types::*;
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
    Tilde,

    // One or two character tokens.
    Slash,
    SlashEqual,
    Star,
    StarEqual,
    Mod,
    ModEqual,
    Plus,
    PlusPlus,
    PlusEqual,
    Minus,
    MinusMinus,
    MinusEqual,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    GreaterGreater,
    GreaterGreaterEqual,
    Less,
    LessEqual,
    LessLess,
    LessLessEqual,
    Amp,
    AmpEqual,
    AmpAmp,
    Pipe,
    PipeEqual,
    PipePipe,
    Xor,
    XorEqual,
    Arrow,
    Question,
    Colon,

    // Literals.
    Ident,
    String,
    CharLit,
    Number,

    // Keywords.
    Void,
    Int,
    Char,
    Long,
    Struct,
    Union,
    Enum,
    TypeDef,
    Else,
    For,
    If,
    Return,
    While,
    Break,
    Continue,
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
            TokenType::MinusEqual => TokenKind::MinusEqual,
            TokenType::Plus => TokenKind::Plus,
            TokenType::PlusEqual => TokenKind::PlusEqual,
            TokenType::Semicolon => TokenKind::Semicolon,
            TokenType::Slash => TokenKind::Slash,
            TokenType::SlashEqual => TokenKind::SlashEqual,
            TokenType::Star => TokenKind::Star,
            TokenType::StarEqual => TokenKind::StarEqual,
            TokenType::Mod => TokenKind::Mod,
            TokenType::ModEqual => TokenKind::ModEqual,
            TokenType::Bang => TokenKind::Bang,
            TokenType::BangEqual => TokenKind::BangEqual,
            TokenType::Equal => TokenKind::Equal,
            TokenType::EqualEqual => TokenKind::EqualEqual,
            TokenType::Greater => TokenKind::Greater,
            TokenType::GreaterEqual => TokenKind::GreaterEqual,
            TokenType::GreaterGreater => TokenKind::GreaterGreater,
            TokenType::GreaterGreaterEqual => TokenKind::GreaterGreaterEqual,
            TokenType::Less => TokenKind::Less,
            TokenType::LessEqual => TokenKind::LessEqual,
            TokenType::LessLess => TokenKind::LessLess,
            TokenType::LessLessEqual => TokenKind::LessLessEqual,
            TokenType::Ident(_) => TokenKind::Ident,
            TokenType::String(_) => TokenKind::String,
            TokenType::Number(_) => TokenKind::Number,
            TokenType::Else => TokenKind::Else,
            TokenType::For => TokenKind::For,
            TokenType::If => TokenKind::If,
            TokenType::Return => TokenKind::Return,
            TokenType::While => TokenKind::While,
            TokenType::Break => TokenKind::Break,
            TokenType::Continue => TokenKind::Continue,
            TokenType::PlusPlus => TokenKind::PlusPlus,
            TokenType::MinusMinus => TokenKind::MinusMinus,
            TokenType::Amp => TokenKind::Amp,
            TokenType::AmpEqual => TokenKind::AmpEqual,
            TokenType::AmpAmp => TokenKind::AmpAmp,
            TokenType::PipePipe => TokenKind::PipePipe,
            TokenType::Pipe => TokenKind::Pipe,
            TokenType::PipeEqual => TokenKind::PipeEqual,
            TokenType::Xor => TokenKind::Xor,
            TokenType::XorEqual => TokenKind::XorEqual,
            TokenType::CharLit(_) => TokenKind::CharLit,
            TokenType::Char => TokenKind::Char,
            TokenType::Int => TokenKind::Int,
            TokenType::Long => TokenKind::Long,
            TokenType::Struct => TokenKind::Struct,
            TokenType::TypeDef => TokenKind::TypeDef,
            TokenType::Union => TokenKind::Union,
            TokenType::Enum => TokenKind::Enum,
            TokenType::Void => TokenKind::Void,
            TokenType::Tilde => TokenKind::Tilde,
            TokenType::Arrow => TokenKind::Arrow,
            TokenType::Question => TokenKind::Question,
            TokenType::Colon => TokenKind::Colon,
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
    Tilde,

    // One or two character tokens.
    Slash,
    SlashEqual,
    Star,
    StarEqual,
    Mod,
    ModEqual,
    Plus,
    PlusPlus,
    PlusEqual,
    Minus,
    MinusMinus,
    MinusEqual,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    GreaterGreater,
    GreaterGreaterEqual,
    Less,
    LessEqual,
    LessLess,
    LessLessEqual,
    Amp,
    AmpEqual,
    AmpAmp,
    Pipe,
    PipeEqual,
    PipePipe,
    Xor,
    XorEqual,
    Arrow,
    Question,
    Colon,

    // Literals.
    Ident(String),
    String(String),
    CharLit(i8),
    Number(i64),

    // Keywords.
    Void,
    Long,
    Int,
    Char,
    Struct,
    Union,
    Enum,
    TypeDef,
    Else,
    For,
    If,
    Return,
    While,
    Break,
    Continue,
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
                TokenType::MinusEqual => "'-='",
                TokenType::MinusMinus => "'--'",
                TokenType::Plus => "'+'",
                TokenType::PlusEqual => "'+='",
                TokenType::PlusPlus => "'++'",
                TokenType::Semicolon => "';'",
                TokenType::Slash => "'/'",
                TokenType::SlashEqual => "'/='",
                TokenType::Star => "'*'",
                TokenType::StarEqual => "'*='",
                TokenType::Mod => "'%'",
                TokenType::ModEqual => "'%='",
                TokenType::Bang => "'!'",
                TokenType::BangEqual => "'!='",
                TokenType::Amp => "'&'",
                TokenType::AmpEqual => "'&='",
                TokenType::AmpAmp => "'&&'",
                TokenType::Pipe => "'|'",
                TokenType::PipeEqual => "'|='",
                TokenType::PipePipe => "'||'",
                TokenType::Xor => "'^'",
                TokenType::XorEqual => "'^='",
                TokenType::Char => "'char'",
                TokenType::CharLit(_) => "'char'",
                TokenType::Int => "'int'",
                TokenType::Long => "'long'",
                TokenType::Struct => "'struct'",
                TokenType::TypeDef => "'typedef'",
                TokenType::Union => "'union'",
                TokenType::Enum => "'enum'",
                TokenType::Equal => "'='",
                TokenType::EqualEqual => "'=='",
                TokenType::Greater => "'>'",
                TokenType::GreaterEqual => "'>='",
                TokenType::GreaterGreater => "'>>'",
                TokenType::GreaterGreaterEqual => "'>>='",
                TokenType::Less => "'<'",
                TokenType::LessEqual => "'<='",
                TokenType::LessLess => "'<<'",
                TokenType::LessLessEqual => "'<<='",
                TokenType::Ident(_) => "identifier",
                TokenType::String(_) => "string",
                TokenType::Number(_) => "number",
                TokenType::Else => "'else'",
                TokenType::For => "'for'",
                TokenType::If => "'if'",
                TokenType::Return => "'return'",
                TokenType::While => "'while'",
                TokenType::Break => "'break'",
                TokenType::Continue => "'continue'",
                TokenType::Void => "'void'",
                TokenType::Tilde => "'~'",
                TokenType::Arrow => "'->'",
                TokenType::Question => "'?'",
                TokenType::Colon => "':'",
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
    pub fn default(kind: TokenType) -> Self {
        Token {
            token: kind,
            line_index: -1,
            line_string: "".to_string(),
            column: -1,
        }
    }
    pub fn unwrap_string(&self) -> String {
        match &self.token {
            TokenType::Ident(s) => s.clone(),
            TokenType::String(s) => s.clone(),
            _ => panic!("cant unwrap string on {} token", self.token),
        }
    }
    pub fn unwrap_num(&self) -> i64 {
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
        self.token == TokenType::Enum
            || self.token == TokenType::Union
            || self.token == TokenType::Struct
            || Types::into_vec().contains(&TokenKind::from(&self.token))
    }
    pub fn into_type(self) -> NEWTypes {
        assert!(self.is_type());

        NEWTypes::Primitive(match self.token {
            TokenType::Int => Types::Int,
            TokenType::Char => Types::Char,
            TokenType::Void => Types::Void,
            TokenType::Long => Types::Long,
            _ => unreachable!("only types are checked"),
        })
    }
    pub fn comp_to_binary(&self) -> TokenType {
        match self.token {
            TokenType::SlashEqual => TokenType::Slash,
            TokenType::StarEqual => TokenType::Star,
            TokenType::ModEqual => TokenType::Mod,
            TokenType::XorEqual => TokenType::Xor,
            TokenType::PipeEqual => TokenType::Pipe,
            TokenType::AmpEqual => TokenType::Amp,
            TokenType::GreaterGreaterEqual => TokenType::GreaterGreater,
            TokenType::LessLessEqual => TokenType::LessLess,
            TokenType::MinusEqual | TokenType::MinusMinus => TokenType::Minus,
            TokenType::PlusEqual | TokenType::PlusPlus => TokenType::Plus,
            _ => unreachable!("not compound token"),
        }
    }
}
