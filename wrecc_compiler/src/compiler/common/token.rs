use crate::compiler::common::error::Location;
use crate::compiler::parser::hir::decl::SpecifierKind;
use std::fmt::Display;
use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq)]
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
    Ellipsis,

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
    Switch,
    Case,
    Default,
    Return,
    While,
    Do,
    Break,
    Continue,
    Sizeof,
    Goto,
}
impl TokenKind {
    pub fn comp_to_binary(&self) -> TokenKind {
        match self {
            TokenKind::SlashEqual => TokenKind::Slash,
            TokenKind::StarEqual => TokenKind::Star,
            TokenKind::ModEqual => TokenKind::Mod,
            TokenKind::XorEqual => TokenKind::Xor,
            TokenKind::PipeEqual => TokenKind::Pipe,
            TokenKind::AmpEqual => TokenKind::Amp,
            TokenKind::GreaterGreaterEqual => TokenKind::GreaterGreater,
            TokenKind::LessLessEqual => TokenKind::LessLess,
            TokenKind::MinusEqual | TokenKind::MinusMinus => TokenKind::Minus,
            TokenKind::PlusEqual | TokenKind::PlusPlus => TokenKind::Plus,
            _ => unreachable!("not compound token"),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            TokenKind::BangEqual
            | TokenKind::EqualEqual
            | TokenKind::GreaterEqual
            | TokenKind::LessEqual
            | TokenKind::Arrow
            | TokenKind::PlusPlus
            | TokenKind::MinusMinus
            | TokenKind::PlusEqual
            | TokenKind::MinusEqual
            | TokenKind::PipeEqual
            | TokenKind::ModEqual
            | TokenKind::AmpEqual
            | TokenKind::XorEqual
            | TokenKind::SlashEqual
            | TokenKind::StarEqual
            | TokenKind::GreaterGreater
            | TokenKind::LessLess
            | TokenKind::Do => 2,
            TokenKind::String(s) => s.len() + 2,
            TokenKind::Ident(s) => s.len(),
            TokenKind::Int
            | TokenKind::For
            | TokenKind::GreaterGreaterEqual
            | TokenKind::LessLessEqual => 3,
            TokenKind::Void
            | TokenKind::Char
            | TokenKind::Else
            | TokenKind::Long
            | TokenKind::Enum
            | TokenKind::Goto => 4,
            TokenKind::While | TokenKind::Union | TokenKind::Break => 5,
            TokenKind::If => 2,
            TokenKind::Return | TokenKind::Struct | TokenKind::Sizeof => 6,
            TokenKind::TypeDef => 7,
            TokenKind::Continue => 8,
            TokenKind::Number(n) => n.to_string().len(),
            _ => 1,
        }
    }
}
impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TokenKind::LeftParen => "')'",
                TokenKind::RightParen => "')'",
                TokenKind::LeftBrace => "'{'",
                TokenKind::RightBrace => "'}'",
                TokenKind::LeftBracket => "'['",
                TokenKind::RightBracket => "']'",
                TokenKind::Comma => "','",
                TokenKind::Dot => "'.'",
                TokenKind::Minus => "'-'",
                TokenKind::MinusEqual => "'-='",
                TokenKind::MinusMinus => "'--'",
                TokenKind::Plus => "'+'",
                TokenKind::PlusEqual => "'+='",
                TokenKind::PlusPlus => "'++'",
                TokenKind::Semicolon => "';'",
                TokenKind::Slash => "'/'",
                TokenKind::SlashEqual => "'/='",
                TokenKind::Star => "'*'",
                TokenKind::StarEqual => "'*='",
                TokenKind::Mod => "'%'",
                TokenKind::ModEqual => "'%='",
                TokenKind::Bang => "'!'",
                TokenKind::BangEqual => "'!='",
                TokenKind::Amp => "'&'",
                TokenKind::AmpEqual => "'&='",
                TokenKind::AmpAmp => "'&&'",
                TokenKind::Pipe => "'|'",
                TokenKind::PipeEqual => "'|='",
                TokenKind::PipePipe => "'||'",
                TokenKind::Xor => "'^'",
                TokenKind::XorEqual => "'^='",
                TokenKind::Char => "'char'",
                TokenKind::CharLit(_) => "'char'",
                TokenKind::Int => "'int'",
                TokenKind::Long => "'long'",
                TokenKind::Struct => "'struct'",
                TokenKind::TypeDef => "'typedef'",
                TokenKind::Union => "'union'",
                TokenKind::Enum => "'enum'",
                TokenKind::Equal => "'='",
                TokenKind::EqualEqual => "'=='",
                TokenKind::Greater => "'>'",
                TokenKind::GreaterEqual => "'>='",
                TokenKind::GreaterGreater => "'>>'",
                TokenKind::GreaterGreaterEqual => "'>>='",
                TokenKind::Less => "'<'",
                TokenKind::LessEqual => "'<='",
                TokenKind::LessLess => "'<<'",
                TokenKind::LessLessEqual => "'<<='",
                TokenKind::Ident(..) => "identifier",
                TokenKind::String(_) => "string",
                TokenKind::Number(_) => "number",
                TokenKind::Else => "'else'",
                TokenKind::For => "'for'",
                TokenKind::If => "'if'",
                TokenKind::Switch => "'switch'",
                TokenKind::Case => "'case'",
                TokenKind::Default => "'default'",
                TokenKind::Return => "'return'",
                TokenKind::While => "'while'",
                TokenKind::Break => "'break'",
                TokenKind::Continue => "'continue'",
                TokenKind::Void => "'void'",
                TokenKind::Tilde => "'~'",
                TokenKind::Arrow => "'->'",
                TokenKind::Question => "'?'",
                TokenKind::Colon => "':'",
                TokenKind::Do => "'do'",
                TokenKind::Sizeof => "'sizeof'",
                TokenKind::Goto => "'goto'",
                TokenKind::Ellipsis => "'...'",
            }
        )
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub line_index: i32,
    pub column: i32,
    pub line_string: String,
    pub filename: PathBuf,
}
impl Token {
    pub fn new(
        token: TokenKind,
        line_index: i32,
        column: i32,
        line_string: String,
        filename: PathBuf,
    ) -> Self {
        Token {
            kind: token,
            line_index,
            column,
            line_string,
            filename,
        }
    }
    pub fn default(kind: TokenKind) -> Self {
        Token {
            kind,
            line_index: -1,
            line_string: "".to_string(),
            filename: PathBuf::new(),
            column: -1,
        }
    }
    pub fn unwrap_string(&self) -> String {
        match &self.kind {
            TokenKind::Ident(s, ..) => s.clone(),
            TokenKind::String(s) => s.clone(),
            _ => panic!("cant unwrap string on {} token", self.kind),
        }
    }
    pub fn unwrap_num(&self) -> i64 {
        match &self.kind {
            TokenKind::Number(n) => *n,
            _ => panic!("cant unwrap number on {} token", self.kind),
        }
    }
    pub fn unwrap_char(&self) -> i8 {
        match &self.kind {
            TokenKind::CharLit(c) => *c,
            _ => panic!("cant unwrap char on {} token", self.kind),
        }
    }
    pub fn is_type(&self) -> bool {
        matches!(
            self.kind,
            TokenKind::Enum
                | TokenKind::Union
                | TokenKind::Struct
                | TokenKind::Void
                | TokenKind::Char
                | TokenKind::Int
                | TokenKind::Long
        )
    }
}
impl PartialEq for Token {
    fn eq(&self, other: &Token) -> bool {
        self.line_index == other.line_index
            && self.column == other.column
            && self.filename == other.filename
            && std::mem::discriminant(&self.kind) == std::mem::discriminant(&other.kind)
    }
}
impl Into<SpecifierKind> for Token {
    fn into(self) -> SpecifierKind {
        match self.kind {
            TokenKind::Int => SpecifierKind::Int,
            TokenKind::Char => SpecifierKind::Char,
            TokenKind::Void => SpecifierKind::Void,
            TokenKind::Long => SpecifierKind::Long,
            _ => unreachable!("token not specifier"),
        }
    }
}
impl Location for Token {
    fn line_index(&self) -> i32 {
        self.line_index
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
