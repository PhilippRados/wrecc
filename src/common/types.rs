use crate::common::token::TokenKind;
use std::fmt::Display;

#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub enum Types {
    Void, // type-promotion order
    Char,
    Int,
}
impl Types {
    pub fn into_vec() -> Vec<TokenKind> {
        vec![TokenKind::Char, TokenKind::Int, TokenKind::Void]
    }
    // returns type-size in bytes
    pub fn size(&self) -> usize {
        match self {
            Types::Void => 0,
            Types::Char => 1,
            Types::Int => 4,
        }
    }
}
impl Display for Types {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Types::Char => "'char'",
                Types::Int => "'int'",
                Types::Void => "'void'",
            }
        )
    }
}
