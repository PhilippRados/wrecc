use crate::token::TokenKind;
use std::fmt::Display;

#[derive(Clone, PartialEq)]
pub enum TypeValues {
    Char(i8),
    Int(i32),
    Void,
}
impl TypeValues {
    pub fn unwrap_as_int(&self) -> i32 {
        match self {
            TypeValues::Char(c) => *c as i32,
            TypeValues::Int(n) => *n,
            TypeValues::Void => unreachable!("Type checker should catch this"),
        }
    }
    pub fn from(token: &Types, value: i32) -> Self {
        match token {
            Types::Int => TypeValues::Int(value),
            Types::Char => TypeValues::Char(value as i8),
            Types::Void => TypeValues::Void,
        }
    }
}
#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub enum Types {
    Void = 0, // type-promotion order
    Char = 1,
    Int = 4,
}
impl From<&TypeValues> for Types {
    fn from(token: &TypeValues) -> Self {
        match token {
            TypeValues::Char(_) => Types::Char,
            TypeValues::Int(_) => Types::Int,
            TypeValues::Void => Types::Void,
        }
    }
}
impl Types {
    pub fn into_vec() -> Vec<TokenKind> {
        vec![TokenKind::Char, TokenKind::Int, TokenKind::Void]
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
