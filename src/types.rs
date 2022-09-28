use crate::token::TokenKind;

#[derive(Clone, PartialEq)]
pub enum Types {
    Char(i8),
    Int(i32),
    Void,
}
impl Types {
    pub fn into_vec() -> Vec<TokenKind> {
        vec![TokenKind::Char, TokenKind::Int, TokenKind::Void]
    }
    pub fn unwrap_num(&self) -> i32 {
        match self {
            Types::Char(c) => *c as i32,
            Types::Int(n) => *n,
            Types::Void => unreachable!("Type checker should catch this"),
        }
    }
}
