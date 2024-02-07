use crate::compiler::common::{error::*, token::Token};
use std::collections::VecDeque;

pub struct DoublePeek<T> {
    pub inner: VecDeque<T>,
    pub eof: Option<T>,
}
impl<T: Clone> DoublePeek<T> {
    pub fn new(list: Vec<T>) -> Self {
        DoublePeek {
            eof: list.last().cloned(),
            inner: list.into(),
        }
    }
    pub fn next(&mut self) -> Option<T> {
        self.inner.pop_front()
    }
}
impl DoublePeek<Token> {
    pub fn first_token_after(&self, current: &Token) -> Option<&Token> {
        self.inner.iter().find(|token| token.kind != current.kind)
    }
    pub fn peek(&self, expected: &'static str) -> Result<&Token, Error> {
        self.inner.front().ok_or_else(|| {
            if let Some(eof_token) = &self.eof {
                Error::new(eof_token, ErrorKind::Eof(expected))
            } else {
                // QUESTION: is this ever reached?
                Error::eof(expected)
            }
        })
    }
    pub fn double_peek(&self, expected: &'static str) -> Result<&Token, Error> {
        self.inner.get(1).ok_or_else(|| {
            if let Some(eof_token) = &self.eof {
                Error::new(eof_token, ErrorKind::Eof(expected))
            } else {
                Error::eof(expected)
            }
        })
    }
}
