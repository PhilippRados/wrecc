use crate::compiler::common::error::*;
use std::collections::VecDeque;

pub struct DoublePeek<T> {
    inner: VecDeque<T>,
    eof: Option<T>,
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
    pub fn peek(&self) -> Result<&T, (Option<T>, ErrorKind)> {
        self.inner
            .front()
            .ok_or_else(|| (self.eof.clone(), ErrorKind::Eof("Expected expression")))
    }
    pub fn double_peek(&self) -> Result<&T, (Option<T>, ErrorKind)> {
        self.inner
            .get(1)
            .ok_or_else(|| (self.eof.clone(), ErrorKind::Eof("Expected expression")))
    }
}
