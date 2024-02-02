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
    // cannot return Error directly because preprocessor::scanner::Token doesnt implement Location
    pub fn peek(&self, expected: &'static str) -> Result<&T, (Option<T>, ErrorKind)> {
        self.inner
            .front()
            .ok_or_else(|| (self.eof.clone(), ErrorKind::Eof(expected)))
    }
    pub fn double_peek(&self, expected: &'static str) -> Result<&T, (Option<T>, ErrorKind)> {
        self.inner
            .get(1)
            .ok_or_else(|| (self.eof.clone(), ErrorKind::Eof(expected)))
    }
}
