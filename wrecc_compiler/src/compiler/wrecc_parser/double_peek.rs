use crate::compiler::common::error::*;
use std::collections::VecDeque;

pub struct DoublePeek<T>(VecDeque<T>);
impl<T> DoublePeek<T> {
    pub fn new(list: Vec<T>) -> Self {
        DoublePeek(list.into())
    }
    pub fn next(&mut self) -> Option<T> {
        self.0.pop_front()
    }
    pub fn peek(&self) -> Result<&T, Error> {
        self.0.front().ok_or(Error::eof("Expected expression"))
    }
    pub fn double_peek(&self) -> Result<&T, Error> {
        self.0.get(1).ok_or(Error::eof("Expected expression"))
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn to_vec(self) -> Vec<T> {
        self.0.into()
    }
}
