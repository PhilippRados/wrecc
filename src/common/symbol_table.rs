use std::collections::HashMap;

#[derive(Clone, PartialEq)]
pub struct Table<T, F> {
    pub vars: HashMap<String, T>,
    pub funcs: HashMap<String, F>,
}
impl<T, F> Table<T, F> {
    pub fn new() -> Self {
        Table {
            vars: HashMap::<String, T>::new(),
            funcs: HashMap::<String, F>::new(),
        }
    }
}
