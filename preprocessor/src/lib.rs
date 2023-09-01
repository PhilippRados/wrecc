mod preprocessor;
mod scanner;

use crate::preprocessor::*;
use compiler::Error;
use scanner::*;

use std::collections::HashMap;

pub fn preprocess(
    filename: &str,
    source: &str,
) -> Result<(String, HashMap<String, String>), Vec<Error>> {
    let tokens = Scanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens).start()
}
