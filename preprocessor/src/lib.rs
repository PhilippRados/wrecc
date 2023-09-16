mod preprocessor;
mod scanner;

use crate::preprocessor::*;
use compiler::Error;
use scanner::*;

use std::collections::HashMap;

// Preprocesses given input file
pub fn preprocess(filename: &str, source: &str) -> Result<String, Vec<Error>> {
    let tokens = Scanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens, None)
        .start()
        .map(|(source, _)| source)
}

// Preprocesses given input file if input file nested inside root-file
fn preprocess_included(
    filename: &str,
    source: &str,
    defines: HashMap<String, Vec<Token>>,
) -> Result<(String, HashMap<String, Vec<Token>>), Vec<Error>> {
    let tokens = Scanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens, Some(defines)).start()
}
