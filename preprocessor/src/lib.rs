mod preprocessor;
mod scanner;

use crate::preprocessor::*;
use compiler::Error;
use scanner::*;

use std::collections::HashMap;
use std::path::Path;

// Preprocesses given input file
pub fn preprocess(filename: &Path, source: &str) -> Result<String, Vec<Error>> {
    let tokens = Scanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens, None)
        .start()
        .map(|(source, _)| source)
}

// Preprocesses given input file if input file nested inside root-file
fn preprocess_included(
    filename: &Path,
    source: &str,
    defines: HashMap<String, Vec<TokenKind>>,
) -> Result<(String, HashMap<String, Vec<TokenKind>>), Vec<Error>> {
    let tokens = Scanner::new(source).scan_token();

    Preprocessor::new(filename, source, tokens, Some(defines)).start()
}
