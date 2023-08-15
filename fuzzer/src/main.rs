#[macro_use]
extern crate afl;
use compiler::compile;
use preprocessor::*;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            let source = Preprocessor::new("", s).preprocess();
            if let Ok(source) = source {
                let _ = compile("", &source);
            }
        }
    });
}
