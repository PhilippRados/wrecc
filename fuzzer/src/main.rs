#[macro_use]
extern crate afl;
use compiler::compile;
use preprocessor::preprocess;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            let source = preprocess("", s);
            if let Ok((source, _)) = source {
                let _ = compile("", &source);
            }
        }
    });
}
