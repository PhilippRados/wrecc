#[macro_use]
extern crate afl;
use std::path::Path;
use wrecc_compiler::*;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            if let Ok(source) = preprocess(Path::new("./some.c"), s) {
                let _ = compile(Path::new("./some.c"), &source, false);
            }
        }
    });
}
