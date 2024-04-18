//! Handles generating and deleting files which are needed for creating a binary file

use std::fs;
use std::io::prelude::*;
use std::path::{Path, PathBuf};

/// Specifies a file to be generated in the temp-dir of the OS.
/// This file is deleted once it goes out of scope at the end of the program.
pub struct TempFile(PathBuf);
impl TempFile {
    pub fn new(extension: &'static str) -> Self {
        let temp_dir = std::env::temp_dir();
        let filename = format!("wrecc_tmp{}", rand());
        let filename = PathBuf::from(filename).with_extension(extension);

        TempFile(temp_dir.join(filename))
    }
}
impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

pub enum OutFile {
    Temp(TempFile),
    Regular(PathBuf),
}
impl OutFile {
    pub fn get(&self) -> &Path {
        match self {
            OutFile::Temp(f) => &f.0,
            OutFile::Regular(f) => f,
        }
    }
}

/// Generates random numbers for unique temp-file
fn rand() -> String {
    const RANDOM_LEN: u32 = 8;
    if let Ok(mut f) = fs::File::open("/dev/urandom") {
        let mut buf = [0u8; RANDOM_LEN as usize];
        f.read_exact(&mut buf).unwrap();
        buf.into_iter().map(|c| c.to_string()).collect()
    } else {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .subsec_nanos();

        format!("{}", nanos)
    }
}
