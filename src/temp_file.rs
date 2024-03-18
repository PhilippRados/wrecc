use std::fs;
use std::path::{Path, PathBuf};

pub struct TempFile(PathBuf);
impl TempFile {
    pub fn new(extension: &'static str) -> Self {
        let temp_dir = std::env::temp_dir();
        let filename = PathBuf::from("wrecc_temp_file").with_extension(extension);

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
