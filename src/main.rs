mod cli_options;

use cli_options::*;
use compiler::compile;
use compiler::Error as CompilerError;
use preprocessor::*;

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

struct TempFile(PathBuf);
impl TempFile {
    fn new(extension: &'static str) -> Self {
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

enum OutFile {
    Temp(TempFile),
    Regular(PathBuf),
}
impl OutFile {
    fn get(&self) -> &Path {
        match self {
            OutFile::Temp(f) => &f.0,
            OutFile::Regular(f) => f,
        }
    }
}
pub enum Error {
    Comp(Vec<CompilerError>),
    Sys(String),
}
impl Error {
    fn print(self) {
        match self {
            Error::Comp(errors) => {
                for e in errors {
                    e.print_error();
                }
            }
            Error::Sys(e) => {
                eprintln!("wrecc: {}", e);
            }
        }
    }
}
impl From<Vec<CompilerError>> for Error {
    fn from(errors: Vec<CompilerError>) -> Self {
        Error::Comp(errors)
    }
}

// Reads in string from file passed from user
fn read_input_file(file: &Path) -> Result<String, Error> {
    fs::read_to_string(file)
        .map_err(|_| Error::Sys(format!("Couldn't find file: '{}'", file.display())))
}

// Generates x8664 assembly output file
fn generate_asm_file(cli_options: &CliOptions, output: String) -> Result<OutFile, Error> {
    let output_path = output_path(cli_options, cli_options.compile_only, "s");

    let mut output_file = std::fs::File::create(output_path.get()).map_err(|_| {
        Error::Sys(format!(
            "Couldn't create file '{}'",
            output_path.get().display()
        ))
    })?;

    if writeln!(output_file, "{}", output).is_err() {
        Err(Error::Sys(format!(
            "Couldn't write to file '{}'",
            output_path.get().display()
        )))
    } else {
        Ok(output_path)
    }
}

fn output_path(cli_options: &CliOptions, is_last_phase: bool, extension: &'static str) -> OutFile {
    match (&cli_options.output_path, is_last_phase) {
        (Some(file), true) => OutFile::Regular(file.clone()),
        (None, true) => OutFile::Regular(cli_options.file_path.with_extension(extension)),
        (_, false) => OutFile::Temp(TempFile::new(extension)),
    }
}

fn assemble(cli_options: &CliOptions, filename: OutFile) -> Result<OutFile, Error> {
    let output_path = output_path(cli_options, cli_options.no_link, "o");

    let output = Command::new("as")
        .arg(filename.get())
        .arg("-o")
        .arg(output_path.get())
        .output()
        .map_err(|_| Error::Sys("Couldn't invoke assembler 'as'".to_string()))?;

    if output.status.success() {
        Ok(output_path)
    } else {
        Err(Error::Sys(String::from_utf8(output.stderr).unwrap()))
    }
}

fn link(filename: OutFile, output_path: Option<PathBuf>) -> Result<(), Error> {
    let mut cmd = Command::new("ld");
    cmd.arg("-dynamic")
        .arg("-lSystem")
        .arg("-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib")
        .arg(filename.get());

    if let Some(output_name) = output_path {
        cmd.arg("-o");
        cmd.arg(output_name);
    }

    let output = cmd
        .output()
        .map_err(|_| Error::Sys("Couldn't invoke linker 'ld'".to_string()))?;

    if output.status.success() {
        Ok(())
    } else {
        Err(Error::Sys(String::from_utf8(output.stderr).unwrap()))
    }
}

fn run() -> Result<(), Error> {
    let cli_options = CliOptions::parse()?;

    let original_source = read_input_file(&cli_options.file_path)?;
    let preprocessed_source = preprocess(&cli_options.file_path, &original_source)?;

    if cli_options.preprocess_only {
        return Ok(eprintln!("{}", &preprocessed_source));
    }

    let asm_output = compile(
        &cli_options.file_path,
        &preprocessed_source,
        cli_options.dump_ast,
    )?;

    let filename = generate_asm_file(&cli_options, asm_output)?;

    if cli_options.compile_only {
        return Ok(());
    }

    let filename = assemble(&cli_options, filename)?;

    if cli_options.no_link {
        return Ok(());
    }

    link(filename, cli_options.output_path)?;

    Ok(())
}

fn main() {
    match run() {
        Ok(()) => (),
        Err(errors) => {
            errors.print();
            std::process::exit(1);
        }
    }
}
