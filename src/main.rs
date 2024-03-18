mod cli_options;

use cli_options::*;
use wrecc_compiler::compiler::common::error::Error as CompilerError;
use wrecc_compiler::*;

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
    Comp(Vec<CompilerError>, bool),
    Sys(String),
}
impl Error {
    fn print(self) {
        match self {
            Error::Comp(errors, no_color) => {
                for e in &errors {
                    e.print_error(no_color);
                }
                eprintln!(
                    "{} error{} generated.",
                    errors.len(),
                    if errors.len() > 1 { "s" } else { "" }
                );
            }
            Error::Sys(e) => {
                eprintln!("wrecc: {}", e);
            }
        }
    }
}
impl From<(Vec<CompilerError>, bool)> for Error {
    fn from((errors, no_color): (Vec<CompilerError>, bool)) -> Self {
        Error::Comp(errors, no_color)
    }
}

// Reads in string from file passed from user
fn read_input_file(file: &Path) -> Result<String, Error> {
    fs::read_to_string(file)
        .map_err(|_| Error::Sys(format!("could not find file: '{}'", file.display())))
}

// Generates x8664 assembly output file
fn generate_asm_file(options: &CliOptions, output: String) -> Result<OutFile, Error> {
    let output_path = output_path(options, options.compile_only, "s");

    let mut output_file = std::fs::File::create(output_path.get())
        .map_err(|_| Error::Sys(format!("could not create file '{}'", output_path.get().display())))?;

    if writeln!(output_file, "{}", output).is_err() {
        Err(Error::Sys(format!(
            "could not write to file '{}'",
            output_path.get().display()
        )))
    } else {
        Ok(output_path)
    }
}

fn output_path(options: &CliOptions, is_last_phase: bool, extension: &'static str) -> OutFile {
    match (&options.output_path, is_last_phase) {
        (Some(file), true) => OutFile::Regular(file.clone()),
        (None, true) => OutFile::Regular(options.file_path.with_extension(extension)),
        (_, false) => OutFile::Temp(TempFile::new(extension)),
    }
}

fn assemble(options: &CliOptions, filename: OutFile) -> Result<OutFile, Error> {
    let output_path = output_path(options, options.no_link, "o");

    let output = Command::new("as")
        .arg(filename.get())
        .arg("-o")
        .arg(output_path.get())
        .output()
        .map_err(|_| Error::Sys("could not invoke assembler 'as'".to_string()))?;

    if output.status.success() {
        Ok(output_path)
    } else {
        Err(Error::Sys(format!(
            "as: {}",
            String::from_utf8(output.stderr).unwrap()
        )))
    }
}
fn find_libpath() -> Result<PathBuf, Error> {
    if Path::new("/usr/lib/x86_64-linux-gnu/crti.o").exists() {
        return Ok(PathBuf::from("/usr/lib/x86_64-linux-gnu/"));
    }
    if Path::new("/usr/lib64/crti.o").exists() {
        return Ok(PathBuf::from("/usr/lib64"));
    }
    Err(Error::Sys(String::from("library path not found")))
}

fn link(filename: OutFile, output_path: &Option<PathBuf>) -> Result<(), Error> {
    let mut cmd = Command::new("ld");
    match std::env::consts::OS {
        "macos" => {
            // WARN: first check where SDK is installed and if not emit error-message
            cmd.arg("-dynamic")
                .arg("-lSystem")
                .arg("-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib")
                .arg(filename.get());
        }
        "linux" => {
            let libpath = find_libpath()?;
            // FIXME: this should be done dynamically
            let gcc_libpath = Path::new("/usr/lib/gcc/x86_64-linux-gnu/9");
            cmd.arg("-m")
                .arg("elf_x86_64")
                .arg("-dynamic-linker")
                .arg("/lib64/ld-linux-x86-64.so.2")
                .arg(format!("{}/crt1.o", libpath.display()))
                .arg(format!("{}/crti.o", libpath.display()))
                .arg(format!("{}/crtbegin.o", gcc_libpath.display()))
                .arg(format!("-L{}", gcc_libpath.display()))
                .arg("-L/usr/lib/x86_64-linux-gnu")
                .arg("-L/usr/lib64")
                .arg("-L/lib64")
                .arg("-L/usr/lib/x86_64-linux-gnu")
                .arg("-L/usr/lib/x86_64-pc-linux-gnu")
                .arg("-L/usr/lib/x86_64-redhat-linux")
                .arg("-L/usr/lib")
                .arg("-L/lib")
                .arg(filename.get())
                .arg("-lc")
                .arg("-lgcc")
                .arg("--as-needed")
                .arg("-lgcc_s")
                .arg(format!("{}/crtend.o", gcc_libpath.display()))
                .arg(format!("{}/crtn.o", libpath.display()));
        }
        _ => return Err(Error::Sys(String::from("only supports linx and macos"))),
    }

    if let Some(output_name) = output_path {
        cmd.arg("-o");
        cmd.arg(output_name);
    }

    let output = cmd
        .output()
        .map_err(|_| Error::Sys("could not invoke linker 'ld'".to_string()))?;

    if output.status.success() {
        Ok(())
    } else {
        Err(Error::Sys(String::from_utf8(output.stderr).unwrap()))
    }
}

fn run() -> Result<(), Error> {
    let options = CliOptions::parse()?;

    let source = read_input_file(&options.file_path)?;
    let pp_source = preprocess(
        &options.file_path,
        &options.user_include_dirs,
        &options.defines,
        source,
    )
    .map_err(|e| (e, options.no_color))?;

    if options.preprocess_only {
        return Ok(pp_source.iter().for_each(|s| eprint!("{}", s.kind.to_string())));
    }

    let asm_source = compile(pp_source, options.dump_ast).map_err(|e| (e, options.no_color))?;

    let asm_file = generate_asm_file(&options, asm_source)?;

    if options.compile_only {
        return Ok(());
    }

    let object_file = assemble(&options, asm_file)?;

    if options.no_link {
        return Ok(());
    }

    link(object_file, &options.output_path)?;

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
