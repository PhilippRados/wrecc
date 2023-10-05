mod cli_options;

use cli_options::*;
use compiler::*;
use preprocessor::*;

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

// Reads in string from file passed from user
fn read_input_file(file: &Path) -> String {
    if let Ok(source) = fs::read_to_string(&file) {
        source
    } else {
        Error::sys_exit(&format!("Couldn't find file: '{}'", file.display()), 1)
    }
}

// Generates x8664 assembly output file
fn generate_asm_file(cli_options: &CliOptions, output: String) -> PathBuf {
    let output_path = output_path(cli_options, cli_options.compile_only, "s");

    let mut output_file = std::fs::File::create(&output_path).unwrap_or_else(|_| {
        Error::sys_exit(
            &format!("Couldn't create file '{}'", output_path.display()),
            1,
        )
    });

    if let Err(_) = writeln!(output_file, "{}", output) {
        Error::sys_exit(
            &format!("Couldn't write to file '{}'", output_path.display()),
            1,
        )
    }

    output_path
}

fn output_path(cli_options: &CliOptions, is_last_phase: bool, extension: &'static str) -> PathBuf {
    match (&cli_options.output_path, is_last_phase) {
        (Some(file), true) => file.clone(),
        (None, true) => cli_options.file_path.with_extension(extension),
        (_, false) => {
            // TODO: create proper tempfile
            PathBuf::from("temp")
        }
    }
}

fn assemble(cli_options: &CliOptions, filename: &Path) -> PathBuf {
    let output_path = output_path(cli_options, cli_options.no_link, "o");

    let output = Command::new("as")
        .arg(filename)
        .arg("-o")
        .arg(&output_path)
        .output()
        .unwrap_or_else(|_| Error::sys_exit("Couldn't invoke assembler 'as'", 1));

    if !output.status.success() {
        Error::sys_exit(
            std::str::from_utf8(&output.stderr).unwrap(),
            output.status.code().unwrap(),
        );
    }

    output_path
}

fn link(filename: &Path, output_path: Option<PathBuf>) {
    let mut cmd = Command::new("ld");
    cmd.arg("-dynamic")
        .arg("-lSystem")
        .arg("-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib")
        .arg(filename);

    if let Some(output_name) = output_path {
        cmd.arg("-o");
        cmd.arg(output_name);
    }

    let output = cmd
        .output()
        .unwrap_or_else(|_| Error::sys_exit("Couldn't invoke linker 'ld'", 1));

    if !output.status.success() {
        Error::sys_exit(
            std::str::from_utf8(&output.stderr).unwrap(),
            output.status.code().unwrap(),
        );
    }
}

fn run() -> Result<(), Vec<Error>> {
    let cli_options = CliOptions::parse();

    let original_source = read_input_file(&cli_options.file_path);
    let preprocessed_source = preprocess(&cli_options.file_path, &original_source)?;

    if cli_options.preprocess_only {
        return Ok(eprintln!("{}", &preprocessed_source));
    }

    let asm_output = compile(&cli_options.file_path, &preprocessed_source)?;

    let filename = generate_asm_file(&cli_options, asm_output);

    if cli_options.compile_only {
        return Ok(());
    }

    let filename = assemble(&cli_options, &filename);

    if cli_options.no_link {
        return Ok(());
    }

    link(&filename, cli_options.output_path);

    Ok(())
}

fn main() {
    match run() {
        Ok(()) => (),
        Err(errors) => {
            for e in errors {
                e.print_error();
            }
        }
    }
}
