mod cli_options;

use cli_options::*;
use compiler::*;
use preprocessor::*;

use std::fs;
use std::io::Write;
use std::path::Path;

// Reads in string from file passed from user
fn read_input_file(file: &Path) -> String {
    if let Ok(source) = fs::read_to_string(&file) {
        source
    } else {
        Error::sys_exit(&format!("Couldn't find file: '{}'", file.display()), 1)
    }
}

// Generates x8664 assembly output file
fn generate_output_file(cli_options: &CliOptions, output: String) {
    let output_path = if let Some(file) = &cli_options.output_path {
        file.clone()
    } else {
        cli_options.file_path.with_extension("s")
    };

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
}

fn run() -> Result<(), Vec<Error>> {
    let cli_options = CliOptions::parse();

    let original_source = read_input_file(&cli_options.file_path);
    let preprocessed_source = preprocess(&cli_options.file_path, &original_source)?;

    if cli_options.preprocess_only {
        return Ok(eprintln!("{}", &preprocessed_source));
    }

    let output = compile(&cli_options.file_path, &preprocessed_source)?;

    generate_output_file(&cli_options, output);

    if cli_options.compile_only {
        return Ok(());
    }
    // TODO: invoke assembler and linker

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
