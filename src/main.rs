use compiler::*;
use preprocessor::*;

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

// TODO: add license information
const VERSION: &'static str = concat!(
    env!("CARGO_PKG_NAME"),
    " ",
    env!("CARGO_PKG_VERSION"),
    "\nPhilipp Rados\n",
    "https://github.com/PhilippRados/wrecc"
);

const USAGE: &'static str = "\
usage: wrecc [-o | --output <file>] [-E | --preprocess-only]
        [-S | --compile-only] [-h | --help] [-v | --version] <file>";

const HELP: &'static str = "usage: wrecc [options] <file>
options:
    -o | --output <file>    Specifies the output-file to write to
    -E | --preprocess-only  Stops evaluation after preprocessing printing the preprocessed source
    -S | --compile-only     Stops evaluation after compiling printing the generated assembly
    -h                      Prints usage information
    --help                  Prints elaborate help information
    -v | --version          Prints version information

file:
    The C source file to be read";

fn sys_info(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(0);
}

struct CliOptions {
    // required argument specifying file to compile
    file_path: PathBuf,

    // optional argument specifying output-file to write to
    output_path: Option<PathBuf>,

    // stops evaluation after preprocessing printing the preprocessed source
    preprocess_only: bool,

    // stops evaluation after compiling printing the resulting asm
    compile_only: bool,
}
impl CliOptions {
    fn default() -> CliOptions {
        CliOptions {
            file_path: PathBuf::new(),
            output_path: None,
            preprocess_only: false,
            compile_only: false,
        }
    }
    fn parse() -> CliOptions {
        let mut cli_options = CliOptions::default();
        let mut args = std::env::args()
            .collect::<Vec<String>>()
            .into_iter()
            .skip(1);

        while let Some(arg) = args.next() {
            if arg.starts_with('-') {
                match arg.as_str() {
                    "-o" | "--output" => {
                        if let Some(file) = args.next() {
                            cli_options.output_path = Some(PathBuf::from(file));
                        } else {
                            Error::sys_exit(&format!("Expects file following '{}' option", arg), 2)
                        }
                    }
                    "-E" | "--preprocess-only" => cli_options.preprocess_only = true,
                    "-S" | "--compile-only" => cli_options.compile_only = true,
                    "-h" => sys_info(USAGE),
                    "--help" => sys_info(HELP),
                    "-v" | "--version" => sys_info(VERSION),
                    _ => Error::sys_exit(&format!("Illegal option '{}'", arg), 2),
                }
            } else {
                cli_options.file_path = PathBuf::from(arg);
            }
        }

        if cli_options.file_path.to_string_lossy().is_empty() {
            Error::sys_exit("No input files given", 2);
        } else if let Some(Some("c")) = cli_options.file_path.extension().map(|s| s.to_str()) {
            cli_options
        } else {
            Error::sys_exit(
                &format!(
                    "File '{}' is not a valid C source file",
                    cli_options.file_path.display()
                ),
                2,
            );
        }
    }
}

// Reads in string from file passed from user
fn read_input_file(file: &Path) -> String {
    if let Ok(source) = fs::read_to_string(&file) {
        source
    } else {
        Error::sys_exit(&format!("Couldn't find file: '{}'", file.display()), 2)
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
            2,
        )
    });

    writeln!(output_file, "{}", output).expect("write failed");
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
