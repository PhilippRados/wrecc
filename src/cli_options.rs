use compiler::Error;
use std::path::PathBuf;

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
    -S | --compile-only     Stops evaluation after compiling resulting in a .s file
    -c | --no-link          Stops evaluation after assembling resulting in a .o file
    -h                      Prints usage information
    --help                  Prints elaborate help information
    -v | --version          Prints version information

file:
    The C source file to be read";

fn sys_info(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(0);
}

pub struct CliOptions {
    // required argument specifying file to compile
    pub file_path: PathBuf,

    // optional argument specifying output-file to write to
    pub output_path: Option<PathBuf>,

    // stops evaluation after preprocessing printing the preprocessed source
    pub preprocess_only: bool,

    // stops evaluation after compiling resulting in a .s file
    pub compile_only: bool,

    // stops evaluation after assembling resulting in an .o file
    pub no_link: bool,
}
impl CliOptions {
    fn default() -> CliOptions {
        CliOptions {
            file_path: PathBuf::new(),
            output_path: None,
            preprocess_only: false,
            compile_only: false,
            no_link: false,
        }
    }
    pub fn parse() -> CliOptions {
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
                            Error::sys_exit(&format!("Expects file following '{}' option", arg), 1)
                        }
                    }
                    "-E" | "--preprocess-only" => cli_options.preprocess_only = true,
                    "-S" | "--compile-only" => cli_options.compile_only = true,
                    "-c" | "--no-link" => cli_options.no_link = true,
                    "-h" => sys_info(USAGE),
                    "--help" => sys_info(HELP),
                    "-v" | "--version" => sys_info(VERSION),
                    _ => Error::sys_exit(&format!("Illegal option '{}'", arg), 1),
                }
            } else {
                cli_options.file_path = PathBuf::from(arg);
            }
        }

        if cli_options.file_path.to_string_lossy().is_empty() {
            Error::sys_exit("No input files given", 1);
        } else if let Some(Some("c")) = cli_options.file_path.extension().map(|s| s.to_str()) {
            cli_options
        } else {
            Error::sys_exit(
                &format!(
                    "File '{}' is not a valid C source file",
                    cli_options.file_path.display()
                ),
                1,
            );
        }
    }
}
