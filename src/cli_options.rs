use crate::Error;
use std::path::PathBuf;

// TODO: add license information
const VERSION: &str = concat!(
    env!("CARGO_PKG_NAME"),
    " ",
    env!("CARGO_PKG_VERSION"),
    "\nPhilipp Rados\n",
    "https://github.com/PhilippRados/wrecc"
);

const USAGE: &str = "\
usage: wrecc [-o | --output <file>] [-E | --preprocess-only]
        [-S | --compile-only] [-c | --no-link] [--dump-ast]
        [--no-color] [-h | --help] [-v | --version] <file>";

const HELP: &str = "usage: wrecc [options] <file>
options:
    -o | --output <file>    Specifies the output-file to write to
    -E | --preprocess-only  Stops evaluation after preprocessing printing the preprocessed source
    -S | --compile-only     Stops evaluation after compiling resulting in a .s file
    -c | --no-link          Stops evaluation after assembling resulting in a .o file
         --dump-ast         Displays the AST produced by the parser while also compiling program as usual
         --no-color         Errors are printed without color
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

    // displays AST while also compiling program as usual
    pub dump_ast: bool,

    // errors are printed without color
    pub no_color: bool,
}
impl CliOptions {
    fn default() -> CliOptions {
        CliOptions {
            file_path: PathBuf::new(),
            output_path: None,
            preprocess_only: false,
            compile_only: false,
            no_link: false,
            dump_ast: false,
            no_color: false,
        }
    }
    pub fn parse() -> Result<CliOptions, Error> {
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
                            return Err(Error::Sys(format!(
                                "Expects file following '{}' option",
                                arg
                            )));
                        }
                    }
                    "-E" | "--preprocess-only" => cli_options.preprocess_only = true,
                    "-S" | "--compile-only" => cli_options.compile_only = true,
                    "-c" | "--no-link" => cli_options.no_link = true,
                    "--dump-ast" => cli_options.dump_ast = true,
                    "--no-color" => cli_options.no_color = true,
                    "-h" => sys_info(USAGE),
                    "--help" => sys_info(HELP),
                    "-v" | "--version" => sys_info(VERSION),
                    _ => return Err(Error::Sys(format!("Illegal option '{}'", arg))),
                }
            } else {
                cli_options.file_path = PathBuf::from(arg);
            }
        }

        if cli_options.file_path.to_string_lossy().is_empty() {
            Err(Error::Sys("No input files given".to_string()))
        } else if let Some(Some("c")) = cli_options.file_path.extension().map(|s| s.to_str()) {
            Ok(cli_options)
        } else {
            Err(Error::Sys(format!(
                "File '{}' is not a valid C source file",
                cli_options.file_path.display()
            )))
        }
    }
}
