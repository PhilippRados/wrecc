use crate::WreccError;
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
usage: wrecc [-o <file>] [-I <dir>] [-D <name>=<value>]
             [-L <dir>] [-l <name>] [-E] [-S] [-c] [--dump-ast]
             [--no-color] [-h | --help] [-v] <file>";

const HELP: &str = "usage: wrecc [options] <file>
options:
    -o | --output <file>                Specifies the output-file to write to
    -I | --include-dir <dir>            Adds <dir> to the directories to be searched for using #include
    -D | --define <macro-name>=<value>  Defines a new object-like macro
    -L | --library-path <dir>           Adds <dir> to the directories to tthe library search paths (passed as -L<dir> to linker)
    -l | --library <name>               Looks for shared libraries with <name> in library search paths (passed as -l<name> to linker)
    -E | --preprocess-only              Stops evaluation after preprocessing printing the preprocessed source
    -S | --compile-only                 Stops evaluation after compiling resulting in a .s file
    -c | --no-link                      Stops evaluation after assembling resulting in a .o file
         --dump-ast                     Displays the AST produced by the parser while also compiling program as usual
         --no-color                     Errors are printed without color
    -h                                  Prints usage information
    --help                              Prints elaborate help information
    -v | --version                      Prints version information

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

    // directories specified by user to be searched after #include "..." and before #include <...>
    pub user_include_dirs: Vec<PathBuf>,

    // all definitions passed as cli-arguments
    // INFO: duplicate definitions are caught in preprocessor
    pub defines: Vec<(String, String)>,

    // adds a path to the directories to be searched during linking (passed as -L<dir> to linker)
    pub lib_paths: Vec<PathBuf>,

    // adds name to the shared libraries going to be linked (passed as -l<name> to linker)
    pub shared_libs: Vec<String>,
}
impl CliOptions {
    fn new() -> CliOptions {
        CliOptions {
            file_path: PathBuf::new(),
            user_include_dirs: Vec::new(),
            defines: Vec::new(),
            lib_paths: Vec::new(),
            shared_libs: Vec::new(),
            output_path: None,
            preprocess_only: false,
            compile_only: false,
            no_link: false,
            dump_ast: false,
            no_color: false,
        }
    }
    pub fn parse() -> Result<CliOptions, WreccError> {
        let mut cli_options = CliOptions::new();
        let mut args = std::env::args().collect::<Vec<String>>().into_iter().skip(1);

        while let Some(arg) = args.next() {
            if arg.starts_with('-') {
                match arg.as_str() {
                    "-o" | "--output" => {
                        if let Some(file) = args.next() {
                            cli_options.output_path = Some(PathBuf::from(file));
                        } else {
                            return Err(WreccError::Cli(vec![format!(
                                "expected file following '{}' option",
                                arg
                            )]));
                        }
                    }
                    "-I" | "--include-dir" => {
                        if let Some(dir) = args.next() {
                            cli_options.user_include_dirs.push(PathBuf::from(dir))
                        } else {
                            return Err(WreccError::Cli(vec![format!(
                                "expected dir following '{}' option",
                                arg
                            )]));
                        }
                    }
                    "-D" | "--define" => {
                        let Some(arg) = args.next() else {
                            return Err(WreccError::Cli(vec![format!(
                                "expected macro-definition following '{}' option",
                                arg
                            )]));
                        };

                        let (macro_name, value) = arg
                            .split_once('=')
                            // if no '=' found then `-D foo`, same as `-D foo=1`
                            .unwrap_or((&arg, "1"));

                        cli_options
                            .defines
                            .push((macro_name.to_string(), value.to_string()));
                    }
                    "-L" | "--library-path" => {
                        if let Some(path) = args.next() {
                            cli_options.lib_paths.push(PathBuf::from(path));
                        } else {
                            return Err(WreccError::Cli(vec![format!(
                                "expected directory path following '{}' option",
                                arg
                            )]));
                        }
                    }
                    "-l" | "--library" => {
                        if let Some(lib_name) = args.next() {
                            cli_options.shared_libs.push(lib_name);
                        } else {
                            return Err(WreccError::Cli(vec![format!(
                                "expected library name following '{}' option",
                                arg
                            )]));
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
                    _ => return Err(WreccError::Cli(vec![format!("illegal option '{}'", arg)])),
                }
            } else {
                cli_options.file_path = PathBuf::from(arg);
            }
        }

        if cli_options.file_path.to_string_lossy().is_empty() {
            Err(WreccError::Cli(vec!["no input files given".to_string()]))
        } else if let Some(Some("c")) = cli_options.file_path.extension().map(|s| s.to_str()) {
            Ok(cli_options)
        } else {
            Err(WreccError::Cli(vec![format!(
                "file '{}' is not a valid C source file",
                cli_options.file_path.display()
            )]))
        }
    }
}
