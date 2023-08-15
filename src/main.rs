use compiler::*;
use preprocessor::*;

use std::fs;

struct CliOptions {
    // required argument specifying file to compile
    file_path: String,

    // optional argument specifying output-file to write to
    // TODO: parse -o flag
    #[allow(dead_code)]
    output_path: Option<String>,
}

fn process_cmd_arguments() -> CliOptions {
    let args: Vec<String> = std::env::args().collect();

    let file_path = match args.len() {
        2 => args[1].to_string(),
        _ => Error::sys_exit("Usage: rucc <file>", 22),
    };

    CliOptions { file_path, output_path: None }
}

// Reads in string from file passed from user
fn read_input_file(file: &str) -> String {
    let source = fs::read_to_string(&file)
        .unwrap_or_else(|_| Error::sys_exit(&format!("Couldn't find file: '{}'", file), 2));

    source
}

// Generates x8664 assembly output file
fn generate_output_file(output: String) {
    use std::io::Write;
    let mut output_file =
        std::fs::File::create("/Users/philipprados/documents/coding/Rust/rucc/generated.s")
            .expect("create failed");

    writeln!(output_file, "{}", output).expect("write failed");
}

fn run() -> Result<(), Vec<Error>> {
    let cli_options = process_cmd_arguments();

    let original_source = read_input_file(&cli_options.file_path);
    let preprocessed_source =
        Preprocessor::new(&cli_options.file_path, &original_source).preprocess()?;

    // eprintln!("{}", &preprocessed_source);

    let output = compile(&cli_options.file_path, &preprocessed_source)?;

    generate_output_file(output);

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
