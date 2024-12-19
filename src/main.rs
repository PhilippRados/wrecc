//! Wrecc is made up of two crates: this binary-crate (wrecc)
//! and the compiler implementation library-crate [wrecc_compiler](wrecc_compiler).
//! This crate uses all the methods exposed by the lib-crate to build the resulting
//! binary from the generated assembly. It assembles and links the assembly by manually
//! invoking the `as` and `ld` commands.
//! This crate also includes the modules [cli_options](crate::cli_options) which parses the
//! cli-args and [temp_file](crate::temp_file) which generates the temp-files passed to the invoked
//! commands.

mod cli_options;
mod temp_file;

use cli_options::*;
use temp_file::*;
use wrecc_compiler::compiler::common::error::WreccError;
use wrecc_compiler::preprocessor::PPToken;
use wrecc_compiler::*;

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Helper macro to embed headers into binary
macro_rules! include_header {
    ($filename:expr) => {
        (
            PathBuf::from($filename),
            include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/include/", $filename)),
        )
    };
}

/// Includes all headers found in [include](https://github.com/PhilippRados/wrecc/tree/master/include)
fn init_standard_headers() -> HashMap<PathBuf, &'static str> {
    HashMap::from([
        include_header!("ctype.h"),
        include_header!("errno.h"),
        include_header!("fcntl.h"),
        include_header!("limits.h"),
        include_header!("stddef.h"),
        include_header!("stdio.h"),
        include_header!("stdlib.h"),
        include_header!("string.h"),
        include_header!("time.h"),
        include_header!("unistd.h"),
        include_header!("setjmp.h"),
        include_header!("signal.h"),
        include_header!("locale.h"),
        include_header!("iso646.h"),
        include_header!("stdint.h"),
        include_header!("inttypes.h"),
    ])
}

/// Reads in string from file passed from user
fn read_input_file(file: &Path) -> Result<String, WreccError> {
    fs::read_to_string(file)
        .map_err(|_| WreccError::Sys(format!("could not find file: '{}'", file.display())))
}

/// Writes the produced x86-64 assembly into a file
fn generate_asm_file(options: &CliOptions, file: &Path, output: String) -> Result<OutFile, WreccError> {
    let output_path = output_path(file, &options.output_path, options.compile_only, "s");

    let mut output_file = std::fs::File::create(output_path.get()).map_err(|_| {
        WreccError::Sys(format!("could not create file '{}'", output_path.get().display()))
    })?;

    if writeln!(output_file, "{}", output).is_err() {
        Err(WreccError::Sys(format!(
            "could not write to file '{}'",
            output_path.get().display()
        )))
    } else {
        Ok(output_path)
    }
}

/// Selects [OutFile] based on cli-args passed and which stage of execution is currently executed
fn output_path(
    file: &Path,
    output_path: &Option<PathBuf>,
    is_last_phase: bool,
    extension: &'static str,
) -> OutFile {
    match (output_path, is_last_phase) {
        (Some(file), true) => OutFile::Regular(file.clone()),
        (None, true) => OutFile::Regular(file.with_extension(extension)),
        (_, false) => OutFile::Temp(TempFile::new(extension)),
    }
}

/// Invokes assembler `as` and stores its output in a file
fn assemble(options: &CliOptions, file: &Path, asm_file: OutFile) -> Result<OutFile, WreccError> {
    let output_path = output_path(file, &options.output_path, options.no_link, "o");

    let mut cmd = Command::new("as");
    cmd.arg(asm_file.get()).arg("-o").arg(output_path.get());

    // Specify target architecture for macos
    // so that apple silicon chips can run x86-64 binary through rosetta
    if std::env::consts::OS == "macos" {
        cmd.arg("-arch").arg("x86_64");
    }

    let output = cmd
        .output()
        .map_err(|_| WreccError::Sys("could not invoke assembler 'as'".to_string()))?;

    if output.status.success() {
        Ok(output_path)
    } else {
        Err(WreccError::Sys(format!(
            "as: {}",
            String::from_utf8(output.stderr).unwrap()
        )))
    }
}

/// Invokes linker `ld` and stores its output in the specified filename.
/// Linker is invoked with some default library-search paths for mac and linux to link with
/// libc.<br>
/// Options `-l` and `-L` are also passed to the linker.<br>
/// If the default search path doesn't include libc on your system you can pass it using `-L`
/// and linking libc should work.
fn link(options: CliOptions, files: Vec<OutFile>) -> Result<(), WreccError> {
    let mut cmd = Command::new("ld");
    match std::env::consts::OS {
        "macos" => {
            cmd.arg("-dynamic")
                .arg("-lSystem")
                .arg("-L/usr/lib")
                .arg("-L/usr/local/lib")
                .arg("-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib")
                .arg("-L/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/lib/");

            for filename in &files {
                cmd.arg(filename.get());
            }
            for path in options.lib_paths {
                cmd.arg(format!("-L{}", path.display()));
            }
        }
        "linux" => {
            let mut lib_paths = [
                "/usr/lib/x86_64-linux-gnu",
                "/usr/lib64",
                "/lib64",
                "/usr/lib/x86_64-pc-linux-gnu",
                "/usr/lib/x86_64-redhat-linux",
                "/usr/lib",
                "/lib",
            ]
            .into_iter()
            .map(PathBuf::from)
            .chain(options.lib_paths);

            let lib_path = lib_paths
                .find(|path| path.join("crti.o").exists())
                .ok_or_else(|| WreccError::Sys(String::from("library path not found")))?;

            cmd.arg("-m")
                .arg("elf_x86_64")
                .arg("-dynamic-linker")
                .arg("/lib64/ld-linux-x86-64.so.2")
                .arg(format!("{}/crt1.o", lib_path.display()))
                .arg(format!("{}/crti.o", lib_path.display()));

            // not sure if libc is always in lib_path so I just pass all lib_paths for now
            for path in lib_paths {
                cmd.arg(format!("-L{}", path.display()));
            }
            for filename in &files {
                cmd.arg(filename.get());
            }

            cmd.arg("-lc").arg(format!("{}/crtn.o", lib_path.display()));
        }
        _ => return Err(WreccError::Sys(String::from("only supports linux and macos"))),
    }

    for name in options.shared_libs {
        cmd.arg(format!("-l{}", name));
    }

    if let Some(output_name) = options.output_path {
        cmd.arg("-o");
        cmd.arg(output_name);
    }

    let output = cmd
        .output()
        .map_err(|_| WreccError::Sys("could not invoke linker 'ld'".to_string()))?;

    if output.status.success() {
        Ok(())
    } else {
        Err(WreccError::Sys(String::from_utf8(output.stderr).unwrap()))
    }
}

fn print_pp(pp_source: Vec<PPToken>, options: &CliOptions) -> Result<(), WreccError> {
    let pp_string: String = pp_source.iter().map(|s| s.kind.to_string()).collect();

    if let Some(pp_file) = &options.output_path {
        let mut output_file = std::fs::File::create(pp_file)
            .map_err(|_| WreccError::Sys(format!("could not create file '{}'", pp_file.display())))?;

        if writeln!(output_file, "{}", pp_string).is_err() {
            Err(WreccError::Sys(format!(
                "could not write to file '{}'",
                pp_file.display()
            )))
        } else {
            Ok(())
        }
    } else {
        eprintln!("{}", pp_string);
        Ok(())
    }
}

/// Actually runs the [preprocessor] and the [compiler] to create an object file
fn process_file(
    options: &CliOptions,
    file: &Path,
    standard_headers: &HashMap<PathBuf, &'static str>,
) -> Result<Option<OutFile>, WreccError> {
    let source = read_input_file(&file)?;

    let pp_source = preprocess(
        &file,
        &options.user_include_dirs,
        &options.defines,
        standard_headers,
        source,
    )?;

    if options.preprocess_only {
        print_pp(pp_source, &options)?;
        return Ok(None);
    }

    let asm_source = compile(pp_source, options.dump_ast)?;

    let asm_file = generate_asm_file(&options, file, asm_source)?;

    if options.compile_only {
        return Ok(None);
    }

    let object_file = assemble(&options, file, asm_file)?;

    Ok(Some(object_file))
}

/// Iterates over all input files and links the resulting object files into a single binary
fn run(options: CliOptions) -> Result<(), Vec<WreccError>> {
    let mut object_files = Vec::new();
    let mut errors = Vec::new();
    let mut early_exit = false;
    let standard_headers = init_standard_headers();

    for file in options.files.iter() {
        match process_file(&options, file, &standard_headers) {
            Ok(Some(obj)) => object_files.push(obj),
            Ok(None) => early_exit = true,
            Err(e) => errors.push(e),
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    if options.no_link || early_exit {
        return Ok(());
    }

    link(options, object_files).map_err(|e| vec![e])?;

    Ok(())
}

/// Seperate main to clean up all destructors
fn real_main() -> Result<(), ()> {
    let options = CliOptions::parse().map_err(|e| e.print(false))?;
    let no_color = options.no_color;

    run(options).map_err(|errs| errs.into_iter().map(|e| e.print(no_color)).collect())
}

/// Main entrypoint only calls [real_main] and returns correct exit-code according to result
fn main() {
    match real_main() {
        Ok(_) => (),
        Err(_) => std::process::exit(1),
    }
}
