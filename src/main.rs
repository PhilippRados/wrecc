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
use wrecc_compiler::*;

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Reads in string from file passed from user
fn read_input_file(file: &Path) -> Result<String, WreccError> {
    fs::read_to_string(file)
        .map_err(|_| WreccError::Sys(format!("could not find file: '{}'", file.display())))
}

/// Generates x86_64 assembly output file
fn generate_asm_file(options: &CliOptions, output: String) -> Result<OutFile, WreccError> {
    let output_path = output_path(options, options.compile_only, "s");

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
fn output_path(options: &CliOptions, is_last_phase: bool, extension: &'static str) -> OutFile {
    match (&options.output_path, is_last_phase) {
        (Some(file), true) => OutFile::Regular(file.clone()),
        (None, true) => OutFile::Regular(options.file_path.with_extension(extension)),
        (_, false) => OutFile::Temp(TempFile::new(extension)),
    }
}

/// Invokes assembler `as` and stores its output in a file
fn assemble(options: &CliOptions, filename: OutFile) -> Result<OutFile, WreccError> {
    let output_path = output_path(options, options.no_link, "o");

    let output = Command::new("as")
        .arg(filename.get())
        .arg("-o")
        .arg(output_path.get())
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
fn link(options: CliOptions, filename: OutFile) -> Result<(), WreccError> {
    let mut cmd = Command::new("ld");
    match std::env::consts::OS {
        "macos" => {
            cmd.arg("-dynamic")
                .arg("-lSystem")
                .arg("-L/usr/lib")
                .arg("-L/usr/local/lib")
                .arg("-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib")
                .arg("-L/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/lib/")
                .arg(filename.get());

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

            cmd.arg(filename.get())
                .arg("-lc")
                .arg(format!("{}/crtn.o", lib_path.display()));
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

/// Actually runs the [preprocessor] and the [compiler] to create the binary.
fn run(options: CliOptions) -> Result<(), WreccError> {
    let source = read_input_file(&options.file_path)?;
    let pp_source = preprocess(
        &options.file_path,
        &options.user_include_dirs,
        &options.defines,
        source,
    )?;

    if options.preprocess_only {
        return Ok(pp_source.iter().for_each(|s| eprint!("{}", s.kind.to_string())));
    }

    let asm_source = compile(pp_source, options.dump_ast)?;

    let asm_file = generate_asm_file(&options, asm_source)?;

    if options.compile_only {
        return Ok(());
    }

    let object_file = assemble(&options, asm_file)?;

    if options.no_link {
        return Ok(());
    }

    link(options, object_file)?;

    Ok(())
}

/// Seperate main to clean up all destructors
fn real_main() -> Result<(), ()> {
    let options = CliOptions::parse().map_err(|errs| errs.print(false))?;
    let no_color = options.no_color;

    run(options).map_err(|errs| errs.print(no_color))
}

/// Main entrypoint only calls [real_main] and returns correct exit-code according to result
fn main() {
    match real_main() {
        Ok(_) => (),
        Err(_) => std::process::exit(1),
    }
}
