pub mod compiler;
pub mod preprocessor;

use compiler::{
    codegen::register_allocation::*, codegen::*, common::error::*, parser::*, scanner::*, typechecker::*,
};
use preprocessor::{scanner::Scanner as PPScanner, *};

use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;

// Preprocesses given input file
pub fn preprocess(
    filename: &Path,
    user_include_dirs: &Vec<PathBuf>,
    defines: &Vec<(String, String)>,
    source: String,
) -> Result<Vec<PPToken>, Vec<Error>> {
    let tokens = PPScanner::new(source).scan_token();
    let include_depth = 0;

    let mut system_header_paths = Vec::new();

    // INFO: these env-vars are only checked once at compile-time

    // if installed then add include path set during installation
    if let Some(include_dir_path) = option_env!("WRECC_INCLUDE_DIR") {
        system_header_paths.push(PathBuf::from(include_dir_path));
    }

    // if building from source (or for development) then look in ROOT_CRATE_DIR/include
    if let Some(cargo_manifest_dir) = option_env!("CARGO_MANIFEST_DIR") {
        let cargo_manifest_dir = PathBuf::from(cargo_manifest_dir);
        let root_crate_path = cargo_manifest_dir
            .parent()
            .expect("library-crate inside root-crate");
        system_header_paths.push(root_crate_path.join("include"));
    }

    let mut header_search_paths = Vec::new();
    header_search_paths.extend(user_include_dirs.clone());
    header_search_paths.extend(system_header_paths);

    // TODO: should return Error::Sys instead
    if header_search_paths.is_empty() {
        return Err(vec![Error {
            kind: ErrorKind::Regular(
                "Cannot find system-headers. Either pass with -I or set the WRECC_INCLUDE_DIR env-var",
            ),
            line_index: -1,
            line_string: String::from(""),
            filename: PathBuf::new(),
            column: -1,
        }]);
    }

    // INFO: convert all cli-passed defines to #defines as if they were in regular source file
    // to properly error check them
    let mut dummy_defines = String::new();
    for (macro_name, value) in defines {
        dummy_defines.push_str(&format!("#define {} {}\n", macro_name, value));
    }
    let (_, defines) = Preprocessor::new(
        &PathBuf::from("command-line-argument"),
        PPScanner::new(dummy_defines).scan_token(),
        HashMap::new(),
        header_search_paths.clone(),
        include_depth,
    )
    .start()?;

    Preprocessor::new(filename, tokens, defines, header_search_paths, include_depth)
        .start()
        .map(|(tokens, _)| tokens)
}

pub fn compile(source: Vec<PPToken>, dump_ast: bool) -> Result<String, Vec<Error>> {
    // scan input
    let tokens = Scanner::new(source).scan_token()?;

    // parse tokens and return parse-tree
    let parse_tree = Parser::new(tokens).parse()?;

    if dump_ast {
        parse_tree.iter().for_each(|decl| eprintln!("{}", decl));
    }

    // check for semantic errors and annotate parse-tree returning new ast
    let (mir, const_labels) = TypeChecker::new().check(parse_tree)?;

    // turn AST into LIR
    let (lir, live_intervals) = Compiler::new(const_labels).translate(mir);

    // fill in physical registers
    let asm = RegisterAllocation::new(live_intervals).generate(lir);

    let output = asm
        .into_iter()
        .map(|instr| instr.to_string())
        .collect::<Vec<String>>()
        .join("\n");

    Ok(output)
}
