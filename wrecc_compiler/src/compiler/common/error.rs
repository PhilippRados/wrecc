//! The errors emitted throughout all of wrecc

use crate::compiler::common::{token::*, types::*};
use crate::compiler::typechecker::mir::decl::StorageClass;
use std::num::IntErrorKind;
use std::path::PathBuf;

/// The high-level error type, which is used by both lib.rs and main.rs
#[derive(Debug)]
pub enum WreccError {
    /// Error produced by [compiler](crate::compiler) (parsing/typechecking etc)
    Comp(Vec<Error>),
    /// Error when doing system operations (linking/assembling etc)
    Sys(String),
    /// Error in passing cli-arguments (passing invalid argument)
    Cli(Vec<String>),
}
impl WreccError {
    pub fn print(self, no_color: bool) {
        match self {
            WreccError::Comp(errors) => {
                for e in &errors {
                    e.print_error(no_color);
                }
                eprintln!(
                    "{} error{} generated.",
                    errors.len(),
                    if errors.len() > 1 { "s" } else { "" }
                );
            }
            WreccError::Cli(errors) => {
                for e in &errors {
                    eprintln!("wrecc: <command-line>: {}", e);
                }
            }
            WreccError::Sys(error) => {
                eprintln!("wrecc: {}", error);
            }
        }
    }
}
impl From<Vec<Error>> for WreccError {
    fn from(compiler_errors: Vec<Error>) -> WreccError {
        WreccError::Comp(compiler_errors)
    }
}

/// All error-types in [wrecc_compiler](crate)
#[derive(Debug, PartialEq, Clone)]
pub enum ErrorKind {
    // scan errors
    UnexpectedChar(char),
    CharLiteralQuotes,
    CharLiteralAscii(char),
    InvalidEscape(char),
    UnterminatedString,
    InvalidNumber(IntErrorKind),
    Eof(&'static str),

    // parsing errors
    NotIntegerConstant(&'static str),
    NegativeArraySize,
    IsEmpty(TokenKind),
    EnumOverflow,
    IncompleteType(QualType),
    IncompleteReturnType(String, QualType),
    IncompleteFuncParam(String, QualType),
    IncompleteArgType(usize, QualType),
    IncompleteAssign(QualType),
    IncompleteTentative(QualType),
    VoidFuncArg,
    IncompleteMemberAccess(QualType),
    TypeAlreadyExists(String, TokenKind),
    EnumForwardDecl,
    EmptyAggregate(TokenKind),
    Redefinition(&'static str, String),
    RedefOtherSymbol(String, String),
    RedefTypeMismatch(String, QualType, QualType),
    NonExistantMember(String, QualType),
    DuplicateMember(String),
    InvalidArrayDesignator(QualType),
    TooLong(&'static str, usize, usize),
    NonAggregateInitializer(QualType, QualType),
    ExpectedExpression(TokenKind),
    NotType(TokenKind),
    UndeclaredType(String),
    InvalidVariadic,
    InvalidRestrict(QualType),

    // folding errors
    DivideByZero,
    NegativeShift,
    InvalidConstCast(QualType, QualType),
    IntegerOverflow(QualType),

    // typechecker errors
    UndeclaredLabel(String),
    NotInteger(&'static str, QualType),
    NotScalar(&'static str, QualType),
    DuplicateCase(i32),
    NotIn(&'static str, &'static str),
    MultipleDefaults,
    IllegalAssign(QualType, QualType),
    NotConstantInit(&'static str),
    InvalidExplicitCast(QualType, QualType),
    NoReturnAllPaths(String),
    InvalidMainReturn(QualType),
    TypeMismatch(QualType, QualType),
    InvalidSymbol(String, &'static str),
    InvalidMemberAccess(QualType),
    InvalidIncrementType(QualType),
    InvalidRvalueIncrement,
    NotAssignable(QualType),
    NotLvalue(&'static str),
    RegisterAddress(String),
    MismatchedArity(QualType, usize, usize),
    MismatchedArgs(usize, QualType, QualType, QualType),
    InvalidLogical(TokenKind, QualType, QualType),
    InvalidBinary(TokenKind, QualType, QualType),
    InvalidComp(TokenKind, QualType, QualType),
    InvalidDerefType(QualType),
    MismatchedFunctionReturn(QualType, QualType),
    InvalidUnary(TokenKind, QualType, &'static str),
    UnnamedFuncParams,
    InvalidStorageClass(StorageClass, &'static str),
    InvalidReturnType(QualType),
    NonAggregateDesignator(QualType),
    DesignatorOverflow(usize, i128),
    InitializerOverflow(QualType),
    ScalarOverflow,
    InvalidArray(QualType),
    InvalidCaller(QualType),
    FunctionMember(String, QualType),
    ArraySizeOverflow,
    EmptyInit,
    InvalidAggrInit(QualType),
    ConstAssign,
    ConstStructAssign(QualType, String),

    // environment errors
    UndeclaredSymbol(String),
    StorageClassMismatch(String, &'static str, &'static str),

    // preprocessor errors
    InvalidDirective(String),
    InvalidHeader(String),
    InvalidMacroName,
    UnterminatedIf(String),
    DuplicateElse,
    MissingIf(String),
    MissingExpression(String),
    ElifAfterElse,
    TrailingTokens(&'static str),
    MaxIncludeDepth(usize),

    Regular(&'static str), // generic error message when message only used once
    Multiple(Vec<Error>),
}

impl ErrorKind {
    /// The error message being emitted by and error
    pub fn message(&self) -> String {
        match self {
            ErrorKind::UnexpectedChar(c) => format!("unexpected character: {:?}", c),
            ErrorKind::Eof(s) => format!("{}, found end of file", s),
            ErrorKind::CharLiteralQuotes => {
                "character literal must contain single character enclosed by single quotes ('')"
                    .to_string()
            }
            ErrorKind::InvalidNumber(kind) => {
                format!(
                    "cannot parse number literal: {}",
                    match kind {
                        IntErrorKind::InvalidDigit => "invalid digit found in string",
                        IntErrorKind::PosOverflow => "number is too large to fit in 64bits",
                        _ => "",
                    }
                )
            }
            ErrorKind::CharLiteralAscii(c) => {
                format!("character literal must be valid ascii value. '{}' is not", c)
            }
            ErrorKind::InvalidEscape(c) => format!("cannot escape character '{}'", c),
            ErrorKind::UnterminatedString => "unterminated string".to_string(),

            ErrorKind::NotIntegerConstant(s) => {
                format!("{} has to be an integer constant expression", s)
            }
            ErrorKind::NegativeArraySize => "array size has to be greater than zero".to_string(),
            ErrorKind::IsEmpty(t) => format!("cannot have empty {}", t),
            ErrorKind::EnumOverflow => {
                "enum constant overflow, value has to be in range of type 'int'".to_string()
            }
            ErrorKind::IncompleteType(t) => format!("'{}' contains incomplete type", t),
            ErrorKind::IncompleteReturnType(name, t) => {
                format!("function '{}' has incomplete return type '{}'", name, t)
            }
            ErrorKind::IncompleteAssign(t) => {
                format!("cannot assign to incomplete type '{}'", t)
            }
            ErrorKind::IncompleteTentative(t) => {
                format!("tentative definition of type '{}' is never completed", t)
            }
            ErrorKind::NotType(token) => format!("expected type-declaration, found {}", token),
            ErrorKind::UndeclaredType(s) => format!("undeclared type '{}'", s),
            ErrorKind::InvalidVariadic => {
                "expected at least one named parameter before variadic arguments".to_string()
            }
            ErrorKind::InvalidRestrict(ty) => {
                format!(
                    "'restrict' can only appear on pointers to object-types, not: '{}'",
                    ty
                )
            }
            ErrorKind::IncompleteMemberAccess(qtype) => {
                format!(
                    "cannot access members of type that contains incomplete type '{}'",
                    qtype
                )
            }
            ErrorKind::IncompleteFuncParam(func_name, qtype) => {
                format!(
                    "function '{}' contains incomplete type '{}' as parameter",
                    func_name, qtype
                )
            }
            ErrorKind::VoidFuncArg => {
                "function argument 'void' must be first and only unnamed argument if specified"
                    .to_string()
            }
            ErrorKind::TypeAlreadyExists(name, token) => {
                format!("type '{}' already exists but not as {}", name, token)
            }
            ErrorKind::EnumForwardDecl => "cannot forward declare enums".to_string(),
            ErrorKind::EmptyAggregate(token) => {
                format!("cannot declare unnamed {} without members", token)
            }
            ErrorKind::Redefinition(kind, name) => format!("redefinition of {} '{}'", kind, name),
            ErrorKind::RedefOtherSymbol(name, kind) => format!(
                "redefinition of '{}' as different symbol. Already exists as '{}'",
                name, kind
            ),
            ErrorKind::RedefTypeMismatch(name, new, old) => {
                format!("conflicting types for '{}': '{}' vs '{}'", name, new, old)
            }
            ErrorKind::NonExistantMember(member, qtype) => {
                format!("no member '{}' in '{}'", member, qtype)
            }
            ErrorKind::InvalidArrayDesignator(qtype) => {
                format!("can only use array designator on type 'array' not '{}'", qtype)
            }
            ErrorKind::DesignatorOverflow(expected, actual) => {
                format!(
                    "array designator index '{}' exceeds type-size: '{}'",
                    actual, expected
                )
            }
            ErrorKind::InitializerOverflow(qtype) => {
                format!("initializer overflow, excess elements in '{}'", qtype)
            }
            ErrorKind::ScalarOverflow => "excess elements in scalar initializer".to_string(),
            ErrorKind::ArraySizeOverflow => {
                "array-size exceeds maximum size of 9223372036854775807".to_string()
            }
            ErrorKind::EmptyInit => "cannot have empty aggregate-initializer".to_string(),
            ErrorKind::InvalidAggrInit(qtype) => {
                format!("cannot initialize '{}' with scalar", qtype)
            }
            ErrorKind::ConstAssign => "cannot assign variable which was declared 'const'".to_string(),
            ErrorKind::ConstStructAssign(ty, member) => {
                format!(
                    "cannot assign to '{}' that contains member '{}' declared 'const'",
                    ty, member
                )
            }
            ErrorKind::InvalidArray(qtype) => format!("invalid array-type: '{}'", qtype),
            ErrorKind::InvalidCaller(qtype) => format!(
                "called object type: '{}' is not function or function pointer",
                qtype
            ),
            ErrorKind::FunctionMember(member_name, member_type) => {
                format!(
                    "field '{}' has illegal function-type: '{}'",
                    member_name, member_type
                )
            }

            ErrorKind::NonAggregateDesignator(qtype) => {
                format!(
                    "can only use designator when initializing aggregate types, not '{}'",
                    qtype
                )
            }
            ErrorKind::TooLong(s, expected, actual) => {
                format!("{} is too long, expected: {}, Actual: {}", s, expected, actual)
            }
            ErrorKind::NonAggregateInitializer(expected, actual) => format!(
                "cannot initialize non-aggregate type '{}' with '{}'",
                expected, actual
            ),
            ErrorKind::ExpectedExpression(token) => format!("expected expression, found: {}", token),
            ErrorKind::DuplicateMember(name) => format!("duplicate member '{}'", name),

            ErrorKind::DivideByZero => "cannot divide by zero".to_string(),
            ErrorKind::InvalidConstCast(old_type, new_type) => {
                format!("invalid constant-cast from '{}' to '{}'", old_type, new_type)
            }
            ErrorKind::NegativeShift => "shift amount has to positive".to_string(),
            ErrorKind::IntegerOverflow(qtype) => {
                format!("integer overflow with type: '{}'", qtype)
            }

            ErrorKind::UndeclaredLabel(label) => {
                format!("undeclared label '{}'", label)
            }
            ErrorKind::NotInteger(s, qtype) => {
                format!("{} must be integer type, found '{}'", s, qtype)
            }
            ErrorKind::NotScalar(s, qtype) => {
                format!("{} must be scalar type, found '{}'", s, qtype)
            }
            ErrorKind::DuplicateCase(n) => format!("duplicate 'case'-statement with value {}", n),
            ErrorKind::NotIn(inner, outer) => {
                format!("'{}'-statements have to be inside a '{}'-statement", inner, outer)
            }
            ErrorKind::MultipleDefaults => {
                "cannot have multiple 'default'-statements inside a 'switch'-statement".to_string()
            }
            ErrorKind::IllegalAssign(left, right) => {
                format!("cannot assign to type '{}' with type '{}'", left, right)
            }
            ErrorKind::NotConstantInit(s) => {
                format!("{} can only be initialized to compile-time constants", s)
            }
            ErrorKind::InvalidExplicitCast(old_type, new_type) => {
                format!(
                    "invalid cast from '{}' to '{}', '{}' is not a scalar type",
                    old_type,
                    new_type,
                    if !old_type.ty.is_scalar() {
                        old_type
                    } else {
                        new_type
                    }
                )
            }
            ErrorKind::NoReturnAllPaths(name) => {
                format!("non-void function '{}' doesn't return in all code paths", name)
            }
            ErrorKind::InvalidMainReturn(qtype) => {
                format!("expected 'main' return type 'int', found: '{}'", qtype)
            }
            ErrorKind::TypeMismatch(left, right) => {
                format!("mismatched operand types: '{}' and '{}'", left, right)
            }
            ErrorKind::InvalidSymbol(name, symbol) => {
                format!("symbol '{}' already exists, but not as {}", name, symbol)
            }
            ErrorKind::InvalidMemberAccess(qtype) => {
                format!("can only access members of structs/unions, not '{}'", qtype)
            }
            ErrorKind::InvalidIncrementType(qtype) => {
                format!("cannot increment value of type '{}'", qtype)
            }
            ErrorKind::InvalidRvalueIncrement => "cannot increment rvalues".to_string(),
            ErrorKind::NotAssignable(qtype) => {
                format!("type '{}' is not assignable", qtype)
            }
            ErrorKind::NotLvalue(s) => format!("lvalue required {}", s),
            ErrorKind::RegisterAddress(var_name) => {
                format!(
                    "cannot take address of variable '{}' with 'register' storage-class",
                    var_name
                )
            }
            ErrorKind::IncompleteArgType(index, qtype) => {
                format!(
                    "{} argument has incomplete type: '{}'",
                    num_to_ord(index + 1),
                    qtype
                )
            }
            ErrorKind::MismatchedArity(qtype, expected, actual) => {
                format!(
                    "function of type '{}' expected {} argument(s) found {}",
                    qtype, expected, actual
                )
            }
            ErrorKind::MismatchedArgs(index, qtype, expected, actual) => {
                format!(
                            "mismatched arguments in function of type '{}': expected {} parameter to be of type '{}', found '{}'",
                            qtype,num_to_ord(index + 1),  expected, actual
                        )
            }
            ErrorKind::InvalidLogical(token, left_type, right_type) => {
                format!(
                    "invalid logical expression: '{}' {} '{}', both types need to be scalar",
                    left_type, token, right_type
                )
            }
            ErrorKind::InvalidComp(token, left_type, right_type) => {
                format!("invalid comparsion: '{}' {} '{}'", left_type, token, right_type)
            }
            ErrorKind::InvalidBinary(token, left_type, right_type) => {
                format!(
                    "invalid binary expression: '{}' {} '{}'",
                    left_type, token, right_type
                )
            }
            ErrorKind::InvalidDerefType(qtype) => {
                format!(
                    "cannot dereference value-type '{}', expected type 'pointer'",
                    qtype,
                )
            }
            ErrorKind::MismatchedFunctionReturn(func_return, body_return) => {
                format!(
                    "mismatched function return type: expected '{}', found: '{}'",
                    func_return, body_return
                )
            }

            ErrorKind::UndeclaredSymbol(name) => {
                format!("undeclared symbol '{}'", name)
            }
            ErrorKind::StorageClassMismatch(name, current, existing) => {
                format!(
                    "{} declaration of '{}' follows {} declaration",
                    current, name, existing
                )
            }
            ErrorKind::InvalidUnary(token, right_type, kind) => {
                format!(
                    "invalid unary-expression {} with type '{}', must be {}-type",
                    token, right_type, kind
                )
            }
            ErrorKind::UnnamedFuncParams => {
                "unnamed parameters are not allowed in function definitions".to_string()
            }
            ErrorKind::InvalidStorageClass(sc, s) => {
                format!("invalid storage-class specifier '{}' in {}", sc.to_string(), s)
            }
            ErrorKind::InvalidReturnType(qtype) => {
                format!("functions cannot return type '{}'", qtype)
            }

            ErrorKind::InvalidHeader(s) => format!("'{}' is not a valid header file", s),
            ErrorKind::InvalidDirective(s) => {
                format!("'#{}' is not a valid preprocessor directive", s)
            }
            ErrorKind::UnterminatedIf(if_kind) => {
                format!("unterminated '#{}'", if_kind)
            }
            ErrorKind::InvalidMacroName => "macro name must be valid identifier".to_string(),
            ErrorKind::DuplicateElse => "can only have single '#else' in '#if'-directive".to_string(),
            ErrorKind::MissingExpression(kind) => {
                format!("'#{}' directive expects expression", kind)
            }
            ErrorKind::MissingIf(kind) => {
                format!("found '#{}' without matching '#if'", kind)
            }
            ErrorKind::ElifAfterElse => "found '#elif' after '#else'".to_string(),
            ErrorKind::TrailingTokens(msg) => format!("found trailing tokens after {}", msg),
            ErrorKind::MaxIncludeDepth(max) => {
                format!("#include is nested too deeply, exceeds maximum-depth of {}", max)
            }

            ErrorKind::Regular(s) => s.to_string(),
            ErrorKind::Multiple(_) => {
                unreachable!("should be turned into vec<error> and print seperate errors")
            }
        }
    }
}

fn num_to_ord(n: usize) -> String {
    match n {
        1 => "1st".to_string(),
        2 => "2nd".to_string(),
        3 => "3rd".to_string(),
        _ => n.to_string() + "th",
    }
}

/// Main error used throughout [wrecc_compiler](crate)
#[derive(Debug, PartialEq, Clone)]
pub struct Error {
    pub line_index: i32,
    pub line_string: String,
    pub column: i32,
    pub filename: PathBuf,
    pub kind: ErrorKind,
}
impl Error {
    pub fn new(object: &impl Location, kind: ErrorKind) -> Self {
        Error {
            line_index: object.line_index(),
            line_string: object.line_string(),
            column: object.column(),
            filename: object.filename(),
            kind,
        }
    }

    /// Recursive helper-function chaining all found errors into single vector
    pub fn flatten_multiple(self) -> Vec<Error> {
        match self.kind {
            ErrorKind::Multiple(errors) => {
                let mut flatten = vec![];
                for e in errors {
                    flatten.append(&mut e.flatten_multiple())
                }
                flatten
            }
            _ => vec![self],
        }
    }

    pub fn new_multiple(errors: Vec<Error>) -> Self {
        Error {
            line_index: -1,
            line_string: String::from(""),
            filename: PathBuf::new(),
            column: -1,
            kind: ErrorKind::Multiple(errors),
        }
    }
    /// HACK: should never be used because in theory there is always an eof-token
    pub fn eof(expected: &'static str) -> Self {
        Error {
            line_index: -1,
            line_string: String::from(""),
            filename: PathBuf::from("current file"),
            column: -1,
            kind: ErrorKind::Eof(expected),
        }
    }
    /// Prints the error to `stderr` using all of its location information.<br>
    /// If `no_color` is specified then only prints without any highlighting and color codes.
    pub fn print_error(&self, no_color: bool) {
        let included = if let Some(Some("h")) = self.filename.extension().map(|s| s.to_str()) {
            "included file "
        } else {
            ""
        };
        eprintln!(
            "{}: {}",
            color_text("error", Color::Red, true, no_color),
            color_text(&self.kind.message(), Color::White, true, no_color),
        );

        if self.line_index != -1 {
            eprintln!(
                "{}  {} in {}{}:{}:{}",
                color_text("|", Color::Blue, false, no_color),
                color_text("-->", Color::Blue, false, no_color),
                included,
                color_text(
                    &self.filename.display().to_string(),
                    Color::White,
                    false,
                    no_color
                ),
                self.line_index,
                self.column,
            );

            let line_length = self.line_index.to_string().len();

            eprintln!("{}", color_text("|", Color::Blue, false, no_color));
            eprintln!(
                "{} {}",
                color_text(&self.line_index.to_string(), Color::Blue, true, no_color),
                self.line_string
            );
            eprint!("{}", color_text("|", Color::Blue, false, no_color));
            for _ in 1..self.column as usize + line_length {
                eprint!(" ");
            }
            eprintln!("{}", color_text("^", Color::Red, true, no_color));
        }
    }
}
/// Trait which can be implemented by different error-tokens which are all locatable
pub trait Location {
    fn line_index(&self) -> i32;
    fn column(&self) -> i32;
    fn line_string(&self) -> String;
    fn filename(&self) -> PathBuf;
}
enum Color {
    Red,
    Blue,
    White,
}
impl Color {
    fn code(&self) -> usize {
        match self {
            Color::Red => 31,
            Color::Blue => 34,
            Color::White => 37,
        }
    }
}
fn color_text(text: &str, color: Color, bold: bool, no_color: bool) -> String {
    if no_color {
        text.to_string()
    } else {
        format!(
            "\x1b[{};{}m{}\x1b[0m",
            color.code(),
            if bold { "1" } else { "" },
            text
        )
    }
}
