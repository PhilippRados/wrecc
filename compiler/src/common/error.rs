use crate::common::{token::*, types::*};
use std::num::IntErrorKind;
use std::path::PathBuf;

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
    BracketsNotAllowed,
    NotIntegerConstant(&'static str),
    NegativeArraySize,
    IsEmpty(TokenType),
    EnumOverflow,
    IncompleteType(NEWTypes),
    IncompleteReturnType(String, NEWTypes),
    IncompleteFuncArg(String, NEWTypes),
    VoidFuncArg,
    IncompleteMemberAccess(NEWTypes),
    TypeAlreadyExists(String, TokenType),
    EnumForwardDecl,
    EmptyAggregate(TokenType),
    Redefinition(&'static str, String),
    NonExistantMember(String, NEWTypes),
    DuplicateMember(String),
    InvalidArrayDesignator(NEWTypes),
    TooLong(&'static str, usize, usize),
    NonAggregateInitializer(NEWTypes, NEWTypes),
    InitializerOverflow(usize, usize),
    ExpectedExpression(TokenType),
    NotType(TokenType),
    UndeclaredType(String),
    InvalidVariadic,

    // folding errors
    DivideByZero,
    NegativeShift,
    InvalidConstCast(NEWTypes, NEWTypes),

    // typechecker errors
    MissingLabel(String, String),
    NotInteger(&'static str, NEWTypes),
    NotScalar(&'static str, NEWTypes),
    DuplicateCase(i64),
    NotIn(&'static str, &'static str),
    MultipleDefaults,
    IllegalAssign(NEWTypes, NEWTypes),
    NotConstantInit(&'static str),
    InvalidExplicitCast(NEWTypes, NEWTypes),
    NoReturnAllPaths(String),
    InvalidMainReturn(NEWTypes),
    TypeMismatch(NEWTypes, NEWTypes),
    InvalidSymbol(String, &'static str),
    InvalidMemberAccess(NEWTypes),
    InvalidIncrementType(NEWTypes),
    InvalidRvalueIncrement,
    NotAssignable(NEWTypes),
    NotLvalue,
    MismatchedArity(String, usize, usize),
    MismatchedArgs(usize, String, Option<Token>, NEWTypes, NEWTypes),
    InvalidLogical(TokenType, NEWTypes, NEWTypes),
    InvalidBinary(TokenType, NEWTypes, NEWTypes),
    InvalidComp(TokenType, NEWTypes, NEWTypes),
    InvalidDerefType(NEWTypes),
    InvalidArrayReturn,
    MismatchedFunctionReturn(NEWTypes, NEWTypes),
    InvalidUnary(TokenType, NEWTypes, &'static str),
    UnnamedFuncParams,

    // environment errors
    MismatchedFuncDeclReturn(NEWTypes, NEWTypes),
    MismatchedFuncDeclArity(usize, usize),
    TypeMismatchFuncDecl(usize, NEWTypes, NEWTypes),
    MismatchedVariadic(bool, bool),
    UndeclaredSymbol(String),
    IntegerOverflow(NEWTypes),

    // preprocessor errors
    InvalidDirective(String),
    InvalidHeader(String),
    InvalidMacroName,
    UnterminatedIf(String),
    DuplicateElse,
    MissingIf(String),
    ElifAfterElse,

    Regular(&'static str), // generic error message when message only used once
    Multiple(Vec<Error>),
}

impl ErrorKind {
    fn message(&self) -> String {
        match self {
            ErrorKind::UnexpectedChar(c) => format!("Unexpected character: {:?}", c),
            ErrorKind::Eof(s) => format!("{}, found end of file", s),
            ErrorKind::CharLiteralQuotes => {
                "Character literal must contain single character enclosed by single quotes ('')"
                    .to_string()
            }
            ErrorKind::InvalidNumber(kind) => {
                format!(
                    "Can't parse number literal. {}",
                    match kind {
                        IntErrorKind::InvalidDigit => "Invalid digit found in string",
                        IntErrorKind::PosOverflow => "Number is too large to fit in 64bits",
                        _ => "",
                    }
                )
            }
            ErrorKind::CharLiteralAscii(c) => {
                format!(
                    "Character literal must be valid ascii value. '{}' is not",
                    c
                )
            }
            ErrorKind::InvalidEscape(c) => format!("Can't escape character '{}'", c),
            ErrorKind::UnterminatedString => "Unterminated string".to_string(),

            ErrorKind::BracketsNotAllowed => {
                "Brackets not allowed here; Put them after the Identifier".to_string()
            }
            ErrorKind::NotIntegerConstant(s) => {
                format!("{} has to be an integer constant expression", s)
            }
            ErrorKind::NegativeArraySize => "Array size has to be greater than zero".to_string(),
            ErrorKind::IsEmpty(t) => format!("Can't have empty {}", t),
            ErrorKind::EnumOverflow => {
                "Enum constant overflow. Value has to be in range -2147483648 and 2147483647"
                    .to_string()
            }
            ErrorKind::IncompleteType(t) => format!("'{}' contains incomplete type", t),
            ErrorKind::IncompleteReturnType(name, t) => {
                format!("Function '{}' has incomplete return type '{}'", name, t)
            }
            ErrorKind::NotType(token) => format!("Expected type-declaration, found {}", token),
            ErrorKind::UndeclaredType(s) => format!("Undeclared type '{}'", s),
            ErrorKind::InvalidVariadic => {
                "Expected at least one named parameter before variadic arguments".to_string()
            }
            ErrorKind::IncompleteMemberAccess(type_decl) => {
                format!(
                    "Can't access members of type that contains incomplete type '{}'",
                    type_decl
                )
            }
            ErrorKind::IncompleteFuncArg(func_name, type_decl) => {
                format!(
                    "Function '{}' contains incomplete type '{}' as parameter",
                    func_name, type_decl
                )
            }
            ErrorKind::VoidFuncArg => {
                "Function argument 'void' must be first and only unnamed argument if specified"
                    .to_string()
            }
            ErrorKind::TypeAlreadyExists(name, token) => {
                format!("Type '{}' already exists but not as {}", name, token)
            }
            ErrorKind::EnumForwardDecl => "Can't forward declare enums".to_string(),
            ErrorKind::EmptyAggregate(token) => {
                format!("Can't declare anonymous {} without members", token)
            }
            ErrorKind::Redefinition(kind, name) => format!("Redefinition of {} '{}'", kind, name),
            ErrorKind::NonExistantMember(member, type_decl) => {
                format!("No member '{}' in '{}'", member, type_decl)
            }
            ErrorKind::InvalidArrayDesignator(type_decl) => format!(
                "Can only use array designator on type 'array' not '{}'",
                type_decl
            ),
            ErrorKind::TooLong(s, expected, actual) => format!(
                "{} is too long. Expected: {}, Actual: {}",
                s, expected, actual
            ),
            ErrorKind::NonAggregateInitializer(expected, actual) => format!(
                "Can't initialize non-aggregate type '{}' with '{}'",
                expected, actual
            ),
            ErrorKind::InitializerOverflow(expected, actual) => format!(
                "Initializer overflow. Expected size: {}, Actual size: {}",
                expected, actual
            ),
            ErrorKind::ExpectedExpression(token) => format!("Expected expression found: {}", token),
            ErrorKind::DuplicateMember(name) => format!("Duplicate member '{}'", name),

            ErrorKind::DivideByZero => "Can't divide by zero".to_string(),
            ErrorKind::InvalidConstCast(old_type, new_type) => format!(
                "Invalid constant-cast from '{}' to '{}'",
                old_type, new_type,
            ),
            ErrorKind::NegativeShift => "Shift amount has to positive".to_string(),
            ErrorKind::IntegerOverflow(type_decl) => {
                format!("Integer overflow with type: '{}'", type_decl)
            }

            ErrorKind::MissingLabel(label, func_name) => {
                format!("No label '{}' in function '{}'", label, func_name)
            }
            ErrorKind::NotInteger(s, type_decl) => {
                format!("{} must be integer type, found '{}'", s, type_decl,)
            }
            ErrorKind::NotScalar(s, type_decl) => {
                format!("{} must be scalar type, found '{}'", s, type_decl,)
            }
            ErrorKind::DuplicateCase(n) => format!("Duplicate 'case'-statement with value {}", n),
            ErrorKind::NotIn(inner, outer) => {
                format!(
                    "'{}'-statements have to be inside a '{}'-statement",
                    inner, outer
                )
            }
            ErrorKind::MultipleDefaults => {
                "Can't have multiple 'default'-statements inside a 'switch'-statement".to_string()
            }
            ErrorKind::IllegalAssign(left, right) => {
                format!("Can't assign to type '{}' with type '{}'", left, right)
            }
            ErrorKind::NotConstantInit(s) => {
                format!("{} can only be initialized to compile-time constants", s)
            }
            ErrorKind::InvalidExplicitCast(old_type, new_type) => {
                format!(
                    "Invalid cast from '{}' to '{}'. '{}' is not a scalar type",
                    old_type,
                    new_type,
                    if !old_type.is_scalar() {
                        old_type
                    } else {
                        new_type
                    }
                )
            }
            ErrorKind::NoReturnAllPaths(name) => {
                format!(
                    "Non-void function '{}' doesn't return in all code paths",
                    name
                )
            }
            ErrorKind::InvalidMainReturn(type_decl) => {
                format!("Expected 'main' return type 'int', found: '{}'", type_decl)
            }
            ErrorKind::TypeMismatch(left, right) => {
                format!("Mismatched operand types. '{}' and '{}'", left, right)
            }
            ErrorKind::InvalidSymbol(name, symbol) => {
                format!("Symbol '{}' already exists, but not as {}", name, symbol)
            }
            ErrorKind::InvalidMemberAccess(type_decl) => {
                format!(
                    "Can only access members of structs/unions, not '{}'",
                    type_decl
                )
            }
            ErrorKind::InvalidIncrementType(type_decl) => {
                format!("Can't increment value of type '{}'", type_decl)
            }
            ErrorKind::InvalidRvalueIncrement => "Can't increment Rvalues".to_string(),
            ErrorKind::NotAssignable(type_decl) => {
                format!("Type '{}' is not assignable", type_decl)
            }
            ErrorKind::NotLvalue => "Expect Lvalue left of assignment".to_string(),
            ErrorKind::MismatchedArity(name, expected, actual) => {
                format!(
                    "Function '{}' expected {} argument(s) found {}",
                    name, expected, actual
                )
            }
            ErrorKind::MismatchedArgs(index, func_name, param_name, expected, actual) => {
                match param_name {
                    Some(name) => {
                        format!(
                            "Mismatched arguments in function '{}': expected parameter '{}' to be of type '{}', found '{}'",
                            func_name,name.unwrap_string(), expected, actual
                        )
                    }
                    None => {
                        format!(
                            "Mismatched arguments in function '{}': expected {} parameter to be of type '{}', found '{}'",
                            func_name,num_to_ord(index + 1),  expected, actual
                        )
                    }
                }
            }
            ErrorKind::InvalidLogical(token, left_type, right_type) => {
                format!(
                    "Invalid logical expression: '{}' {} '{}'. Both types need to be scalar",
                    left_type, token, right_type
                )
            }
            ErrorKind::InvalidComp(token, left_type, right_type) => {
                format!(
                    "Invalid comparsion: '{}' {} '{}'",
                    left_type, token, right_type
                )
            }
            ErrorKind::InvalidBinary(token, left_type, right_type) => {
                format!(
                    "Invalid binary expression: '{}' {} '{}'",
                    left_type, token, right_type
                )
            }
            ErrorKind::InvalidDerefType(type_decl) => {
                format!(
                    "Can't dereference value-type '{}', expected type 'pointer'",
                    type_decl,
                )
            }
            ErrorKind::InvalidArrayReturn => "Can't return stack-array from function".to_string(),
            ErrorKind::MismatchedFunctionReturn(func_return, body_return) => {
                format!(
                    "Mismatched function return type: '{}', found: '{}'",
                    func_return, body_return
                )
            }

            ErrorKind::MismatchedFuncDeclReturn(expected, actual) => {
                format!(
                    "Conflicting return-types in function-declarations: expected {}, found {}",
                    expected, actual
                )
            }
            ErrorKind::MismatchedFuncDeclArity(expected, actual) => {
                format!(
                    "Mismatched number of parameters in function-declarations: expected {}, found {}",
                    expected,actual
                )
            }

            ErrorKind::MismatchedVariadic(expected, actual) => {
                let bool_to_msg = |val| {
                    if val {
                        "variadic args"
                    } else {
                        "no variadic args"
                    }
                };
                format!(
                    "Mismatched function-declarations: expected {}, found {}",
                    bool_to_msg(*expected),
                    bool_to_msg(*actual),
                )
            }
            ErrorKind::TypeMismatchFuncDecl(index, expected, actual) => {
                format!("Mismatched parameter-types in function-declarations: expected {} parameter to be of type '{}', found '{}'",
                            num_to_ord(index + 1),expected,actual)
            }
            ErrorKind::UndeclaredSymbol(name) => {
                format!("Undeclared symbol '{}'", name)
            }
            ErrorKind::InvalidUnary(token, right_type, kind) => {
                format!(
                    "Invalid unary-expression {} with type '{}'. Must be {}-type",
                    token, right_type, kind
                )
            }
            ErrorKind::UnnamedFuncParams => {
                "Unnamed parameters are not allowed in function definitions".to_string()
            }

            ErrorKind::InvalidHeader(s) => format!("'{}' is not a valid header file", s),
            ErrorKind::InvalidDirective(s) => {
                format!("'#{}' is not a valid preprocessor directive", s)
            }
            ErrorKind::UnterminatedIf(if_kind) => {
                format!("Unterminated '#{}'", if_kind)
            }
            ErrorKind::InvalidMacroName => "Macro name must be valid identifier".to_string(),
            ErrorKind::DuplicateElse => {
                "Can only have single '#else' in '#if'-directive".to_string()
            }
            ErrorKind::MissingIf(kind) => {
                format!("Found '#{}' without matching '#if'", kind)
            }
            ErrorKind::ElifAfterElse => "Found '#elif' after '#else'".to_string(),

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
            filename: object.filename().into(),
            kind,
        }
    }

    // Recursive helper-function chaining all found errors into single vector
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
    pub fn eof(expected: &'static str) -> Self {
        // TODO: have correct location info
        Error {
            line_index: -1,
            line_string: String::from(""),
            filename: PathBuf::from("current file"),
            column: -1,
            kind: ErrorKind::Eof(expected),
        }
    }
    pub fn print_error(&self) {
        let included = if let Some(Some("h")) = self.filename.extension().map(|s| s.to_str()) {
            "included file "
        } else {
            ""
        };
        eprintln!(
            "Error: in {}{}: {}",
            included,
            self.filename.display(),
            self.kind.message()
        );

        if self.line_index != -1 {
            let line_length = self.line_index.to_string().len();

            eprintln!("|");
            eprintln!("{} {}", self.line_index, self.line_string);
            eprint!("|");
            for _ in 1..self.column as usize + line_length {
                eprint!(" ");
            }
            eprintln!("^");
        }
    }

    pub fn sys_exit(msg: &str, exit_code: i32) -> ! {
        eprintln!("rucc: {msg}");
        std::process::exit(exit_code);
    }
}
pub trait Location {
    fn line_index(&self) -> i32;
    fn column(&self) -> i32;
    fn line_string(&self) -> String;
    fn filename(&self) -> PathBuf;
}
