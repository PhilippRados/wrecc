use crate::common::{token::*, types::*};
use crate::scanner::Scanner;

#[derive(Debug, PartialEq, Clone)]
pub enum ErrorKind {
    // scan errors
    UnexpectedChar(char),
    CharLiteralQuotes,
    CharLiteralAscii(char),
    InvalidEscape(char),
    UnterminatedString,
    Eof(&'static str),

    // parsing errors
    BracketsNotAllowed,
    NotIntegerConstant(&'static str),
    NegativeArraySize,
    IsEmpty(TokenType),
    EnumOverflow,
    IncompleteType(NEWTypes),
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
    IllegalVoidDecl(String),
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
    InvalidLogical(TokenType, NEWTypes, NEWTypes),
    InvalidBinary(TokenType, NEWTypes, NEWTypes),
    InvalidDerefType(NEWTypes),
    InvalidArrayReturn,
    MismatchedFunctionReturn(NEWTypes, NEWTypes),
    InvalidUnary(TokenType, NEWTypes, &'static str),

    // environment errors
    MismatchedFuncDeclReturn(NEWTypes, NEWTypes),
    MismatchedFuncDeclArity(usize, usize),
    TypeMismatchFuncDecl(NEWTypes, NEWTypes),
    UndeclaredSymbol(String),
    IntegerOverflow(NEWTypes),

    Regular(&'static str), // generic error message when message only used once
    Indicator,             // just to signal an error occured
}

impl ErrorKind {
    fn message(&self) -> String {
        match self {
            ErrorKind::UnexpectedChar(c) => format!("Unexpected character: {}", c),
            ErrorKind::Eof(s) => format!("Expected {}, found end of file", s),
            ErrorKind::CharLiteralQuotes => {
                "Character literal must contain single character enclosed by single quotes ('')"
                    .to_string()
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
            ErrorKind::NotType(token) => format!("Expected type-declaration, found {}", token),
            ErrorKind::UndeclaredType(s) => format!("Undeclared type '{}'", s),
            ErrorKind::IncompleteMemberAccess(type_decl) => {
                format!("Can't access members of incomplete type '{}'", type_decl)
            }
            ErrorKind::TypeAlreadyExists(name, token) => {
                format!("Type '{}' already exists but not as {}", name, token)
            }
            ErrorKind::EnumForwardDecl => "Can't forward declare enums".to_string(),
            ErrorKind::EmptyAggregate(token) => {
                format!("Can't declare anonymous {} without members", token)
            }
            // ErrorKind::FunctionRedefinition(name) => {
            //
            // }
            // ErrorKind::SymbolRedefinition => "Redefinition of symbol with same name".to_string(),
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
            ErrorKind::IllegalVoidDecl(name) => {
                format!("Can't declare variable '{}' as 'void'", name)
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
                    "At '{}': expected {} argument(s) found {}",
                    name, expected, actual
                )
            }
            ErrorKind::InvalidLogical(token, left_type, right_type) => {
                format!(
                    "Invalid logical expression: '{}' {} '{}'. Both types need to be scalar",
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
            ErrorKind::TypeMismatchFuncDecl(expected, actual) => {
                format!("Mismatched parameter-types in function-declarations: expected '{}', found '{}'",
                            expected,actual)
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

            ErrorKind::Regular(s) => s.to_string(),
            ErrorKind::Indicator => unreachable!(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Error {
    pub line_index: i32,
    pub line_string: String,
    pub column: i32,
    pub kind: ErrorKind,
}
impl Error {
    pub fn new(t: &Token, kind: ErrorKind) -> Self {
        Error {
            line_index: t.line_index,
            line_string: t.line_string.clone(),
            column: t.column,
            kind,
        }
    }
    pub fn new_scan_error(scanner: &Scanner, kind: ErrorKind) -> Self {
        Error {
            line_index: scanner.line,
            line_string: scanner.raw_source[(scanner.line - 1) as usize].clone(),
            column: scanner.column,
            kind,
        }
    }
    pub fn eof() -> Self {
        Error {
            line_index: -1,
            line_string: String::from(""),
            column: -1,
            kind: ErrorKind::Regular("Expected expression found end of file"),
        }
    }
    pub fn indicator() -> Self {
        Error {
            line_index: -1,
            line_string: String::from(""),
            column: -1,
            kind: ErrorKind::Indicator,
        }
    }
    pub fn is_indicator(&self) -> bool {
        matches!(self.kind, ErrorKind::Indicator)
    }
    pub fn print_error(&self) {
        eprintln!("Error: {}", self.kind.message());

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
