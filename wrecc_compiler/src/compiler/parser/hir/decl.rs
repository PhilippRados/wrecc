use crate::compiler::common::token::Token;
use crate::compiler::parser::hir::{expr::*, stmt::*};
use std::collections::VecDeque;

use super::expr::PrintIndent;

pub enum ExternalDeclaration {
    Declaration(Declaration),
    Function(FuncDecl, Vec<Stmt>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub specifiers: Vec<DeclSpecifier>,
    pub storage_classes: Vec<StorageClass>,
    pub is_inline: bool,
    pub declarators: Vec<(Declarator, Option<Init>)>,
}

pub struct FuncDecl {
    pub specifiers: Vec<DeclSpecifier>,
    pub storage_classes: Vec<StorageClass>,
    pub is_inline: bool,
    pub name: Token,
    pub modifiers: Vec<DeclModifier>,
}

pub struct ParsedSpecifiers {
    pub specifiers: Vec<DeclSpecifier>,
    pub storage_classes: Vec<StorageClass>,
    pub is_inline: bool,
}
impl ParsedSpecifiers {
    pub fn new() -> Self {
        ParsedSpecifiers {
            specifiers: Vec::new(),
            storage_classes: Vec::new(),
            is_inline: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct DeclType {
    pub specifiers: Vec<DeclSpecifier>,
    pub modifiers: Vec<DeclModifier>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct DeclSpecifier {
    pub token: Token,
    pub kind: SpecifierKind,
}
#[derive(Clone, Debug, PartialEq)]
pub struct StorageClass {
    pub token: Token,
    pub kind: StorageClassKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum StorageClassKind {
    TypeDef,
    Extern,
    Static,
    Auto,
    Register,
}

pub type MemberDeclaration = (Vec<DeclSpecifier>, Vec<MemberDeclarator>);

#[derive(Clone, Debug, PartialEq)]
pub struct MemberDeclarator {
    pub name: Token,
    pub modifiers: Vec<DeclModifier>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SpecifierKind {
    Void,
    Char,
    Short,
    Int,
    Long,

    Struct(Option<Token>, Option<Vec<MemberDeclaration>>),
    Union(Option<Token>, Option<Vec<MemberDeclaration>>),
    Enum(Option<Token>, Option<Vec<(Token, Option<ExprKind>)>>),

    UserType,
}
impl SpecifierKind {
    pub fn order(&self) -> usize {
        match self {
            SpecifierKind::Void => 0,
            SpecifierKind::Char => 1,
            SpecifierKind::Short => 2,
            SpecifierKind::Long => 3,
            // int is last in specifier order because thats easier to read:
            // eg: `short int` `long int`
            SpecifierKind::Int => 4,
            _ => 5,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ParamDecl {
    pub specifiers: Vec<DeclSpecifier>,
    pub storage_classes: Vec<StorageClass>,
    pub is_inline: bool,
    pub declarator: Declarator,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclModifier {
    Pointer,
    Array(Token, Option<ExprKind>),
    Function { params: Vec<ParamDecl>, variadic: bool, token: Token },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declarator {
    pub name: Option<Token>,
    pub modifiers: Vec<DeclModifier>,
}
pub enum DeclaratorKind {
    Abstract,
    NoAbstract,
    MaybeAbstract,
}

#[derive(PartialEq, Clone, Debug)]
pub struct Init {
    pub kind: InitKind,
    pub designator: Option<VecDeque<Designator>>,
    pub token: Token,
}
#[derive(PartialEq, Clone, Debug)]
pub enum InitKind {
    Scalar(ExprKind),
    Aggr(Vec<Box<Init>>),
}

#[derive(PartialEq, Clone, Debug)]
pub struct Designator {
    pub kind: DesignatorKind,
    pub token: Token,
}
#[derive(PartialEq, Clone, Debug)]
pub enum DesignatorKind {
    Array(ExprKind),
    Member(String),
}

impl PrintIndent for ExternalDeclaration {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            ExternalDeclaration::Function(FuncDecl { name, .. }, body) => {
                let body = body
                    .iter()
                    .map(|s| indent_fmt(s, indent_level + 1))
                    .collect::<Vec<String>>()
                    .join("\n")
                    .or_empty(indent_level + 1);

                format!("FuncDef: '{}'\n{}", name.unwrap_string(), body)
            }
            ExternalDeclaration::Declaration(decl) => decl.print_indent(indent_level + 1),
        }
    }
}

impl std::fmt::Display for ExternalDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}

impl PrintIndent for InitKind {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            InitKind::Scalar(expr) => format!("Scalar:\n{}", indent_fmt(expr, indent_level + 1)),
            InitKind::Aggr(list) => format!(
                "Aggregate:\n{}",
                list.iter()
                    .map(|init| indent_fmt(&init.kind, indent_level + 1))
                    .collect::<Vec<String>>()
                    .join("\n")
                    .or_empty(indent_level + 1)
            ),
        }
    }
}
impl PrintIndent for Declaration {
    fn print_indent(&self, indent_level: usize) -> String {
        let indent = "-".repeat(indent_level);
        let decls = self
            .declarators
            .iter()
            .map(|(declarator, init)| {
                if let Some(name) = &declarator.name {
                    match init {
                        Some(init) => format!(
                            "{}Init: '{}'\n{}",
                            indent,
                            name.unwrap_string(),
                            indent_fmt(&init.kind, indent_level + 1)
                        ),
                        None => format!("{}Decl: '{}'", indent, name.unwrap_string()),
                    }
                } else {
                    String::from("")
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
            .or_empty(indent_level);

        let typedef = if self
            .storage_classes
            .iter()
            .any(|storage| storage.kind == StorageClassKind::TypeDef)
        {
            "Typedef-"
        } else {
            ""
        };
        format!("{}Declaration:\n{}", typedef, decls)
    }
}

impl std::fmt::Display for InitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}
