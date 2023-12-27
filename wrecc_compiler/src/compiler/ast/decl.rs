use crate::compiler::ast::{expr::*, stmt::*};
use crate::compiler::common::token::Token;
use std::collections::VecDeque;

use super::expr::PrintIndent;

pub enum ExternalDeclaration {
    Declaration(Declaration),
    Function(DeclType, Token, Vec<Stmt>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub specifiers: Vec<DeclSpecifier>,
    pub declarators: Vec<(Declarator, Option<Init>)>,
    pub is_typedef: bool,
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

pub type MemberDeclaration = (Vec<DeclSpecifier>, Vec<Declarator>);

#[derive(Clone, Debug, PartialEq)]
pub enum SpecifierKind {
    Void,
    Char,
    Int,
    Long,

    Struct(Option<Token>, Option<Vec<MemberDeclaration>>),
    Union(Option<Token>, Option<Vec<MemberDeclaration>>),
    Enum(Option<Token>, Option<Vec<(Token, Option<Expr>)>>),

    UserType,
}
impl SpecifierKind {
    pub fn order(&self) -> usize {
        match self {
            SpecifierKind::Void => 0,
            SpecifierKind::Char => 1,
            SpecifierKind::Int => 2,
            SpecifierKind::Long => 3,
            _ => 4,
        }
    }
}
#[derive(Clone, Debug, PartialEq)]
pub enum DeclModifier {
    Pointer,
    Array(Token, Expr),
    Function {
        params: Vec<(Vec<DeclSpecifier>, Declarator)>,
        variadic: bool,
        token: Token,
    },
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
    pub offset: i64,
}
#[derive(PartialEq, Clone, Debug)]
pub enum InitKind {
    Scalar(Expr),
    Aggr(Vec<Box<Init>>),
}

#[derive(PartialEq, Clone, Debug)]
pub struct Designator {
    pub kind: DesignatorKind,
    pub token: Token,
}
#[derive(PartialEq, Clone, Debug)]
pub enum DesignatorKind {
    Array(Expr),
    Member(String),
}

impl PrintIndent for ExternalDeclaration {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            ExternalDeclaration::Function(_, name, body) => {
                let body = body
                    .iter()
                    .map(|s| indent_fmt(s, indent_level + 1))
                    .collect::<Vec<String>>()
                    .join("\n");

                format!("Func: '{}'\n{}", name.unwrap_string(), body)
            }
            ExternalDeclaration::Declaration(_decls) => {
                // let decls = decls
                //     .iter()
                //     .map(|kind| indent_fmt(kind, indent_level + 1))
                //     .collect::<Vec<_>>()
                //     .join("\n");
                // format!("Decl:\n{}", decls)
                "decl".to_string()
            }
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
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        }
    }
}
impl std::fmt::Display for InitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}