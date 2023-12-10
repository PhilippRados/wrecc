use crate::compiler::common::{expr::*, stmt::*, token::Token, types::NEWTypes};
use std::collections::VecDeque;

use super::expr::PrintIndent;

pub enum ExternalDeclaration {
    Declaration(Vec<DeclarationKind>),
    Function(Token, Vec<Stmt>),
}

#[derive(Clone, Debug)]
pub struct Declarator {
    pub name: Option<Token>,
    pub type_decl: NEWTypes,
    pub is_typedef: bool,
}
pub enum DeclaratorKind {
    Abstract,
    NoAbstract,
    MaybeAbstract,
}

// TODO: only need vardecl
#[derive(Clone, Debug)]
pub enum DeclarationKind {
    VarDecl(NEWTypes, Token, Option<Init>, bool),
    FuncDecl(Token),
}

impl DeclarationKind {
    pub fn get_token(&self) -> &Token {
        match self {
            DeclarationKind::VarDecl(_, token, ..) | DeclarationKind::FuncDecl(token) => token,
        }
    }
}
impl PartialEq for DeclarationKind {
    fn eq(&self, other: &Self) -> bool {
        self.get_token().unwrap_string() == other.get_token().unwrap_string()
    }
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
    Array(i64),
    Member(String),
}

impl PrintIndent for ExternalDeclaration {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            ExternalDeclaration::Function(name, body) => {
                let body = body
                    .iter()
                    .map(|s| indent_fmt(s, indent_level + 1))
                    .collect::<Vec<String>>()
                    .join("\n");

                format!("Func: '{}'\n{}", name.unwrap_string(), body)
            }
            ExternalDeclaration::Declaration(decls) => {
                let decls = decls
                    .iter()
                    .map(|kind| indent_fmt(kind,indent_level + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("Decl:\n{}",decls)
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

impl PrintIndent for DeclarationKind {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            DeclarationKind::VarDecl(_, t, init, _) => {
                if let Some(init) = init {
                    format!(
                        "VarInit: '{}'\n{}",
                        t.unwrap_string(),
                        indent_fmt(&init.kind, indent_level + 1)
                    )
                } else {
                    format!("VarDecl: '{}'", t.unwrap_string())
                }
            }
            DeclarationKind::FuncDecl(t) => {
                format!("FuncDecl: '{}'", t.unwrap_string())
            }

        }
    }

}

impl std::fmt::Display for DeclarationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}
