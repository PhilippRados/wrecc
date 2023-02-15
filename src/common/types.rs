use crate::common::token::{Token, TokenKind};
use std::fmt::Display;
use std::rc::Rc;
pub use struct_ref::StructRef;

static RETURN_REG: &[&str; 3] = &["%al", "%eax", "%rax"];

pub trait TypeInfo {
    // returns size in bytes of type
    fn size(&self) -> usize;

    // returns the correct suffix for a register of type
    fn reg_suffix(&self) -> &str;

    // returns the instruction-suffixes
    fn suffix(&self) -> &str;

    // returns the instruction-suffixes spelled out
    fn complete_suffix(&self) -> &str;

    // returns the return register name of type
    fn return_reg(&self) -> &str;
}

#[derive(Clone, PartialEq, Debug)]
pub enum NEWTypes {
    Primitive(Types),
    Array { amount: usize, of: Box<NEWTypes> },
    Pointer(Box<NEWTypes>),
    Struct(StructInfo),
}

// this code is shamelessly copied from the more sophisticated saltwater compiler
mod struct_ref {
    use super::NEWTypes;
    use super::Token;
    use std::cell::RefCell;
    use std::rc::Rc;

    thread_local! {
        static CUSTOMS: RefCell<Vec<Rc<Vec<(NEWTypes, Token)>>>> = Default::default();
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct StructRef {
        index: usize,
    }
    impl Default for StructRef {
        fn default() -> Self {
            Self::new()
        }
    }

    impl StructRef {
        pub fn new() -> StructRef {
            CUSTOMS.with(|list| {
                let mut types = list.borrow_mut();
                let index = types.len();
                types.push(Rc::new(vec![]));
                StructRef { index }
            })
        }

        pub fn get(&self) -> Rc<Vec<(NEWTypes, Token)>> {
            CUSTOMS.with(|list| list.borrow()[self.index].clone())
        }
        pub(crate) fn update(&self, members: Vec<(NEWTypes, Token)>) {
            CUSTOMS.with(|list| {
                let mut types = list.borrow_mut();
                types[self.index] = members.into();
            });
        }
    }
}
#[derive(Clone, PartialEq, Debug)]
pub enum StructInfo {
    Named(String, StructRef),
    Anonymous(Vec<(NEWTypes, Token)>),
}
impl StructInfo {
    pub fn members(&self) -> Rc<Vec<(NEWTypes, Token)>> {
        match self {
            StructInfo::Named(_, s) => s.get(),
            StructInfo::Anonymous(m) => Rc::new(m.clone()),
        }
    }
    fn name(&self) -> &str {
        match self {
            StructInfo::Named(name, _) => name,
            StructInfo::Anonymous(_) => "anonymous",
        }
    }
}

impl TypeInfo for NEWTypes {
    fn size(&self) -> usize {
        match self {
            NEWTypes::Primitive(t) => t.size(),
            NEWTypes::Struct(s) => s.members().iter().fold(0, |acc, (t, _)| acc + t.size()),
            NEWTypes::Pointer(_) => 8,
            NEWTypes::Array {
                amount,
                of: element_type,
            } => amount * element_type.size(),
        }
    }
    fn reg_suffix(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.reg_suffix(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } | NEWTypes::Struct(..) => "",
        }
    }
    fn suffix(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.suffix(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } | NEWTypes::Struct(..) => "q",
        }
    }
    fn complete_suffix(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.complete_suffix(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } | NEWTypes::Struct(..) => "quad",
        }
    }
    fn return_reg(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.return_reg(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } => RETURN_REG[2],
            NEWTypes::Struct(..) => unimplemented!(),
        }
    }
}
impl Display for NEWTypes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                NEWTypes::Primitive(t) => t.fmt().to_string(),
                NEWTypes::Array { of, amount } => format!("{}[{}]", of, amount),
                NEWTypes::Pointer(to) => format!("{}*", to),
                NEWTypes::Struct(s) => s.name().to_string(),
            }
        )
    }
}

#[macro_export]
macro_rules! arr_decay {
    ($arr:expr,$ast:expr,$token:expr,$is_global:expr) => {
        if let NEWTypes::Array { of, .. } = $arr {
            $arr = NEWTypes::Pointer(of);

            $ast.kind = ExprKind::Unary {
                token: Token::new(
                    TokenType::Amp,
                    $token.line_index,
                    $token.column,
                    $token.line_string.clone(),
                ),
                right: Box::new($ast.clone()),
                is_global: $is_global,
            };
        }
    };
}
impl NEWTypes {
    pub fn pointer_to(&mut self) {
        *self = NEWTypes::Pointer(Box::new(self.clone()));
    }
    pub fn deref_at(&self) -> Option<NEWTypes> {
        match self {
            NEWTypes::Pointer(inner) => Some(*inner.clone()),
            _ => None,
        }
    }
    pub fn is_void(&self) -> bool {
        *self == NEWTypes::Primitive(Types::Void)
    }
    pub fn is_ptr(&self) -> bool {
        matches!(*self, NEWTypes::Pointer(_))
    }
    pub fn type_compatible(&self, other: &NEWTypes) -> bool {
        match (self, other) {
            (NEWTypes::Primitive(Types::Void), NEWTypes::Primitive(Types::Void)) => true,

            (NEWTypes::Primitive(Types::Void), NEWTypes::Primitive(_))
            | (NEWTypes::Primitive(_), NEWTypes::Primitive(Types::Void)) => false,

            (NEWTypes::Primitive(_), NEWTypes::Primitive(_)) => true,

            (NEWTypes::Pointer(l), NEWTypes::Pointer(r))
                if matches!(**l, NEWTypes::Struct(..)) && matches!(**r, NEWTypes::Struct(..)) =>
            {
                l.type_compatible(r)
            }
            (NEWTypes::Pointer(_), NEWTypes::Pointer(_)) => *self == *other,

            // two structs are compatible if they have the same name and members
            (NEWTypes::Struct(s_l), NEWTypes::Struct(s_r)) => {
                if let (StructInfo::Named(name_l, _), StructInfo::Named(name_r, _)) = (s_l, s_r) {
                    let matching_members = s_l
                        .members()
                        .iter()
                        .zip(s_r.members().iter())
                        .filter(|(l, r)| l.0 == r.0 && l.1.unwrap_string() == r.1.unwrap_string())
                        .count();
                    *name_l == *name_r
                        && matching_members == s_l.members().len()
                        && matching_members == s_r.members().len()
                } else {
                    false
                }
            }

            _ => false,
        }
    }
}
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Types {
    Void,
    Char,
    Int,
    Long,
}

impl TypeInfo for Types {
    fn size(&self) -> usize {
        match self {
            Types::Void => 0,
            Types::Char => 1,
            Types::Int => 4,
            Types::Long => 8,
        }
    }
    fn reg_suffix(&self) -> &str {
        match self {
            Types::Void => unreachable!(),
            Types::Char => "b",
            Types::Int => "d",
            Types::Long => "",
        }
    }
    fn suffix(&self) -> &str {
        self.complete_suffix().get(0..1).unwrap()
    }
    fn complete_suffix(&self) -> &str {
        match self {
            Types::Void => unreachable!(),
            Types::Char => "byte",
            Types::Int => "long",
            Types::Long => "quad",
        }
    }
    fn return_reg(&self) -> &str {
        match self {
            Types::Void => unreachable!("doesnt have return register when returning void"),
            Types::Char => RETURN_REG[0],
            Types::Int => RETURN_REG[1],
            Types::Long => RETURN_REG[2],
        }
    }
}
impl Types {
    pub fn into_vec() -> Vec<TokenKind> {
        vec![
            TokenKind::Char,
            TokenKind::Int,
            TokenKind::Void,
            TokenKind::Long,
        ]
    }
    fn fmt(&self) -> &str {
        match self {
            Types::Void => "void",
            Types::Char => "char",
            Types::Int => "int",
            Types::Long => "long",
        }
    }
}
