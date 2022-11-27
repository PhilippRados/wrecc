use crate::common::token::TokenKind;
use std::fmt::Display;

static RETURN_REG: &[&'static str; 3] = &["%al", "%eax", "%rax"];

pub trait TypeInfo {
    // returns size in bytes of type
    fn size(&self) -> usize;

    // returns the correct suffix for a register of type
    fn reg_suffix(&self) -> &str;

    // returns the correct suffix for an instruction of type
    fn suffix(&self) -> &str;

    // returns the return register name of type
    fn return_reg(&self) -> &str;
}

#[derive(Clone, PartialEq, Debug)]
pub enum NEWTypes {
    Primitive(Types),
    Array {
        amount: usize,
        element_type: Box<NEWTypes>,
    },
    Pointer(Box<NEWTypes>),
}

impl TypeInfo for NEWTypes {
    fn size(&self) -> usize {
        match self {
            NEWTypes::Primitive(t) => t.size(),
            NEWTypes::Pointer(_) => 8,
            NEWTypes::Array {
                amount,
                element_type,
            } => amount * element_type.size(),
        }
    }
    fn reg_suffix(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.reg_suffix(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } => "",
        }
    }
    fn suffix(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.suffix(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } => "q",
        }
    }
    fn return_reg(&self) -> &str {
        match self {
            NEWTypes::Primitive(t) => t.return_reg(),
            NEWTypes::Pointer(_) | NEWTypes::Array { .. } => RETURN_REG[2],
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
                NEWTypes::Array {
                    element_type,
                    amount,
                } => format!("{}[{}]", element_type, amount),
                NEWTypes::Pointer(to) => format!("{}*", to),
            }
        )
    }
}

#[macro_export]
macro_rules! arr_decay {
    ($arr:expr) => {
        if let NEWTypes::Array { element_type, .. } = $arr {
            $arr = NEWTypes::Pointer(element_type)
        }
    };
}
impl NEWTypes {
    pub fn to_array(&mut self, amount: usize) {
        *self = NEWTypes::Array {
            amount,
            element_type: Box::new(self.clone()),
        }
    }
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
        matches!(*self, NEWTypes::Pointer(_)) || matches!(*self, NEWTypes::Array { .. })
    }
    pub fn type_compatible(&self, other: &NEWTypes) -> bool {
        match (self, other) {
            (NEWTypes::Primitive(Types::Void), NEWTypes::Primitive(Types::Void)) => true,

            (NEWTypes::Primitive(Types::Void), NEWTypes::Primitive(_))
            | (NEWTypes::Primitive(_), NEWTypes::Primitive(Types::Void)) => false,

            (NEWTypes::Primitive(_), NEWTypes::Primitive(_)) => true,

            (NEWTypes::Pointer(_), NEWTypes::Pointer(_)) => *self == *other,

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
        match self {
            Types::Void => unreachable!(),
            Types::Char => "b",
            Types::Int => "l",
            Types::Long => "q",
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
