pub use struct_ref::StructRef;

use crate::compiler::common::token::*;
use crate::compiler::parser::hir::expr::*;

use std::fmt::Display;
use std::rc::Rc;

static RETURN_REG: &[&str; 4] = &["%al", "%ax", "%eax", "%rax"];

pub trait TypeInfo {
    /// Returns size of type in bytes
    fn size(&self) -> usize;

    /// Returns the correct suffix for a register of type
    fn reg_suffix(&self) -> String;

    /// Returns the instruction-suffixes
    fn suffix(&self) -> String;

    /// Returns the instruction-suffixes spelled out
    fn complete_suffix(&self) -> String;

    /// Returns the return register name of type
    fn return_reg(&self) -> String;
}

/// All C-types in currently implemented in `wrecc`
#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Primitive(Primitive),
    Array(Box<Type>, ArraySize),
    Pointer(Box<Type>),
    Struct(StructInfo),
    Union(StructInfo),
    Enum(Option<String>, Vec<(Token, i32)>),
    Function(FuncType),
}

#[derive(Clone, PartialEq, Debug)]
pub enum ArraySize {
    Known(usize),
    Unknown,
}

impl TypeInfo for Type {
    fn size(&self) -> usize {
        match self {
            Type::Primitive(t) => t.size(),
            Type::Struct(s) => s.members().iter().fold(0, |acc, (t, _)| acc + t.size()),
            Type::Union(_) => self.union_biggest().size(),
            Type::Pointer(_) => Type::Primitive(Primitive::Long).size(),
            Type::Enum(..) => Type::Primitive(Primitive::Int).size(),
            Type::Array(element_type, ArraySize::Known(amount)) => amount * element_type.size(),
            // INFO: tentative array assumed to have one element
            Type::Array(element_type, ArraySize::Unknown) => element_type.size(),
            Type::Function(_) => 1,
        }
    }
    fn reg_suffix(&self) -> String {
        match self {
            Type::Primitive(t) => t.reg_suffix(),
            Type::Union(_) => self.union_biggest().reg_suffix(),
            Type::Enum(..) => Type::Primitive(Primitive::Int).reg_suffix(),
            Type::Pointer(_) | Type::Array { .. } | Type::Struct(..) => {
                Type::Primitive(Primitive::Long).reg_suffix()
            }
            Type::Function { .. } => unreachable!("no plain function type used"),
        }
    }
    fn suffix(&self) -> String {
        match self {
            Type::Primitive(t) => t.suffix(),
            Type::Union(_) => self.union_biggest().suffix(),
            Type::Enum(..) => Type::Primitive(Primitive::Int).suffix(),
            Type::Pointer(_) | Type::Array { .. } | Type::Struct(..) => {
                Type::Primitive(Primitive::Long).suffix()
            }
            Type::Function { .. } => unreachable!("no plain function type used"),
        }
    }
    fn complete_suffix(&self) -> String {
        match self {
            Type::Primitive(t) => t.complete_suffix(),
            Type::Union(_) => self.union_biggest().complete_suffix(),
            Type::Enum(..) => Type::Primitive(Primitive::Int).complete_suffix(),
            Type::Pointer(_) | Type::Array { .. } | Type::Struct(..) => {
                Type::Primitive(Primitive::Long).complete_suffix()
            }
            Type::Function { .. } => unreachable!("no plain function type used"),
        }
    }
    fn return_reg(&self) -> String {
        match self {
            Type::Primitive(t) => t.return_reg(),
            Type::Pointer(_) | Type::Array { .. } => Type::Primitive(Primitive::Long).return_reg(),
            Type::Enum(..) => Type::Primitive(Primitive::Int).return_reg(),
            Type::Union(..) => self.union_biggest().return_reg(),
            Type::Struct(..) => unimplemented!("currently can't return structs"),
            Type::Function { .. } => unreachable!("no plain function type used"),
        }
    }
}
impl Type {
    pub fn pointer_to(self) -> Type {
        Type::Pointer(Box::new(self.clone()))
    }
    pub fn function_of(self, params: Vec<Type>, variadic: bool) -> Type {
        Type::Function(FuncType {
            return_type: Box::new(self),
            params,
            variadic,
        })
    }
    pub fn deref_at(&self) -> Option<Type> {
        match self {
            Type::Pointer(inner) => Some(*inner.clone()),
            _ => None,
        }
    }
    pub fn is_void(&self) -> bool {
        *self == Type::Primitive(Primitive::Void)
    }
    pub fn is_func(&self) -> bool {
        matches!(self, Type::Function { .. })
    }
    pub fn is_unbounded_array(&self) -> bool {
        matches!(self, Type::Array(_, ArraySize::Unknown))
    }
    pub fn is_array(&self) -> bool {
        matches!(self, Type::Array { .. })
    }
    pub fn is_ptr(&self) -> bool {
        matches!(self, Type::Pointer(_))
    }
    pub fn type_compatible(&self, other: &Type, other_expr: &impl IsZero) -> bool {
        match (self, other) {
            (Type::Primitive(Primitive::Void), Type::Primitive(Primitive::Void)) => true,

            (Type::Primitive(Primitive::Void), Type::Primitive(_))
            | (Type::Primitive(_), Type::Primitive(Primitive::Void)) => false,

            (Type::Primitive(_), Type::Primitive(_)) => true,

            // pointer to null-pointer-constant
            (Type::Pointer(_), _) if other_expr.is_zero() => true,

            // have to catch this since otherwise pointers are compared deeply
            (Type::Pointer(l), Type::Pointer(r)) if l.is_aggregate() && r.is_aggregate() => {
                l.type_compatible(r, other_expr)
            }
            // void* is compatible to any other pointer
            (Type::Pointer(t), Type::Pointer(_)) | (Type::Pointer(_), Type::Pointer(t))
                if matches!(**t, Type::Primitive(Primitive::Void)) =>
            {
                true
            }
            (Type::Array(of1, ArraySize::Known(size1)), Type::Array(of2, ArraySize::Known(size2))) => {
                size1 == size2 && of1.type_compatible(of2, other_expr)
            }
            // unspecified arrays are compatible if they have the same type
            (Type::Array(of1, ArraySize::Unknown), Type::Array(of2, ArraySize::Unknown))
            | (Type::Array(of1, ArraySize::Known(_)), Type::Array(of2, ArraySize::Unknown))
            | (Type::Array(of1, ArraySize::Unknown), Type::Array(of2, ArraySize::Known(_))) => {
                of1.type_compatible(of2, other_expr)
            }

            (Type::Pointer(_), Type::Pointer(_)) => *self == *other,

            // two structs/unions are compatible if they refer to the same definition
            (Type::Struct(s_l), Type::Struct(s_r)) | (Type::Union(s_l), Type::Union(s_r)) => {
                match (s_l, s_r) {
                    (StructInfo::Named(_, l_ref), StructInfo::Named(_, r_ref)) => l_ref == r_ref,
                    (StructInfo::Unnamed(name_l, _), StructInfo::Unnamed(name_r, _)) => name_l == name_r,
                    _ => false,
                }
            }
            (Type::Enum(..), Type::Primitive(Primitive::Void))
            | (Type::Primitive(Primitive::Void), Type::Enum(..)) => false,

            (Type::Enum(..), Type::Primitive(_)) | (Type::Primitive(_), Type::Enum(..)) => true,

            // func is compatible to func if they have the exact same signature
            (Type::Function(f1), Type::Function(f2)) => f1 == f2,

            _ => false,
        }
    }
    pub fn is_scalar(&self) -> bool {
        match self {
            Type::Primitive(Primitive::Void) => false,
            Type::Primitive(_) | Type::Pointer(_) | Type::Enum(..) => true,
            _ => false,
        }
    }
    pub fn is_integer(&self) -> bool {
        match self {
            Type::Primitive(Primitive::Void) => false,
            Type::Primitive(_) | Type::Enum(..) => true,
            _ => false,
        }
    }
    pub fn is_struct(&self) -> bool {
        matches!(self, Type::Struct(_) | Type::Union(_))
    }
    pub fn is_aggregate(&self) -> bool {
        matches!(self, Type::Struct(_) | Type::Union(_) | Type::Array(..))
    }
    fn union_biggest(&self) -> Type {
        match self {
            Type::Union(s) => s
                .members()
                .iter()
                .max_by_key(|(type_decl, _)| type_decl.size())
                .expect("union can't be empty, checked in parser")
                .0
                .clone(),
            _ => unreachable!("not union"),
        }
    }
    pub fn is_complete(&self) -> bool {
        match self {
            Type::Struct(s) | Type::Union(s) => s.is_complete(),
            Type::Array(of, ArraySize::Known(_)) => of.is_complete(),
            Type::Array(_, ArraySize::Unknown) => false,
            _ if self.is_void() => false,
            _ => true,
        }
    }

    pub fn max(&self) -> i64 {
        match self {
            Type::Primitive(t) => t.max(),
            Type::Enum(..) => i32::MAX as i64,
            Type::Pointer(_) => i64::MAX,
            _ => unreachable!(),
        }
    }
    pub fn min(&self) -> i64 {
        match self {
            Type::Primitive(t) => t.min(),
            Type::Enum(..) => i32::MIN as i64,
            Type::Pointer(_) => i64::MIN,
            _ => unreachable!(),
        }
    }

    pub fn maybe_wrap(&self, n: i64) -> Option<i64> {
        match self {
            Type::Primitive(Primitive::Char) => Some(n as i8 as i64),
            Type::Primitive(Primitive::Short) => Some(n as i16 as i64),
            Type::Primitive(Primitive::Int) | Type::Enum(..) => Some(n as i32 as i64),
            Type::Pointer(_) | Type::Primitive(Primitive::Long) => Some(n),
            _ => None,
        }
    }

    pub fn get_primitive(&self) -> Option<&Primitive> {
        if let Type::Primitive(type_decl) = self {
            Some(type_decl)
        } else {
            None
        }
    }
    pub fn is_char_array(&self) -> Option<&ArraySize> {
        if let Type::Array(of, size) = self {
            if let Type::Primitive(Primitive::Char) = **of {
                return Some(size);
            }
        }
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct FuncType {
    pub return_type: Box<Type>,
    pub params: Vec<Type>,
    pub variadic: bool,
}

#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Primitive {
    Void,
    Char,
    Short,
    Int,
    Long,
}

impl TypeInfo for Primitive {
    /// Returns type-size in bytes
    fn size(&self) -> usize {
        match self {
            Primitive::Void => 0,
            Primitive::Char => 1,
            Primitive::Short => 2,
            Primitive::Int => 4,
            Primitive::Long => 8,
        }
    }
    fn reg_suffix(&self) -> String {
        String::from(match self {
            Primitive::Void => unreachable!(),
            Primitive::Char => "b",
            Primitive::Short => "w",
            Primitive::Int => "d",
            Primitive::Long => "",
        })
    }
    fn suffix(&self) -> String {
        self.complete_suffix().get(0..1).unwrap().to_string()
    }
    fn complete_suffix(&self) -> String {
        String::from(match self {
            Primitive::Void => "zero",
            Primitive::Char => "byte",
            Primitive::Short => "word",
            Primitive::Int => "long",
            Primitive::Long => "quad",
        })
    }
    fn return_reg(&self) -> String {
        String::from(match self {
            Primitive::Void => unreachable!("doesnt have return register when returning void"),
            Primitive::Char => RETURN_REG[0],
            Primitive::Short => RETURN_REG[1],
            Primitive::Int => RETURN_REG[2],
            Primitive::Long => RETURN_REG[3],
        })
    }
}
impl Primitive {
    fn fmt(&self) -> &str {
        match self {
            Primitive::Void => "void",
            Primitive::Char => "char",
            Primitive::Short => "short",
            Primitive::Int => "int",
            Primitive::Long => "long",
        }
    }

    fn max(&self) -> i64 {
        match self {
            Primitive::Void => unreachable!(),
            Primitive::Char => i8::MAX as i64,
            Primitive::Short => i16::MAX as i64,
            Primitive::Int => i32::MAX as i64,
            Primitive::Long => i64::MAX,
        }
    }
    fn min(&self) -> i64 {
        match self {
            Primitive::Void => unreachable!(),
            Primitive::Char => i8::MIN as i64,
            Primitive::Short => i16::MIN as i64,
            Primitive::Int => i32::MIN as i64,
            Primitive::Long => i64::MIN,
        }
    }
}

pub fn integer_type(n: i64) -> Primitive {
    if i32::try_from(n).is_ok() {
        Primitive::Int
    } else {
        Primitive::Long
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum StructInfo {
    Named(String, StructRef),
    Unnamed(Token, Vec<(Type, Token)>),
}
impl StructInfo {
    pub fn members(&self) -> Rc<Vec<(Type, Token)>> {
        match self {
            StructInfo::Named(_, s) => s.get(),
            StructInfo::Unnamed(_, m) => Rc::new(m.clone()),
        }
    }
    pub fn member_offset(&self, member_to_find: &str) -> usize {
        self.members()
            .iter()
            .take_while(|(_, name)| name.unwrap_string() != member_to_find)
            .fold(0, |acc, (t, _)| acc + t.size())
    }
    pub fn member_type(&self, member_to_find: &str) -> Type {
        self.members()
            .iter()
            .find(|(_, name)| name.unwrap_string() == member_to_find)
            .unwrap()
            .0
            .clone()
    }
    fn name(&self) -> String {
        match self {
            StructInfo::Named(name, _) => name.to_string(),
            StructInfo::Unnamed(token, _) => format!(
                "(<unnamed> at {}:{}:{})",
                token.filename.display(),
                token.line_index,
                token.column
            ),
        }
    }
    pub fn is_complete(&self) -> bool {
        match self {
            Self::Named(_, s) => s.is_complete(),
            Self::Unnamed(..) => true,
        }
    }
}

mod struct_ref {
    use super::Token;
    use super::TokenKind;
    use super::Type;
    use std::cell::RefCell;
    use std::rc::Rc;

    type IsComplete = bool;
    type InDefinition = bool;

    thread_local! {
        static CUSTOMS: RefCell<Vec<Rc<Vec<(Type, Token)>>>> = Default::default();
        static CUSTOMS_INFO: RefCell<Vec<(IsComplete,InDefinition)>> = Default::default();
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct StructRef {
        index: usize,
        kind: TokenKind,
    }

    impl StructRef {
        pub fn new(kind: TokenKind, is_definition: bool) -> StructRef {
            CUSTOMS_INFO.with(|list| {
                list.borrow_mut().push((false, is_definition));
            });
            CUSTOMS.with(|list| {
                let mut types = list.borrow_mut();
                let index = types.len();
                types.push(Rc::new(vec![]));

                StructRef { index, kind }
            })
        }
        pub fn get_kind(&self) -> &TokenKind {
            &self.kind
        }

        pub fn get(&self) -> Rc<Vec<(Type, Token)>> {
            CUSTOMS.with(|list| list.borrow()[self.index].clone())
        }
        pub fn update(&self, members: Vec<(Type, Token)>) {
            CUSTOMS_INFO.with(|list| {
                let mut types = list.borrow_mut();
                types[self.index].0 = true;
            });
            CUSTOMS_INFO.with(|list| {
                let mut types = list.borrow_mut();
                types[self.index].1 = false;
            });
            CUSTOMS.with(|list| {
                let mut types = list.borrow_mut();
                types[self.index] = members.into();
            });
        }
        pub fn is_complete(&self) -> bool {
            CUSTOMS_INFO.with(|list| list.borrow()[self.index].0)
        }
        pub fn in_definition(&self) -> bool {
            CUSTOMS_INFO.with(|list| list.borrow()[self.index].1)
        }

        pub fn being_defined(&self) {
            CUSTOMS_INFO.with(|list| list.borrow_mut()[self.index].1 = true)
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn suffix_exists(modifiers: &[&Type], i: usize) -> bool {
            modifiers
                .iter()
                .skip(i)
                .any(|m| matches!(m, Type::Array { .. } | Type::Function { .. }))
        }
        fn closing_precedence(modifiers: &[&Type], i: usize) -> &'static str {
            if matches!(modifiers.get(i + 1), Some(Type::Pointer(_))) && suffix_exists(modifiers, i + 1)
            {
                ")"
            } else {
                ""
            }
        }

        fn print_type(type_decl: &Type) -> String {
            let mut current = type_decl;
            let mut modifiers = Vec::new();

            while let Type::Pointer(new)
            | Type::Array(new, _)
            | Type::Function(FuncType { return_type: new, .. }) = current
            {
                modifiers.push(current);
                current = new;
            }

            let mut result = match current {
                Type::Primitive(t) => t.fmt().to_string(),
                Type::Union(s) => "union ".to_string() + &s.name(),
                Type::Struct(s) => "struct ".to_string() + &s.name(),
                Type::Enum(Some(name), ..) => "enum ".to_string() + name,
                Type::Enum(None, ..) => "enum <unnamed>".to_string(),
                _ => unreachable!("all modifiers were removed"),
            };
            if !modifiers.is_empty() {
                result.push(' ');
            }
            let mut pointers = Vec::new();
            let mut suffixes = Vec::new();

            for (i, modifier) in modifiers.iter().enumerate() {
                match modifier {
                    Type::Array(_, size) => suffixes.push(format!(
                        "[{}]{}",
                        match size {
                            ArraySize::Known(size) => size.to_string(),
                            ArraySize::Unknown => String::new(),
                        },
                        closing_precedence(&modifiers, i)
                    )),
                    Type::Pointer(_) => {
                        let precedence = matches!(
                            modifiers.get(i + 1),
                            Some(Type::Array { .. } | Type::Function { .. })
                        );
                        pointers.push(match precedence {
                            true if pointers.is_empty() && suffixes.is_empty() => "(*)",
                            true => "(*",
                            false
                                if suffixes.is_empty()
                                    && suffix_exists(&modifiers, i)
                                    && pointers.is_empty() =>
                            {
                                "*)"
                            }
                            _ => "*",
                        });
                    }
                    Type::Function(FuncType { params, variadic, .. }) => suffixes.push(format!(
                        "({}{}){}",
                        params
                            .iter()
                            .map(|ty| ty.to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                        if *variadic { ", ..." } else { "" },
                        closing_precedence(&modifiers, i)
                    )),
                    _ => unreachable!("not modifier"),
                }
            }
            for s in pointers.iter().rev() {
                result.push_str(s);
            }
            for s in suffixes {
                result.push_str(&s);
            }

            result
        }
        write!(f, "{}", print_type(self))
    }
}

#[cfg(test)]
pub mod tests {

    #[macro_export]
    macro_rules! setup_type {
        ($input:expr) => {
            if let Ok(ty) = crate::compiler::parser::tests::setup($input).type_name() {
                if let Ok(actual_ty) = crate::compiler::typechecker::TypeChecker::new().parse_type(
                    &crate::compiler::common::token::Token::default(
                        crate::compiler::common::token::TokenKind::Semicolon,
                    ),
                    ty,
                ) {
                    actual_ty
                } else {
                    unreachable!("not type declaration")
                }
            } else {
                unreachable!("not type declaration")
            }
        };
        // if type depends on an already existing environment, supply said environment
        ($input:expr,$typechecker:expr) => {
            if let Ok(ty) = crate::compiler::parser::tests::setup($input).type_name() {
                if let Ok(actual_ty) = $typechecker.parse_type(&Token::default(TokenKind::Semicolon), ty)
                {
                    actual_ty
                } else {
                    unreachable!("not type declaration")
                }
            } else {
                unreachable!("not type declaration")
            }
        };
    }
    fn assert_type_print(input: &str, expected: &str) {
        let type_string = setup_type!(input);
        assert_eq!(type_string.to_string(), expected);
    }

    #[test]
    fn multi_dim_arr_print() {
        assert_type_print("int [4][2]", "int [4][2]");
        assert_type_print("int ([3])[4][2]", "int [3][4][2]");

        assert_type_print("long int *[3][4][2]", "long *[3][4][2]");
        assert_type_print("char ***[2]", "char ***[2]");

        assert_type_print("char *((*))[2]", "char *(*)[2]");
        assert_type_print("char *(**)[2]", "char *(**)[2]");
        assert_type_print("char *(**)", "char ***");

        assert_type_print("char *(*)[3][4][2]", "char *(*)[3][4][2]");
        assert_type_print("short (**[3][4])[2]", "short (**[3][4])[2]");
        assert_type_print("char (**(*)[4])[2]", "char (**(*)[4])[2]");
        assert_type_print("char(**(*[3])[4])[2]", "char (**(*[3])[4])[2]");

        assert_type_print("char (*(*[3]))[2]", "char (**[3])[2]");
    }
    #[test]
    fn function_type_print() {
        assert_type_print("int ()", "int ()"); // should this rather be `int (int)`?
        assert_type_print("int (int)", "int (int)");
        assert_type_print("int (int ())", "int (int (*)())");

        assert_type_print("int ((()))", "int (int (*)(int (*)()))");
        assert_type_print("int (char[2])", "int (char *)");

        assert_type_print("void *(*(int[2], char (void)))", "void **(int *, char (*)())");
        assert_type_print("int (*(void))[3]", "int (*())[3]");
        assert_type_print(
            "int (**(int[2], char(void)))[3];",
            "int (**(int *, char (*)()))[3]",
        );

        assert_type_print("short *(short int**, ...)", "short *(short **, ...)");
    }
}
