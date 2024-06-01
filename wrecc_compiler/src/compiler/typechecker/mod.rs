//! Converts [HIR-parsetree](hir) to type-annotated [MIR-ast](mir) and checks for semantic errors

pub mod fold;
pub mod init;
pub mod mir;

use crate::compiler::codegen::align;
use crate::compiler::codegen::register::*;
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::parser::hir;
use crate::compiler::parser::hir::decl::SpecifierKind;

use self::init::*;
use self::mir::decl::{CaseKind, ScopeKind};
use self::mir::expr::{CastDirection, ValueKind};
use crate::find_scope;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

pub type ConstLabels = HashMap<String, usize>;

pub struct TypeChecker {
    // symbol table to store all tags and symbols
    env: Environment,

    // label with its associated label index
    const_labels: ConstLabels,

    // label index counter
    const_label_count: usize,
}

impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            env: Environment::new(),
            const_labels: HashMap::new(),
            const_label_count: 0,
        }
    }
    pub fn check(
        mut self,
        external_decls: Vec<hir::decl::ExternalDeclaration>,
    ) -> Result<(Vec<mir::decl::ExternalDeclaration>, ConstLabels), Vec<Error>> {
        match self.check_declarations(external_decls) {
            Ok(mir) => Ok((mir, self.const_labels)),
            Err(e) => Err(e.flatten_multiple()),
        }
    }
    fn check_declarations(
        &mut self,
        external_decls: Vec<hir::decl::ExternalDeclaration>,
    ) -> Result<Vec<mir::decl::ExternalDeclaration>, Error> {
        let mut mir_decls = Vec::new();
        let mut errors = Vec::new();

        for decl in external_decls {
            match self.visit_decl(decl) {
                Ok(mir_decl) => mir_decls.push(mir_decl),
                Err(e) => errors.push(e),
            }
        }

        if let Err(mut incomplete_declarations) = self.env.check_remaining_tentatives() {
            // TODO: maybe only emit error if that token didn't already emit an
            // IncompleteType error before
            errors.append(&mut incomplete_declarations);
        }

        if errors.is_empty() {
            Ok(mir_decls)
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    fn visit_decl(
        &mut self,
        external_decl: hir::decl::ExternalDeclaration,
    ) -> Result<mir::decl::ExternalDeclaration, Error> {
        match external_decl {
            hir::decl::ExternalDeclaration::Declaration(decl) => self
                .declaration(decl, None)
                .map(mir::decl::ExternalDeclaration::Declaration),
            hir::decl::ExternalDeclaration::Function(func_decl, body) => {
                self.function_definition(func_decl, body)
            }
        }
    }

    fn declaration(
        &mut self,
        decl: hir::decl::Declaration,
        mut func: Option<&mut mir::decl::Function>,
    ) -> Result<Vec<mir::decl::Declarator>, Error> {
        let mut declarators = Vec::new();

        let storage_class = self.parse_storage_classes(&decl.decl_specs.storage_classes)?;
        let qtype = self.parse_specifiers(decl.decl_specs.specifiers)?;
        let qtype = Self::parse_qualifiers(qtype, &decl.decl_specs.qualifiers)?;

        for declarator in decl.declarators {
            if let Some(d) = self.declarator(
                qtype.clone(),
                storage_class.clone(),
                decl.decl_specs.is_inline,
                declarator,
                &mut func,
            )? {
                declarators.push(d);
            }
        }

        Ok(declarators)
    }
    fn declarator(
        &mut self,
        qtype: QualType,
        storage_class: Option<mir::decl::StorageClass>,
        is_inline: bool,
        (declarator, init): (hir::decl::Declarator, Option<hir::decl::Init>),
        func: &mut Option<&mut mir::decl::Function>,
    ) -> Result<Option<mir::decl::Declarator>, Error> {
        let qtype = self.parse_modifiers(qtype, declarator.modifiers)?;

        if let Some(name) = declarator.name {
            if !qtype.ty.is_func() && is_inline {
                return Err(Error::new(
                    &name,
                    ErrorKind::Regular("'inline' can only appear on functions"),
                ));
            }
            if let Type::Function(func_type) = &qtype.ty {
                if name.unwrap_string() == "main" {
                    func_type.check_main_signature(&name, is_inline)?;
                }
            }

            match storage_class {
                Some(sc @ (mir::decl::StorageClass::Register | mir::decl::StorageClass::Auto))
                    if self.env.is_global() || qtype.ty.is_func() =>
                {
                    return Err(Error::new(
                        &name,
                        ErrorKind::InvalidStorageClass(
                            sc,
                            if qtype.ty.is_func() {
                                "function"
                            } else {
                                "global variable"
                            },
                        ),
                    ));
                }
                Some(mir::decl::StorageClass::Extern) if init.is_some() => {
                    return Err(Error::new(
                        &name,
                        ErrorKind::Regular("variable declared with 'extern' cannot have initializer"),
                    ))
                }
                Some(mir::decl::StorageClass::Static) if !self.env.is_global() && qtype.ty.is_func() => {
                    return Err(Error::new(
                        &name,
                        ErrorKind::Regular(
                            "function declared in block scope cannot have 'static' storage-class",
                        ),
                    ))
                }
                Some(mir::decl::StorageClass::TypeDef) if is_inline => {
                    return Err(Error::new(
                        &name,
                        ErrorKind::Regular("'inline' not allowed with 'typedef' storage-class"),
                    ))
                }

                _ => (),
            }

            let symbol = Symbol {
                storage_class,
                kind: if init.is_some() {
                    InitType::Definition
                } else {
                    InitType::Declaration
                },
                reg: None,
                token: name.clone(),
                qtype: qtype.clone(),
            };

            let entry = self.env.declare_symbol(&name, symbol)?;
            let is_typedef = entry.borrow().is_typedef();

            if (is_typedef || qtype.ty.is_func()) && init.is_some() {
                return Err(Error::new(
                    &name,
                    ErrorKind::Regular("only variables can be initialized"),
                ));
            }

            if is_typedef {
                return Ok(None);
            }

            let mut symbol_type = entry.borrow().qtype.clone();

            let init = if let Some(init) = init {
                if !symbol_type.ty.is_unbounded_array() && !symbol_type.ty.is_complete() {
                    return Err(Error::new(&name, ErrorKind::IncompleteType(symbol_type.clone())));
                }
                let init = self.init_check(func, &mut symbol_type, init, entry.borrow().is_static())?;

                // update symbol type if was unbounded array
                if let ty @ Type::Array(_, ArraySize::Unknown) = &mut entry.borrow_mut().qtype.ty {
                    *ty = symbol_type.clone().ty;
                }

                Some(init)
            } else {
                let tentative_decl = self.env.is_global() && symbol_type.ty.is_aggregate();
                if !symbol_type.ty.is_complete() && !tentative_decl && !entry.borrow().is_extern() {
                    return Err(Error::new(&name, ErrorKind::IncompleteType(symbol_type)));
                }
                None
            };

            if let Some(func) = func {
                func.increment_stack_size(&entry);
            }

            Ok(Some(mir::decl::Declarator {
                name,
                init,
                entry: Rc::clone(&entry),
            }))
        } else {
            Ok(None)
        }
    }

    pub fn parse_type(
        &mut self,
        token: &Token,
        decl_type: hir::decl::DeclType,
    ) -> Result<QualType, Error> {
        let qtype = self.parse_specifiers(decl_type.specifiers)?;
        let qtype = Self::parse_qualifiers(qtype, &decl_type.qualifiers)?;
        let qtype = self.parse_modifiers(qtype, decl_type.modifiers)?;

        if !qtype.ty.is_void() && !qtype.ty.is_complete() {
            return Err(Error::new(token, ErrorKind::IncompleteType(qtype)));
        }

        Ok(qtype)
    }
    fn parse_specifiers(&mut self, specifiers: Vec<hir::decl::Specifier>) -> Result<QualType, Error> {
        let ty = if specifiers.is_empty() {
            // WARN: since C99 this should at least issue a warning
            // problem: requires token so should probably already error in parser
            Type::Primitive(Primitive::Int(false))
        } else {
            let token = specifiers[0].token.clone();

            let mut specifier_kind_list: Vec<hir::decl::SpecifierKind> =
                specifiers.into_iter().map(|spec| spec.kind).collect();

            specifier_kind_list.sort_by_key(|spec| spec.order());

            // specifier combinations according to 6.7.2.2
            match specifier_kind_list.as_slice() {
                [hir::decl::SpecifierKind::Struct(name, members)]
                | [hir::decl::SpecifierKind::Union(name, members)] => {
                    self.struct_or_union_specifier(token, name, members)?
                }
                [hir::decl::SpecifierKind::Enum(name, enum_constants)] => {
                    self.enum_specifier(token, name, enum_constants)?
                }
                [hir::decl::SpecifierKind::UserType] => {
                    return self.env.get_symbol(&token).and_then(|symbol| {
                        if symbol.borrow().is_typedef() {
                            Ok(symbol.borrow().qtype.clone())
                        } else {
                            Err(Error::new(
                                &token,
                                ErrorKind::InvalidSymbol(token.unwrap_string(), "user-type"),
                            ))
                        }
                    })
                }

                // void
                [SpecifierKind::Void] => Type::Primitive(Primitive::Void),
                // char, signed char
                [SpecifierKind::Char] | [SpecifierKind::Signed, SpecifierKind::Char] => {
                    Type::Primitive(Primitive::Char(false))
                }
                // unsigned char
                [SpecifierKind::Unsigned, SpecifierKind::Char] => Type::Primitive(Primitive::Char(true)),
                // short, signed short, short int, signed short int
                [SpecifierKind::Short]
                | [SpecifierKind::Signed, SpecifierKind::Short]
                | [SpecifierKind::Short, SpecifierKind::Int]
                | [SpecifierKind::Signed, SpecifierKind::Short, SpecifierKind::Int] => {
                    Type::Primitive(Primitive::Short(false))
                }
                // unsigned short, unsigned short int
                [SpecifierKind::Unsigned, SpecifierKind::Short]
                | [SpecifierKind::Unsigned, SpecifierKind::Short, SpecifierKind::Int] => {
                    Type::Primitive(Primitive::Short(true))
                }
                // int, signed, signed int
                [SpecifierKind::Int]
                | [SpecifierKind::Signed]
                | [SpecifierKind::Signed, SpecifierKind::Int] => Type::Primitive(Primitive::Int(false)),
                // unsigned, unsigned int
                [SpecifierKind::Unsigned] | [SpecifierKind::Unsigned, SpecifierKind::Int] => {
                    Type::Primitive(Primitive::Int(true))
                }
                // long, signed long, long int, signed long int
                // long long, signed long long, long long int, signed long long int
                [SpecifierKind::Long]
                | [SpecifierKind::Signed, SpecifierKind::Long]
                | [SpecifierKind::Long, SpecifierKind::Int]
                | [SpecifierKind::Signed, SpecifierKind::Long, SpecifierKind::Int]
                | [SpecifierKind::Long, SpecifierKind::Long]
                | [SpecifierKind::Signed, SpecifierKind::Long, SpecifierKind::Long]
                | [SpecifierKind::Long, SpecifierKind::Long, SpecifierKind::Int]
                | [SpecifierKind::Signed, SpecifierKind::Long, SpecifierKind::Long, SpecifierKind::Int] => {
                    Type::Primitive(Primitive::Long(false))
                }
                // unsigned long, unsigned long int
                // unsigned long long, unsigned long long int
                [SpecifierKind::Unsigned, SpecifierKind::Long]
                | [SpecifierKind::Unsigned, SpecifierKind::Long, SpecifierKind::Int]
                | [SpecifierKind::Unsigned, SpecifierKind::Long, SpecifierKind::Long]
                | [SpecifierKind::Unsigned, SpecifierKind::Long, SpecifierKind::Long, SpecifierKind::Int] => {
                    Type::Primitive(Primitive::Long(false))
                }
                _ => {
                    return Err(Error::new(
                        &token,
                        ErrorKind::Regular("invalid combination of type-specifiers"),
                    ))
                }
            }
        };

        Ok(QualType::new(ty))
    }
    fn parse_qualifiers(
        mut qtype: QualType,
        new_qualifiers: &Vec<hir::decl::Qualifier>,
    ) -> Result<QualType, Error> {
        if let Some(qualifier) = new_qualifiers
            .iter()
            .find(|q| q.kind == hir::decl::QualifierKind::Restrict)
        {
            match &qtype.ty {
                Type::Pointer(to) if !to.ty.is_func() => (),
                _ => return Err(Error::new(&qualifier.token, ErrorKind::InvalidRestrict(qtype))),
            }
        }

        // if an aggregate type has const or volatile qualifiers then the same qualifiers apply to its element-type
        if new_qualifiers.iter().any(|q| {
            q.kind == hir::decl::QualifierKind::Const || q.kind == hir::decl::QualifierKind::Volatile
        }) {
            match &mut qtype.ty {
                Type::Array(of, _) => {
                    *of = Box::new(Self::parse_qualifiers(*of.clone(), new_qualifiers)?);
                }
                Type::Struct(s) | Type::Union(s) => {
                    let old_members = s.members();
                    let mut new_qualified_members = Vec::new();

                    for (old_qtype, old_token) in old_members.iter() {
                        let new_qualified_type =
                            Self::parse_qualifiers(old_qtype.clone(), new_qualifiers)?;
                        new_qualified_members.push((new_qualified_type, old_token.clone()));
                    }

                    match s {
                        StructKind::Named(_, struct_ref) => {
                            struct_ref.update_members(new_qualified_members)
                        }
                        StructKind::Unnamed(_, members) => *members = new_qualified_members,
                    }
                }
                _ => (),
            }
        }

        let new_qualifiers = Qualifiers::from(new_qualifiers);
        Ok(QualType {
            qualifiers: Qualifiers {
                is_const: new_qualifiers.is_const | qtype.qualifiers.is_const,
                is_restrict: new_qualifiers.is_restrict | qtype.qualifiers.is_restrict,
                is_volatile: new_qualifiers.is_volatile | qtype.qualifiers.is_volatile,
            },
            ..qtype
        })
    }

    fn parse_storage_classes(
        &mut self,
        storage_classes: &Vec<hir::decl::StorageClass>,
    ) -> Result<Option<mir::decl::StorageClass>, Error> {
        match storage_classes.as_slice() {
            [single] => Ok(Some(single.kind.clone().into())),
            [] => Ok(None),
            [_, sec, ..] => Err(Error::new(
                &sec.token,
                ErrorKind::Regular("cannot have multiple storage-classes"),
            )),
        }
    }
    fn parse_modifiers(
        &mut self,
        mut qtype: QualType,
        modifiers: Vec<hir::decl::DeclModifier>,
    ) -> Result<QualType, Error> {
        for m in modifiers {
            qtype = match m {
                hir::decl::DeclModifier::Pointer(qualifiers) => {
                    Self::parse_qualifiers(qtype.pointer_to(), &qualifiers)?
                }
                hir::decl::DeclModifier::Array(token, size) => {
                    if qtype.ty.is_func() || qtype.ty.is_unbounded_array() {
                        return Err(Error::new(&token, ErrorKind::InvalidArray(qtype)));
                    }

                    if let Some(expr) = size {
                        let literal = self
                            .visit_expr(&mut None, expr)?
                            .get_literal_constant(&token, "array size specifier")?;
                        let amount = literal
                            .try_i64()
                            .ok_or_else(|| Error::new(&token, ErrorKind::ArraySizeOverflow))?;

                        if amount > 0 {
                            if i64::overflowing_mul(qtype.ty.size() as i64, amount).1 {
                                return Err(Error::new(&token, ErrorKind::ArraySizeOverflow));
                            }
                            QualType::new(Type::Array(
                                Box::new(qtype),
                                ArraySize::Known(amount as usize),
                            ))
                        } else {
                            return Err(Error::new(&token, ErrorKind::InvalidArraySize));
                        }
                    } else {
                        QualType::new(Type::Array(Box::new(qtype), ArraySize::Unknown))
                    }
                }
                hir::decl::DeclModifier::Function { token, params, variadic } => {
                    // func-params have own scope (their types too)
                    self.env.enter();
                    let params = self
                        .parse_params(&token, params)?
                        .into_iter()
                        .map(|(qtype, _)| qtype)
                        .collect();
                    self.env.exit();

                    if qtype.ty.is_func() || qtype.ty.is_array() {
                        return Err(Error::new(&token, ErrorKind::InvalidReturnType(qtype)));
                    }

                    qtype.function_of(params, variadic)
                }
            };
        }

        Ok(qtype)
    }
    fn struct_or_union_specifier(
        &mut self,
        token: Token,
        name: &Option<Token>,
        members: &Option<Vec<hir::decl::MemberDecl>>,
    ) -> Result<Type, Error> {
        let members = match (&name, members) {
            (Some(name), Some(members)) => {
                let custom_type = self
                    .env
                    .declare_type(name, Tags::Aggregate(StructRef::new(token.clone().kind, true)))?;

                let members = self.struct_declaration(members.clone())?;

                if let Tags::Aggregate(struct_ref) = &*custom_type.borrow_mut() {
                    struct_ref.complete_def(members);
                }
                let members = custom_type.borrow().clone().unwrap_aggr();

                StructKind::Named(name.unwrap_string(), members)
            }

            (Some(name), None) => {
                let custom_type = self.env.get_type(name).or_else(|_| {
                    self.env
                        .declare_type(name, Tags::Aggregate(StructRef::new(token.clone().kind, false)))
                })?;

                if &token.kind != custom_type.borrow().get_kind() {
                    return Err(Error::new(
                        name,
                        ErrorKind::TypeAlreadyExists(name.unwrap_string(), token.kind.clone()),
                    ));
                }

                let members = custom_type.borrow().clone().unwrap_aggr();

                StructKind::Named(name.unwrap_string(), members)
            }
            (None, Some(members)) => {
                let members = self.struct_declaration(members.clone())?;
                StructKind::Unnamed(token.clone(), members)
            }
            (None, None) => {
                return Err(Error::new(&token, ErrorKind::EmptyAggregate(token.kind.clone())));
            }
        };

        Ok(match token.kind {
            TokenKind::Struct => Type::Struct(members),
            TokenKind::Union => Type::Union(members),
            _ => unreachable!("not struct/union specifier"),
        })
    }
    fn struct_declaration(
        &mut self,
        members: Vec<hir::decl::MemberDecl>,
    ) -> Result<Vec<(QualType, Token)>, Error> {
        let mut parsed_members = Vec::new();

        for member in members {
            let qtype = self.parse_specifiers(member.specifiers)?;
            let qtype = Self::parse_qualifiers(qtype, &member.qualifiers)?;

            for hir::decl::MemberDeclarator { name, modifiers } in member.declarators {
                let parsed_type = self.parse_modifiers(qtype.clone(), modifiers)?;

                if !parsed_type.ty.is_complete() {
                    return Err(Error::new(&name, ErrorKind::IncompleteType(parsed_type)));
                }
                if parsed_type.ty.is_func() {
                    return Err(Error::new(
                        &name,
                        ErrorKind::FunctionMember(name.unwrap_string(), parsed_type),
                    ));
                }

                parsed_members.push((parsed_type, name));
            }
        }

        Self::check_duplicate_members(&parsed_members)?;

        Ok(parsed_members)
    }
    fn check_duplicate_members(vec: &[(QualType, Token)]) -> Result<(), Error> {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        for token in vec.iter().map(|(_, name)| name) {
            if !set.insert(token.unwrap_string()) {
                return Err(Error::new(
                    token,
                    ErrorKind::DuplicateMember(token.unwrap_string()),
                ));
            }
        }
        Ok(())
    }

    fn enum_specifier(
        &mut self,
        token: Token,
        name: &Option<Token>,
        constants: &Option<Vec<(Token, Option<hir::expr::ExprKind>)>>,
    ) -> Result<Type, Error> {
        match (&name, constants) {
            (Some(name), Some(values)) => {
                let members = self.enumerator_list(values.clone())?;
                self.env.declare_type(name, Tags::Enum(members.clone()))?;

                Ok(Type::Enum(Some(name.unwrap_string()), members))
            }
            (Some(name), None) => {
                let custom_type = self
                    .env
                    .get_type(name)
                    .map_err(|_| Error::new(name, ErrorKind::EnumForwardDecl))?;

                if &token.kind != custom_type.borrow().get_kind() {
                    return Err(Error::new(
                        name,
                        ErrorKind::TypeAlreadyExists(name.unwrap_string(), token.kind.clone()),
                    ));
                }
                let constants = custom_type.borrow().clone().unwrap_enum();

                Ok(Type::Enum(Some(name.unwrap_string()), constants))
            }
            (None, Some(values)) => Ok(Type::Enum(None, self.enumerator_list(values.clone())?)),
            (None, None) => Err(Error::new(&token, ErrorKind::EmptyAggregate(token.kind.clone()))),
        }
    }
    fn enumerator_list(
        &mut self,
        constants: Vec<(Token, Option<hir::expr::ExprKind>)>,
    ) -> Result<Vec<(Token, i32)>, Error> {
        let mut parsed_constants = Vec::new();
        // 6.7.2.2 The expression that defines the value of an enumeration constant shall be an integer
        // constant expression that has a value representable as an `int`
        let mut index: i32 = 0;
        let mut constants = constants.into_iter().peekable();

        while let Some((name, init)) = constants.next() {
            if let Some(init_expr) = init {
                let literal = self
                    .visit_expr(&mut None, init_expr)?
                    .get_literal_constant(&name, "enum Constant")?;
                if literal.type_overflow(&Type::Primitive(Primitive::Int(false))) {
                    return Err(Error::new(&name, ErrorKind::EnumOverflow));
                }
                index = literal.try_i64().expect("just checked for int type-overflow") as i32;
            }

            // insert enum constant into symbol table
            self.env.declare_symbol(
                &name,
                Symbol {
                    storage_class: None,
                    token: name.clone(),
                    qtype: QualType::new(Type::Primitive(Primitive::Int(false))),
                    kind: InitType::Definition,
                    reg: Some(Register::Literal(
                        LiteralKind::Signed(index as i64),
                        Type::Primitive(Primitive::Int(false)),
                    )),
                },
            )?;

            parsed_constants.push((name.clone(), index));

            if let Some(inc) = index.checked_add(1) {
                index = inc;
            } else {
                if let Some((next_tok, None)) = constants.peek() {
                    return Err(Error::new(next_tok, ErrorKind::EnumOverflow));
                }
            }
        }

        Ok(parsed_constants)
    }
    fn parse_params(
        &mut self,
        token: &Token,
        params: Vec<hir::decl::ParamDecl>,
    ) -> Result<Vec<(QualType, Option<(Token, SymbolRef)>)>, Error> {
        let mut parsed_params = Vec::new();

        for param in params {
            let storage_class = self.parse_storage_classes(&param.decl_specs.storage_classes)?;
            let qtype = self.parse_specifiers(param.decl_specs.specifiers.clone())?;
            let qtype = Self::parse_qualifiers(qtype, &param.decl_specs.qualifiers)?;
            let mut qtype = self.parse_modifiers(qtype, param.declarator.modifiers)?;

            let token_name = if let Some(name) = &param.declarator.name {
                name
            } else {
                token
            };

            if param.decl_specs.is_inline {
                return Err(Error::new(
                    token_name,
                    ErrorKind::Regular("cannot have 'inline' on function parameters"),
                ));
            }

            let storage_class = match storage_class {
                Some(sc @ mir::decl::StorageClass::Register) => Some(sc),
                Some(sc) => {
                    return Err(Error::new(
                        token_name,
                        ErrorKind::InvalidStorageClass(sc, "function-parameter"),
                    ));
                }
                None => None,
            };

            qtype = match qtype.ty {
                Type::Array(of, _) => of.pointer_to(),
                Type::Function { .. } => qtype.pointer_to(),
                _ => qtype,
            };

            let name = if let Some(name) = param.declarator.name {
                let symbol = self.env.declare_symbol(
                    &name,
                    Symbol {
                        storage_class,
                        token: name.clone(),
                        qtype: qtype.clone(),
                        kind: InitType::Declaration,
                        reg: None,
                    },
                )?;

                Some((name, symbol))
            } else {
                None
            };

            parsed_params.push((qtype, name));
        }

        // single unnamed void param is equivalent to empty params
        if let [(
            QualType {
                ty: Type::Primitive(Primitive::Void),
                qualifiers,
            },
            None,
        )] = parsed_params.as_slice()
        {
            if !qualifiers.is_empty() {
                return Err(Error::new(
                    token,
                    ErrorKind::Regular("'void' parameter cannot have type-qualifiers"),
                ));
            }
            parsed_params.pop();
        } else if parsed_params.iter().any(|(qtype, _)| qtype.ty.is_void()) {
            return Err(Error::new(token, ErrorKind::VoidFuncArg));
        }

        Ok(parsed_params)
    }

    fn init_check(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        qtype: &mut QualType,
        mut init: hir::decl::Init,
        is_static: bool,
    ) -> Result<mir::decl::Init, Error> {
        if let Some((string, size)) = Self::is_string_init(qtype, &init)? {
            init.kind = Self::char_array(init.token.clone(), string, size)?;
        }

        match init.kind {
            hir::decl::InitKind::Scalar(expr) => {
                self.init_scalar(func, qtype, &init.token, expr, is_static)
            }
            hir::decl::InitKind::Aggr(list) => {
                self.init_aggregate(func, qtype, init.token, list, is_static)
            }
        }
    }
    fn init_scalar(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        qtype: &QualType,
        token: &Token,
        expr: hir::expr::ExprKind,
        is_static: bool,
    ) -> Result<mir::decl::Init, Error> {
        if qtype.ty.is_array() {
            return Err(Error::new(token, ErrorKind::InvalidAggrInit(qtype.clone())));
        }

        let expr = self.visit_expr(func, expr)?.decay(token)?.to_rval();
        Self::check_type_compatibility(token, qtype, &expr)?;
        let expr = Self::maybe_cast(qtype.clone(), expr);

        let should_be_const = self.env.is_global() || is_static;
        if should_be_const && !expr.is_constant() {
            return Err(Error::new(
                token,
                ErrorKind::NotConstantInit(if is_static {
                    "static variables"
                } else {
                    "global variables"
                }),
            ));
        }

        Ok(mir::decl::Init::Scalar(expr))
    }
    fn init_aggregate(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        qtype: &mut QualType,
        token: Token,
        mut list: Vec<Box<hir::decl::Init>>,
        is_static: bool,
    ) -> Result<mir::decl::Init, Error> {
        match qtype.ty {
            Type::Array { .. } | Type::Struct(_) | Type::Union(_) => {
                let mut new_list = Vec::new();
                let mut objects = CurrentObjects::new(qtype.clone());
                let mut max_index: usize = 0;

                // INFO: int array[3] = {} is a gnu-extension
                if list.is_empty() {
                    return Err(Error::new(&token, ErrorKind::EmptyInit));
                }

                while !list.is_empty() {
                    let first = list.first_mut().unwrap();

                    if let Some(designator) = &mut first.designator {
                        objects.clear();

                        while let Some(d) = designator.pop_front() {
                            let designator_info = self.designator_index(objects.current_type(), d)?;
                            objects.update(designator_info);
                        }

                        first.designator = None;
                    } else {
                        let (i, _, current_type) = objects.current();
                        let sub_type = current_type.at(*i as usize).ok_or_else(|| {
                            Error::new(
                                &first.token,
                                ErrorKind::InitializerOverflow(current_type.clone()),
                            )
                        })?;
                        objects.0.push((0, 0, sub_type))
                    }

                    // handles cases when incompatible aggregate type with scalar:
                    //     struct {
                    //         struct {
                    //             int arr[3] a;
                    //         } s;
                    //     } = {1};
                    //     => pushes 'struct s' and 'int[3]' to current objects and initializes 1 to int
                    // or when aggregate is initialized with scalar of aggregate type
                    //     struct X foo;
                    //     struct {
                    //         int a;
                    //         struct X s;
                    //     } = {.s = foo};
                    let mut sub_qtype = objects.current_type();
                    if let hir::decl::InitKind::Scalar(expr) = first.kind.clone() {
                        // placeholder expression
                        let left = mir::expr::Expr {
                            kind: mir::expr::ExprKind::Nop,
                            qtype: sub_qtype.clone(),
                            value_kind: ValueKind::Lvalue,
                        };
                        let right = self.visit_expr(func, expr)?;

                        while !sub_qtype.ty.is_scalar()
                            && Self::is_string_init(sub_qtype, first)?.is_none()
                            && self.assign(left.clone(), token.clone(), right.clone()).is_err()
                        {
                            let new_sub_type = objects.current_type().at(0).unwrap();
                            objects.0.push((0, 0, new_sub_type));

                            sub_qtype = objects.current_type();
                        }
                    }

                    let init = self.init_check(func, sub_qtype, *list.remove(0), is_static)?;
                    let sub_type_size = sub_qtype.ty.size() as i64;
                    let init_offset = objects.offset();

                    // remove overriding elements
                    let init_interval = if let Some((offset, size)) = objects.find_same_union(&new_list)
                    {
                        offset..offset + size as i64
                    } else {
                        init_offset..init_offset + sub_type_size
                    };
                    new_list.retain(|(.., offset)| !init_interval.contains(offset));

                    // push init elements into new_list
                    match init {
                        mir::decl::Init::Aggr(list) => {
                            for (expr, offset) in list {
                                new_list.push((objects.clone(), expr, init_offset + offset as i64))
                            }
                        }
                        mir::decl::Init::Scalar(expr) => {
                            new_list.push((objects.clone(), expr, init_offset))
                        }
                    }

                    // pop off sub-type
                    objects.0.pop();

                    max_index = std::cmp::max(
                        max_index,
                        objects.0.first().map(|(i, ..)| *i as usize).unwrap_or(0),
                    );

                    objects.update_current();
                }

                // set size of unbounded array to biggest designator index
                if let Type::Array(_, size @ ArraySize::Unknown) = &mut qtype.ty {
                    *size = ArraySize::Known(max_index + 1);
                }

                new_list.sort_by(|(.., offset1), (.., offset2)| offset1.cmp(offset2));
                Ok(mir::decl::Init::Aggr(
                    new_list
                        .into_iter()
                        .map(|(_, expr, offset)| (expr, offset as usize))
                        .collect(),
                ))
            }
            _ => match list.as_slice() {
                [single_init] if matches!(single_init.kind, hir::decl::InitKind::Scalar(_)) => {
                    self.init_check(func, qtype, *single_init.clone(), is_static)
                }
                [single_init] => Err(Error::new(
                    &single_init.token,
                    ErrorKind::Regular("too many braces around scalar initializer"),
                )),
                [_, second_init, ..] => Err(Error::new(&second_init.token, ErrorKind::ScalarOverflow)),
                [] => Err(Error::new(
                    &token,
                    ErrorKind::Regular("scalar initializer cannot be empty"),
                )),
            },
        }
    }

    fn designator_index(
        &mut self,
        qtype: &QualType,
        designator: hir::decl::Designator,
    ) -> Result<(i64, i64, QualType), Error> {
        match (designator.kind, &qtype.ty) {
            (hir::decl::DesignatorKind::Array(expr), Type::Array(of, size)) => {
                let literal = self
                    .visit_expr(&mut None, expr)?
                    .get_literal_constant(&designator.token, "array designator")?;
                let index = literal
                    .try_i64()
                    .ok_or_else(|| Error::new(&designator.token, ErrorKind::ArraySizeOverflow))?;

                if index < 0 {
                    return Err(Error::new(
                        &designator.token,
                        ErrorKind::Regular("array designator must be positive number"),
                    ));
                }

                match size {
                    ArraySize::Known(amount) if index as usize >= *amount => Err(Error::new(
                        &designator.token,
                        ErrorKind::DesignatorOverflow(*amount, index),
                    )),
                    _ => Ok((index, index, *of.clone())),
                }
            }
            (hir::decl::DesignatorKind::Member(_), Type::Array { .. }) => Err(Error::new(
                &designator.token,
                ErrorKind::Regular(
                    "can only use member designator on type 'struct' and 'union' not 'array'",
                ),
            )),

            (hir::decl::DesignatorKind::Array(_), Type::Struct(_) | Type::Union(_)) => Err(Error::new(
                &designator.token,
                ErrorKind::InvalidArrayDesignator(qtype.clone()),
            )),
            (hir::decl::DesignatorKind::Member(m), Type::Struct(s) | Type::Union(s)) => {
                if let Some(index) = s
                    .members()
                    .iter()
                    .position(|(_, m_token)| *m == m_token.unwrap_string())
                {
                    // unions only have single index
                    if let Type::Union(_) = qtype.ty {
                        Ok((0, index as i64, s.member_type(&m)))
                    } else {
                        Ok((index as i64, index as i64, s.member_type(&m)))
                    }
                } else {
                    Err(Error::new(
                        &designator.token,
                        ErrorKind::NonExistantMember(m.clone(), qtype.clone()),
                    ))
                }
            }

            (..) => Err(Error::new(
                &designator.token,
                ErrorKind::NonAggregateDesignator(qtype.clone()),
            )),
        }
    }
    // detects if char-array is initialized with a string
    // both valid:
    // - char arr[4] = "foo";
    // - char arr[4] = {"foo"};
    fn is_string_init<'a>(
        qtype: &'a QualType,
        init: &hir::decl::Init,
    ) -> Result<Option<(String, &'a ArraySize)>, Error> {
        if let Some(size) = qtype.ty.is_char_array() {
            match &init.kind {
                hir::decl::InitKind::Scalar(hir::expr::ExprKind::String(s)) => {
                    return Ok(Some((s.unwrap_string(), size)))
                }
                hir::decl::InitKind::Aggr(list) => match list.as_slice() {
                    [single_init] if single_init.designator.is_none() => {
                        if let hir::decl::InitKind::Scalar(hir::expr::ExprKind::String(s)) =
                            &single_init.kind
                        {
                            return Ok(Some((s.unwrap_string(), size)));
                        }
                    }
                    [first_init, second_init] if first_init.designator.is_none() => {
                        if let hir::decl::InitKind::Scalar(hir::expr::ExprKind::String(_)) =
                            &first_init.kind
                        {
                            return Err(Error::new(
                                &second_init.token,
                                ErrorKind::Regular("excess elements in char array initializer"),
                            ));
                        }
                    }
                    _ => (),
                },
                _ => (),
            }
        }
        Ok(None)
    }
    // char s[] = "abc" identical to char s[] = {'a','b','c','\0'} (6.7.8)
    fn char_array(token: Token, mut s: String, size: &ArraySize) -> Result<hir::decl::InitKind, Error> {
        match size {
            ArraySize::Known(size) if *size < s.len() => {
                return Err(Error::new(
                    &token,
                    ErrorKind::TooLong("initializer-string", *size, s.len()),
                ));
            }
            // append implicit NULL terminator to string
            ArraySize::Known(size) if *size > s.len() => {
                s.push('\0');
            }
            ArraySize::Unknown => {
                s.push('\0');
            }
            _ => (),
        }

        Ok(hir::decl::InitKind::Aggr(
            s.as_bytes()
                .iter()
                .map(|c| {
                    Box::new(hir::decl::Init {
                        token: token.clone(),
                        kind: hir::decl::InitKind::Scalar(hir::expr::ExprKind::Char(*c as char)),
                        designator: None,
                    })
                })
                .collect(),
        ))
    }

    fn function_definition(
        &mut self,
        mut func_decl: hir::decl::FuncDecl,
        body: Vec<hir::stmt::Stmt>,
    ) -> Result<mir::decl::ExternalDeclaration, Error> {
        let name_string = func_decl.name.unwrap_string();

        // have to pop of last modifier first so that params can have other scope than return type
        let Some(hir::decl::DeclModifier::Function { params, variadic, token }) = func_decl.modifiers.pop() else {
            unreachable!("last modifier has to be function to be func-def");
        };

        let storage_class = self.parse_storage_classes(&func_decl.decl_specs.storage_classes)?;
        match storage_class {
            None | Some(mir::decl::StorageClass::Static) | Some(mir::decl::StorageClass::Extern) => (),
            Some(sc) => {
                return Err(Error::new(
                    &func_decl.name,
                    ErrorKind::InvalidStorageClass(sc, "function"),
                ));
            }
        }

        let return_type = self
            .parse_type(
                &func_decl.name,
                hir::decl::DeclType {
                    specifiers: func_decl.decl_specs.specifiers,
                    qualifiers: func_decl.decl_specs.qualifiers,
                    modifiers: func_decl.modifiers,
                },
            )
            .map_err(|mut err| {
                if let ErrorKind::IncompleteType(ty) = err.kind {
                    err.kind = ErrorKind::IncompleteReturnType(name_string.clone(), ty)
                }
                err
            })?;

        if return_type.ty.is_func() || return_type.ty.is_array() {
            return Err(Error::new(
                &func_decl.name,
                ErrorKind::InvalidReturnType(return_type),
            ));
        }

        // have to push scope before declaring local variables
        self.env.enter();

        let params = self.parse_params(&token, params)?;
        let func_type = FuncType {
            return_type: Box::new(return_type.clone()),
            params: params.iter().map(|(ty, _)| ty.clone()).collect(),
            variadic,
        };

        if name_string == "main" {
            func_type.check_main_signature(&func_decl.name, func_decl.decl_specs.is_inline)?;
        }

        let mut func = mir::decl::Function::new(
            name_string.clone(),
            return_type.clone(),
            variadic,
            func_decl.decl_specs.is_inline,
        );

        let symbol = self.env.declare_global(
            &func_decl.name,
            Symbol {
                storage_class,
                qtype: QualType::new(Type::Function(func_type)),
                kind: InitType::Definition,
                reg: None,
                token: func_decl.name.clone(),
            },
        )?;

        for (qtype, param_name) in params.into_iter() {
            if !qtype.ty.is_complete() {
                return Err(Error::new(
                    &func_decl.name,
                    ErrorKind::IncompleteFuncParam(name_string, qtype),
                ));
            }
            if let Some((_, var_symbol)) = param_name {
                func.increment_stack_size(&var_symbol);

                func.params.push(var_symbol);
            } else {
                return Err(Error::new(&func_decl.name, ErrorKind::UnnamedFuncParams));
            }
        }
        let mut errors = Vec::new();
        let mut func_body = Vec::new();

        match self.block(&mut func, body) {
            Ok(mir::stmt::Stmt::Block(stmts)) => func_body = stmts,
            Err(Error { kind: ErrorKind::Multiple(errs), .. }) => {
                errors = errs;
            }
            _ => unreachable!(),
        };

        if let Err(e) = func.compare_gotos() {
            errors.push(e);
        }

        func.implicit_main_return(&mut func_body);

        if errors.is_empty() {
            if !func.return_type.ty.is_void() && !func.returns_all_paths {
                return Err(Error::new(
                    &func_decl.name,
                    ErrorKind::NoReturnAllPaths(name_string),
                ));
            }
            func.returns_all_paths = false;

            Ok(mir::decl::ExternalDeclaration::Function(func, symbol, func_body))
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    fn visit_stmt(
        &mut self,
        func: &mut mir::decl::Function,
        statement: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        match statement {
            hir::stmt::Stmt::Declaration(decls) => self
                .declaration(decls, Some(func))
                .map(mir::stmt::Stmt::Declaration),
            hir::stmt::Stmt::Return(keyword, value) => self.return_statement(func, keyword, value),
            hir::stmt::Stmt::Expr(expr) => {
                Ok(mir::stmt::Stmt::Expr(self.visit_expr(&mut Some(func), expr)?))
            }
            hir::stmt::Stmt::Block(statements) => {
                self.env.enter();
                self.block(func, statements)
            }
            hir::stmt::Stmt::If(keyword, cond, then_branch, else_branch) => {
                self.if_statement(func, keyword, cond, *then_branch, else_branch)
            }
            hir::stmt::Stmt::While(left_paren, cond, body) => {
                self.while_statement(func, left_paren, cond, *body)
            }
            hir::stmt::Stmt::Do(keyword, body, cond) => self.do_statement(func, keyword, *body, cond),
            hir::stmt::Stmt::For(left_paren, init, cond, inc, body) => {
                self.for_statement(func, left_paren, init, cond, inc, *body)
            }
            hir::stmt::Stmt::Break(keyword) => self.break_statement(func, keyword),
            hir::stmt::Stmt::Continue(keyword) => self.continue_statement(func, keyword),
            hir::stmt::Stmt::Switch(keyword, cond, body) => {
                self.switch_statement(func, keyword, cond, *body)
            }
            hir::stmt::Stmt::Case(keyword, value, body) => {
                self.case_statement(func, keyword, value, *body)
            }
            hir::stmt::Stmt::Default(keyword, body) => self.default_statement(func, keyword, *body),
            hir::stmt::Stmt::Goto(label) => self.goto_statement(func, label),
            hir::stmt::Stmt::Label(name, body) => self.label_statement(func, name, *body),
        }
    }
    fn goto_statement(
        &mut self,
        func: &mut mir::decl::Function,
        label: Token,
    ) -> Result<mir::stmt::Stmt, Error> {
        func.gotos.push(label.clone());

        Ok(mir::stmt::Stmt::Goto(label.unwrap_string()))
    }
    fn label_statement(
        &mut self,
        func: &mut mir::decl::Function,
        name_token: Token,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        func.insert_label(&name_token)?;
        let body = self.visit_stmt(func, body)?;

        Ok(mir::stmt::Stmt::Label(name_token.unwrap_string(), Box::new(body)))
    }
    fn switch_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
        cond: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let cond = self.visit_expr(&mut Some(func), cond)?;
        if !cond.qtype.ty.is_integer() {
            return Err(Error::new(
                &token,
                ErrorKind::NotInteger("switch conditional", cond.qtype),
            ));
        }
        let labels = Rc::new(RefCell::new(Vec::new()));
        func.scope
            .push(ScopeKind::Switch(cond.qtype.clone(), Rc::clone(&labels)));
        func.switches.push_back(Rc::clone(&labels));

        let stmt = self.visit_stmt(func, body);

        func.scope.pop();

        Ok(mir::stmt::Stmt::Switch(cond, Box::new(stmt?)))
    }
    fn case_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
        expr: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let mut expr = self.visit_expr(&mut Some(func), expr)?;
        if !expr.qtype.ty.is_integer() {
            return Err(Error::new(
                &token,
                ErrorKind::NotInteger("case value", expr.qtype),
            ));
        }
        let value = expr.get_literal_constant(&token, "case value")?;

        if let Some(ScopeKind::Switch(qtype, labels)) =
            find_scope!(&mut func.scope, ScopeKind::Switch(..))
        {
            if value.type_overflow(&qtype.ty) {
                return Err(Error::new(&token, ErrorKind::CaseOverflow(value, qtype.clone())));
            }

            let case = CaseKind::Case(value.clone());
            if !labels.borrow().contains(&case) {
                labels.borrow_mut().push(case)
            } else {
                return Err(Error::new(&token, ErrorKind::DuplicateCase(value)));
            }
        } else {
            return Err(Error::new(&token, ErrorKind::NotIn("case", "switch")));
        }

        let body = self.visit_stmt(func, body)?;

        Ok(mir::stmt::Stmt::Case(Box::new(body)))
    }
    fn default_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        if let Some(ScopeKind::Switch(_, labels)) = find_scope!(&mut func.scope, ScopeKind::Switch(..)) {
            if !labels.borrow().contains(&CaseKind::Default) {
                labels.borrow_mut().push(CaseKind::Default)
            } else {
                return Err(Error::new(&token, ErrorKind::MultipleDefaults));
            }
        } else {
            return Err(Error::new(&token, ErrorKind::NotIn("default", "switch")));
        }
        let body = self.visit_stmt(func, body)?;

        Ok(mir::stmt::Stmt::Default(Box::new(body)))
    }
    fn do_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
        body: hir::stmt::Stmt,
        cond: hir::expr::ExprKind,
    ) -> Result<mir::stmt::Stmt, Error> {
        func.scope.push(ScopeKind::Loop);
        let body = self.visit_stmt(func, body)?;
        func.scope.pop();

        let cond = self.visit_expr(&mut Some(func), cond)?;
        if !cond.qtype.ty.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::NotScalar("conditional", cond.qtype),
            ));
        }

        func.returns_all_paths = false;

        Ok(mir::stmt::Stmt::Do(Box::new(body), cond))
    }
    fn for_statement(
        &mut self,
        func: &mut mir::decl::Function,
        left_paren: Token,
        init: Option<Box<hir::stmt::Stmt>>,
        cond: Option<hir::expr::ExprKind>,
        inc: Option<hir::expr::ExprKind>,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        self.env.enter();

        let init = match init.map(|stmt| *stmt) {
            Some(hir::stmt::Stmt::Declaration(decl)) => {
                let storage_classes = self.parse_storage_classes(&decl.decl_specs.storage_classes)?;
                match storage_classes {
                    None
                    | Some(mir::decl::StorageClass::Auto)
                    | Some(mir::decl::StorageClass::Register) => {
                        Some(self.visit_stmt(func, hir::stmt::Stmt::Declaration(decl))?)
                    }
                    Some(sc) => {
                        return Err(Error::new(
                            &left_paren,
                            ErrorKind::InvalidStorageClass(sc, "for-statement"),
                        ))
                    }
                }
            }
            Some(stmt) => Some(self.visit_stmt(func, stmt)?),
            None => None,
        };

        let cond = if let Some(cond) = cond {
            let cond = self.visit_expr(&mut Some(func), cond)?;
            if !cond.qtype.ty.is_scalar() {
                return Err(Error::new(
                    &left_paren,
                    ErrorKind::NotScalar("conditional", cond.qtype),
                ));
            }
            Some(cond)
        } else {
            None
        };

        func.scope.push(ScopeKind::Loop);
        let body = self.visit_stmt(func, body)?;

        let inc = inc.map(|inc| self.visit_expr(&mut Some(func), inc)).transpose()?;

        func.scope.pop();
        self.env.exit();

        func.returns_all_paths = false;

        Ok(mir::stmt::Stmt::For(
            init.map(Box::new),
            cond,
            inc,
            Box::new(body),
        ))
    }
    fn break_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
    ) -> Result<mir::stmt::Stmt, Error> {
        if find_scope!(&mut func.scope, ScopeKind::Loop | ScopeKind::Switch(..)).is_none() {
            Err(Error::new(
                &token,
                ErrorKind::NotIn("break", "loop/switch-statement"),
            ))
        } else {
            Ok(mir::stmt::Stmt::Break)
        }
    }
    fn continue_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
    ) -> Result<mir::stmt::Stmt, Error> {
        if find_scope!(&mut func.scope, ScopeKind::Loop).is_none() {
            Err(Error::new(&token, ErrorKind::NotIn("continue", "loop")))
        } else {
            Ok(mir::stmt::Stmt::Continue)
        }
    }

    fn while_statement(
        &mut self,
        func: &mut mir::decl::Function,
        left_paren: Token,
        cond: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let cond = self.visit_expr(&mut Some(func), cond)?;
        if !cond.qtype.ty.is_scalar() {
            return Err(Error::new(
                &left_paren,
                ErrorKind::NotScalar("conditional", cond.qtype),
            ));
        }

        func.scope.push(ScopeKind::Loop);
        let body = self.visit_stmt(func, body)?;
        func.scope.pop();

        func.returns_all_paths = false;

        Ok(mir::stmt::Stmt::While(cond, Box::new(body)))
    }

    fn if_statement(
        &mut self,
        func: &mut mir::decl::Function,
        keyword: Token,
        cond: hir::expr::ExprKind,
        then_branch: hir::stmt::Stmt,
        else_branch: Option<Box<hir::stmt::Stmt>>,
    ) -> Result<mir::stmt::Stmt, Error> {
        let cond = self.visit_expr(&mut Some(func), cond)?;
        if !cond.qtype.ty.is_scalar() {
            return Err(Error::new(
                &keyword,
                ErrorKind::NotScalar("conditional", cond.qtype),
            ));
        }

        let then_branch = self.visit_stmt(func, then_branch)?;
        let then_return = func.returns_all_paths;
        func.returns_all_paths = false;

        let else_branch = else_branch
            .map(|stmt| {
                let else_branch = self.visit_stmt(func, *stmt);
                let else_return = func.returns_all_paths;

                if !then_return || !else_return {
                    func.returns_all_paths = false;
                }
                else_branch
            })
            .transpose()?;

        Ok(mir::stmt::Stmt::If(
            cond,
            Box::new(then_branch),
            else_branch.map(Box::new),
        ))
    }

    fn return_statement(
        &mut self,
        func: &mut mir::decl::Function,
        keyword: Token,
        expr: Option<hir::expr::ExprKind>,
    ) -> Result<mir::stmt::Stmt, Error> {
        func.returns_all_paths = true;

        let expr = if let Some(expr) = expr {
            let expr = self.visit_expr(&mut Some(func), expr)?;

            let expr = expr.decay(&keyword)?;
            if !func.return_type.type_compatible(&expr) {
                return Err(Error::new(
                    &keyword,
                    ErrorKind::MismatchedFunctionReturn(func.return_type.clone(), expr.qtype),
                ));
            }
            let expr = Self::maybe_cast(func.return_type.clone(), expr);

            Some(expr)
        } else {
            let return_type = QualType::new(Type::Primitive(Primitive::Void));
            let return_expr = mir::expr::Expr {
                kind: mir::expr::ExprKind::Nop,
                qtype: return_type.clone(),
                value_kind: ValueKind::Rvalue,
            };

            if !func.return_type.type_compatible(&return_expr) {
                return Err(Error::new(
                    &keyword,
                    ErrorKind::MismatchedFunctionReturn(func.return_type.clone(), return_type),
                ));
            }

            None
        };

        Ok(mir::stmt::Stmt::Return(expr))
    }

    fn block(
        &mut self,
        func: &mut mir::decl::Function,
        body: Vec<hir::stmt::Stmt>,
    ) -> Result<mir::stmt::Stmt, Error> {
        let mut errors = Vec::new();
        let mut stmts = Vec::new();

        for stmt in body {
            match self.visit_stmt(func, stmt) {
                Ok(s) => stmts.push(s),
                Err(e) => errors.push(e),
            }
        }

        self.env.exit();

        if errors.is_empty() {
            Ok(mir::stmt::Stmt::Block(stmts))
        } else {
            Err(Error::new_multiple(errors))
        }
    }

    pub fn visit_expr(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let mut expr = match expr {
            hir::expr::ExprKind::Binary { left, token, right } => {
                self.evaluate_binary(func, *left, token, *right)
            }
            hir::expr::ExprKind::Unary { token, right } => self.evaluate_unary(func, token, *right),
            hir::expr::ExprKind::Char(c) => Ok(mir::expr::Expr {
                qtype: QualType::new(Type::Primitive(Primitive::Char(false))),
                kind: mir::expr::ExprKind::Literal(LiteralKind::Signed(c as i64)),
                value_kind: ValueKind::Rvalue,
            }),
            hir::expr::ExprKind::Number(literal) => Ok(mir::expr::Expr {
                qtype: QualType::new(Type::Primitive(literal.integer_type())),
                kind: mir::expr::ExprKind::Literal(literal),
                value_kind: ValueKind::Rvalue,
            }),
            hir::expr::ExprKind::String(token) => self.string(token.unwrap_string()),
            hir::expr::ExprKind::Logical { left, token, right } => {
                self.evaluate_logical(func, *left, token, *right)
            }
            hir::expr::ExprKind::Comparison { left, token, right } => {
                self.evaluate_comparison(func, *left, token, *right)
            }
            hir::expr::ExprKind::Ident(token) => self.ident(token),
            hir::expr::ExprKind::Assign { l_expr, token, r_expr } => {
                let left = self.visit_expr(func, *l_expr)?;
                let right = self.visit_expr(func, *r_expr)?;

                self.assign(left, token, right)
            }
            hir::expr::ExprKind::CompoundAssign { l_expr, token, r_expr } => {
                self.compound_assign(func, *l_expr, token, *r_expr)
            }
            hir::expr::ExprKind::Call { left_paren, caller, args } => {
                self.evaluate_call(func, left_paren, *caller, args)
            }
            hir::expr::ExprKind::PostUnary { left, token } => {
                self.evaluate_postunary(func, token, *left)
            }
            hir::expr::ExprKind::MemberAccess { token, expr, member } => {
                self.member_access(func, token, member, *expr)
            }
            hir::expr::ExprKind::Cast { token, decl_type, expr } => {
                self.explicit_cast(func, token, *expr, decl_type)
            }
            hir::expr::ExprKind::Ternary { token, cond, true_expr, false_expr } => {
                self.ternary(func, token, *cond, *true_expr, *false_expr)
            }
            hir::expr::ExprKind::Comma { left, right } => self.comma(func, *left, *right),
            hir::expr::ExprKind::SizeofType { token, decl_type } => self.sizeof_type(token, decl_type),
            hir::expr::ExprKind::SizeofExpr { token, expr } => self.sizeof_expr(func, token, *expr),
            hir::expr::ExprKind::Nop => Ok(mir::expr::Expr {
                kind: mir::expr::ExprKind::Nop,
                qtype: QualType::new(Type::Primitive(Primitive::Void)),
                value_kind: ValueKind::Rvalue,
            }),
        }?;

        expr.integer_const_fold()?;

        Ok(expr)
    }
    fn check_type_compatibility(
        token: &Token,
        left_qtype: &QualType,
        right: &mir::expr::Expr,
    ) -> Result<(), Error> {
        if left_qtype.ty.is_void() || right.qtype.ty.is_void() || !left_qtype.type_compatible(right) {
            Err(Error::new(
                token,
                ErrorKind::IllegalAssign(left_qtype.clone(), right.qtype.clone()),
            ))
        } else {
            Ok(())
        }
    }

    // TODO: display warning when casting down
    fn explicit_cast(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        expr: hir::expr::ExprKind,
        decl_type: hir::decl::DeclType,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(func, expr)?.decay(&token)?;
        let new_type = self.parse_type(&token, decl_type)?;

        if !new_type.ty.is_void() && (!expr.qtype.ty.is_scalar() || !new_type.ty.is_scalar()) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidExplicitCast(expr.qtype, new_type.clone()),
            ));
        }

        Ok(Self::always_cast(expr, new_type).to_rval())
    }
    // ensures that equal sized expressions still have new type
    fn always_cast(expr: mir::expr::Expr, new_type: QualType) -> mir::expr::Expr {
        // TODO: usual_arithmetic_conversion() ???
        match expr.qtype.ty.size().cmp(&new_type.ty.size()) {
            Ordering::Less => expr.cast_to(new_type, CastDirection::Up),
            Ordering::Greater => expr.cast_to(new_type, CastDirection::Down),
            Ordering::Equal => expr.cast_to(new_type, CastDirection::Equal),
        }
    }
    fn maybe_cast(new_type: QualType, expr: mir::expr::Expr) -> mir::expr::Expr {
        match expr.qtype.ty.size().cmp(&new_type.ty.size()) {
            Ordering::Less => expr.cast_to(new_type, CastDirection::Up),
            Ordering::Greater => expr.cast_to(new_type, CastDirection::Down),
            Ordering::Equal => expr,
        }
    }

    fn sizeof_type(
        &mut self,
        token: Token,
        decl_type: hir::decl::DeclType,
    ) -> Result<mir::expr::Expr, Error> {
        let qtype = self.parse_type(&token, decl_type)?;

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Literal(LiteralKind::Unsigned(qtype.ty.size() as u64)),
            qtype: QualType::new(Type::Primitive(Primitive::Long(true))),
            value_kind: ValueKind::Rvalue,
        })
    }

    fn sizeof_expr(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(func, expr)?;

        if !expr.qtype.ty.is_void() && !expr.qtype.ty.is_complete() {
            return Err(Error::new(&token, ErrorKind::IncompleteType(expr.qtype)));
        }

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Literal(LiteralKind::Unsigned(expr.qtype.ty.size() as u64)),
            qtype: QualType::new(Type::Primitive(Primitive::Long(true))),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn comma(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        left: hir::expr::ExprKind,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let left = self.visit_expr(func, left)?;
        let right = self.visit_expr(func, right)?;

        Ok(mir::expr::Expr {
            value_kind: ValueKind::Rvalue,
            qtype: right.qtype.clone(),
            kind: mir::expr::ExprKind::Comma {
                left: Box::new(left),
                right: Box::new(right),
            },
        })
    }
    fn ternary(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        cond: hir::expr::ExprKind,
        true_expr: hir::expr::ExprKind,
        false_expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let cond = self.visit_expr(func, cond)?;
        if !cond.qtype.ty.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::NotScalar("conditional", cond.qtype),
            ));
        }
        let true_expr = self.visit_expr(func, true_expr)?;
        let false_expr = self.visit_expr(func, false_expr)?;

        if !true_expr.qtype.type_compatible(&false_expr) {
            return Err(Error::new(
                &token,
                ErrorKind::TypeMismatch(true_expr.qtype, false_expr.qtype),
            ));
        }

        let true_expr = true_expr.maybe_int_promote();
        let false_expr = false_expr.maybe_int_promote();

        let (true_expr, false_expr) = Self::scalar_conversion(true_expr, false_expr);

        Ok(mir::expr::Expr {
            qtype: true_expr.qtype.clone(),
            value_kind: ValueKind::Rvalue,
            kind: mir::expr::ExprKind::Ternary {
                cond: Box::new(cond),
                true_expr: Box::new(true_expr),
                false_expr: Box::new(false_expr),
            },
        })
    }
    fn ident(&mut self, token: Token) -> Result<mir::expr::Expr, Error> {
        let symbol = self.env.get_symbol(&token)?;

        if symbol.borrow().is_typedef() {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidSymbol(token.unwrap_string(), "variable"),
            ));
        }

        let qtype = symbol.borrow().qtype.clone();
        Ok(mir::expr::Expr {
            qtype,
            kind: mir::expr::ExprKind::Ident(Rc::clone(&symbol)),
            value_kind: ValueKind::Lvalue,
        })
    }
    fn member_access(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        member: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(func, expr)?;

        if !expr.qtype.ty.is_complete() {
            return Err(Error::new(&token, ErrorKind::IncompleteMemberAccess(expr.qtype)));
        }

        match &expr.qtype.ty {
            Type::Struct(s) | Type::Union(s) => {
                let member = member.unwrap_string();

                if let Some((member_type, _)) = s
                    .members()
                    .iter()
                    .find(|(_, name)| name.unwrap_string() == member)
                {
                    Ok(mir::expr::Expr {
                        kind: mir::expr::ExprKind::MemberAccess { member, expr: Box::new(expr) },
                        qtype: member_type.clone(),
                        value_kind: ValueKind::Lvalue,
                    })
                } else {
                    Err(Error::new(
                        &token,
                        ErrorKind::NonExistantMember(member, expr.qtype),
                    ))
                }
            }
            _ => Err(Error::new(&token, ErrorKind::InvalidMemberAccess(expr.qtype))),
        }
    }
    fn evaluate_postunary(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let qtype = self.visit_expr(func, expr.clone())?.qtype;

        let (comp_op, bin_op) = match token.kind {
            TokenKind::PlusPlus => (TokenKind::PlusEqual, TokenKind::Minus),
            TokenKind::MinusMinus => (TokenKind::MinusEqual, TokenKind::Plus),
            _ => unreachable!("not a postunary token"),
        };

        // A++ <=> (A += 1) - 1 or A-- <=> (A -= 1) + 1
        let postunary_sugar = hir::expr::ExprKind::Binary {
            left: Box::new(hir::expr::ExprKind::CompoundAssign {
                l_expr: Box::new(expr),
                token: Token { kind: comp_op, ..token.clone() },
                r_expr: Box::new(hir::expr::ExprKind::Number(LiteralKind::Signed(1))),
            }),
            token: Token { kind: bin_op, ..token },
            right: Box::new(hir::expr::ExprKind::Number(LiteralKind::Signed(1))),
        };

        // need to cast back to left-type since binary operation integer promotes
        // char c; typeof(c--) == char
        Ok(Self::maybe_cast(qtype, self.visit_expr(func, postunary_sugar)?))
    }
    fn string(&mut self, data: String) -> Result<mir::expr::Expr, Error> {
        let len = data.len() + 1; // extra byte for \0-Terminator
        self.const_labels
            .insert(data.clone(), create_label(&mut self.const_label_count));

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::String(data),
            qtype: QualType::new(Type::Array(
                Box::new(QualType::new(Type::Primitive(Primitive::Char(false)))),
                ArraySize::Known(len),
            )),
            value_kind: ValueKind::Lvalue,
        })
    }
    fn compound_assign(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        l_expr: hir::expr::ExprKind,
        token: Token,
        r_expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let qtype = self.visit_expr(func, l_expr.clone())?.qtype;

        // to not evaluate l-expr twice convert `A op= B` to `tmp = &A, *tmp = *tmp op B`
        self.env.enter();
        let tmp_token = Token {
            // have to generate unique name so normal variables are not confused for tmp
            kind: TokenKind::Ident(format!("tmp{}{}", token.line_index, token.column)),
            ..token.clone()
        };
        let tmp_type = qtype.pointer_to();
        let tmp_symbol = self
            .env
            .declare_symbol(
                &tmp_token,
                Symbol {
                    storage_class: None,
                    qtype: tmp_type.clone(),
                    kind: InitType::Declaration,
                    reg: None,
                    token: token.clone(),
                },
            )
            .expect("always valid to declare tmp in new scope");

        if let Some(func) = func {
            func.increment_stack_size(&tmp_symbol);
        }

        // tmp = &A, *tmp = *tmp op B
        let compound_sugar = hir::expr::ExprKind::Comma {
            left: Box::new(hir::expr::ExprKind::Assign {
                l_expr: Box::new(hir::expr::ExprKind::Ident(tmp_token.clone())),
                token: token.clone(),
                r_expr: Box::new(hir::expr::ExprKind::Unary {
                    token: Token { kind: TokenKind::Amp, ..token.clone() },
                    right: Box::new(l_expr),
                }),
            }),
            right: Box::new(hir::expr::ExprKind::Assign {
                l_expr: Box::new(hir::expr::ExprKind::Unary {
                    token: Token { kind: TokenKind::Star, ..token.clone() },
                    right: Box::new(hir::expr::ExprKind::Ident(tmp_token.clone())),
                }),
                token: token.clone(),
                r_expr: Box::new(hir::expr::ExprKind::Binary {
                    left: Box::new(hir::expr::ExprKind::Unary {
                        token: Token { kind: TokenKind::Star, ..token.clone() },
                        right: Box::new(hir::expr::ExprKind::Ident(tmp_token.clone())),
                    }),
                    token: Token {
                        kind: token.kind.comp_to_binary(),
                        ..token
                    },
                    right: Box::new(r_expr),
                }),
            }),
        };

        let expr = self.visit_expr(func, compound_sugar).map_err(|err| {
            self.env.exit();
            err
        })?;

        self.env.exit();

        // INFO: still need to pass var-symbol here so that codegen declares var when it has the correct base-pointer offset
        Ok(mir::expr::Expr {
            qtype: expr.qtype.clone(),
            kind: mir::expr::ExprKind::CompoundAssign { tmp_symbol, expr: Box::new(expr) },
            value_kind: ValueKind::Rvalue,
        })
    }
    fn assign(
        &mut self,
        left: mir::expr::Expr,
        token: Token,
        right: mir::expr::Expr,
    ) -> Result<mir::expr::Expr, Error> {
        if left.qtype.ty.is_array() || left.qtype.ty.is_func() {
            return Err(Error::new(&token, ErrorKind::NotAssignable(left.qtype)));
        }

        if left.value_kind != ValueKind::Lvalue {
            return Err(Error::new(&token, ErrorKind::NotLvalue("left of assignment")));
        }

        if !left.qtype.ty.is_complete() {
            return Err(Error::new(&token, ErrorKind::IncompleteAssign(left.qtype)));
        }

        if left.qtype.qualifiers.is_const {
            return Err(Error::new(&token, ErrorKind::ConstAssign));
        }
        if let Type::Struct(s) | Type::Union(s) = &left.qtype.ty {
            if let Some((_, member)) = s.members().iter().find(|(qtype, _)| qtype.qualifiers.is_const) {
                return Err(Error::new(
                    &token,
                    ErrorKind::ConstStructAssign(left.qtype.clone(), member.unwrap_string()),
                ));
            }
        }

        let right = right.decay(&token)?.to_rval();
        Self::check_type_compatibility(&token, &left.qtype, &right)?;
        let right = Self::maybe_cast(left.qtype.clone(), right);

        Ok(mir::expr::Expr {
            // 6.5.16.3 The type of an assignment expression is the type
            // of the left operand unless the left operand has qualified type,
            // in which case it is the unqualified version of the type of the left operand
            qtype: left.qtype.unqualified(),
            value_kind: ValueKind::Rvalue,
            kind: mir::expr::ExprKind::Assign {
                l_expr: Box::new(left),
                r_expr: Box::new(right),
            },
        })
    }

    fn evaluate_call(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        left_paren: Token,
        caller: hir::expr::ExprKind,
        parsed_args: Vec<hir::expr::ExprKind>,
    ) -> Result<mir::expr::Expr, Error> {
        let caller = self.visit_expr(func, caller)?;

        let mut args: Vec<mir::expr::Expr> = Vec::new();
        for (index, expr) in parsed_args.into_iter().enumerate() {
            let arg = self
                .visit_expr(func, expr)?
                .decay(&left_paren)?
                .maybe_int_promote();

            if !arg.qtype.ty.is_complete() {
                return Err(Error::new(
                    &left_paren,
                    ErrorKind::IncompleteArgType(index, arg.qtype),
                ));
            }

            args.push(arg);
        }

        let func_type = match caller.qtype.ty.clone() {
            Type::Function(func_type) => func_type,
            ty => {
                let mut pointer_to_func = None;
                if let Type::Pointer(to) = ty {
                    if let Type::Function(func_type) = to.ty {
                        pointer_to_func = Some(func_type)
                    }
                }
                if let Some(func_type) = pointer_to_func {
                    func_type
                } else {
                    return Err(Error::new(&left_paren, ErrorKind::InvalidCaller(caller.qtype)));
                }
            }
        };

        if (!func_type.variadic && func_type.params.len() != args.len())
            || (func_type.variadic && func_type.params.len() > args.len())
        {
            return Err(Error::new(
                &left_paren,
                ErrorKind::MismatchedArity(caller.qtype, func_type.params.len(), args.len()),
            ));
        }
        let args = self.args_and_params_match(&left_paren, &caller.qtype, func_type.params, args)?;

        let caller = if caller.qtype.ty.is_ptr() {
            self.check_deref(Token { kind: TokenKind::Star, ..left_paren }, caller)
                .expect("already checked if caller is ptr")
        } else {
            caller
        };

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Call { caller: Box::new(caller), args },
            qtype: *func_type.return_type,
            value_kind: ValueKind::Rvalue,
        })
    }
    fn args_and_params_match(
        &self,
        left_paren: &Token,
        qtype: &QualType,
        params: Vec<QualType>,
        mut args: Vec<mir::expr::Expr>,
    ) -> Result<Vec<mir::expr::Expr>, Error> {
        let mut new_args = Vec::new();

        // previously checked that args >= params, can be more args because of variadic params
        let remaining_args: Vec<mir::expr::Expr> = args.drain(params.len()..).collect();

        for (index, (arg, param_type)) in args.into_iter().zip(params).enumerate() {
            Self::check_type_compatibility(left_paren, &param_type, &arg).or(Err(Error::new(
                left_paren,
                ErrorKind::MismatchedArgs(index, qtype.clone(), param_type.clone(), arg.qtype.clone()),
            )))?;

            // cast argument to the correct parameter type
            new_args.push(
                if param_type.ty.size() > Type::Primitive(Primitive::Char(false)).size() {
                    Self::maybe_cast(param_type, arg)
                } else {
                    arg
                },
            );
        }

        new_args.extend(remaining_args);

        Ok(new_args)
    }

    fn evaluate_logical(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let left = self.visit_expr(func, left)?.to_rval().decay(&token)?;
        let right = self.visit_expr(func, right)?.to_rval().decay(&token)?;

        if !left.qtype.ty.is_scalar() || !right.qtype.ty.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidLogical(token.kind.clone(), left.qtype, right.qtype),
            ));
        }

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Logical {
                token,
                left: Box::new(left),
                right: Box::new(right),
            },
            qtype: QualType::new(Type::Primitive(Primitive::Int(false))),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn evaluate_comparison(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let left = self.visit_expr(func, left)?.to_rval().decay(&token)?;
        let right = self.visit_expr(func, right)?.to_rval().decay(&token)?;

        if !Self::is_valid_comp(&left, &right) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidComp(token.kind.clone(), left.qtype, right.qtype),
            ));
        }

        let left = left.maybe_int_promote();
        let right = right.maybe_int_promote();

        let (left, right) = Self::scalar_conversion(left, right);

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Comparison {
                token,
                left: Box::new(left),
                right: Box::new(right),
            },
            qtype: QualType::new(Type::Primitive(Primitive::Int(false))),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn is_valid_comp(left: &mir::expr::Expr, right: &mir::expr::Expr) -> bool {
        let integer_operands = left.qtype.ty.is_integer() && right.qtype.ty.is_integer();
        let compatible_pointers = (left.qtype.ty.is_ptr() || right.qtype.ty.is_ptr())
                // have to check in both directions since either expr can be 0 literal
            && (left.qtype.type_compatible(&right)
            || right.qtype.type_compatible(&left));

        integer_operands || compatible_pointers
    }

    fn evaluate_binary(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let left = self.visit_expr(func, left)?.to_rval().decay(&token)?;
        let right = self.visit_expr(func, right)?.to_rval().decay(&token)?;

        if !Self::is_valid_bin(&token.kind, &left.qtype, &right) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidBinary(token.kind.clone(), left.qtype, right.qtype),
            ));
        }

        let mut left = left.maybe_int_promote();
        let mut right = right.maybe_int_promote();

        if let Some((expr, ptr_type)) = Self::maybe_scale_index(&mut left, &mut right) {
            expr.kind = mir::expr::ExprKind::Scale {
                by_amount: ptr_type.deref_at().expect("can only scale pointers").ty.size(),
                token: token.clone(),
                direction: mir::expr::ScaleDirection::Up,
                expr: Box::new(expr.clone()),
            };
            // expr.qtype = ptr_type;
        }

        Ok(Self::binary_type_promotion(token, left, right))
    }

    fn is_valid_bin(operator: &TokenKind, left_type: &QualType, right_expr: &mir::expr::Expr) -> bool {
        match (&left_type.ty, &right_expr.qtype.ty) {
            (left, right) if !left.is_scalar() || !right.is_scalar() => false,
            (Type::Pointer(_), Type::Pointer(_)) => {
                left_type.type_compatible(right_expr) && operator == &TokenKind::Minus
            }
            (_, Type::Pointer(_)) => operator == &TokenKind::Plus,
            (Type::Pointer(_), _) => operator == &TokenKind::Plus || operator == &TokenKind::Minus,
            _ => true,
        }
    }

    // scale index when pointer arithmetic
    fn maybe_scale_index<'a>(
        left: &'a mut mir::expr::Expr,
        right: &'a mut mir::expr::Expr,
    ) -> Option<(&'a mut mir::expr::Expr, QualType)> {
        match (&left.qtype.ty, &right.qtype.ty) {
            (index, Type::Pointer(inner)) if index.is_integer() && inner.ty.size() > 1 => {
                Some((left, right.qtype.clone()))
            }
            (Type::Pointer(inner), index) if index.is_integer() && inner.ty.size() > 1 => {
                Some((right, left.qtype.clone()))
            }
            _ => None,
        }
    }

    fn binary_type_promotion(
        token: Token,
        left: mir::expr::Expr,
        right: mir::expr::Expr,
    ) -> mir::expr::Expr {
        let (left, right, scale_factor) = match (&left.qtype.ty, &right.qtype.ty, &token.kind) {
            // shift operations always have the type of the left operand
            (.., TokenKind::GreaterGreater | TokenKind::LessLess) => (left, right, None),

            // (Type::Pointer(_), Type::Pointer(_), _)
            //     if matches!(
            //         left.kind,
            //         mir::expr::ExprKind::Scale {
            //             direction: mir::expr::ScaleDirection::Up,
            //             ..
            //         }
            //     ) || matches!(
            //         right.kind,
            //         mir::expr::ExprKind::Scale {
            //             direction: mir::expr::ScaleDirection::Up,
            //             ..
            //         }
            //     ) =>
            // {
            //     (left, right, None)
            // }

            // if pointer - pointer, scale result before operation to match left-pointers type
            (Type::Pointer(inner), Type::Pointer(_), _) => {
                let scale_factor = inner.ty.size();
                let long_ty = QualType::new(Type::Primitive(Primitive::Long(false)));
                (
                    Self::always_cast(left, long_ty.clone()),
                    Self::always_cast(right, long_ty),
                    Some(scale_factor),
                )
            }
            _ => {
                let (left, right) = Self::scalar_conversion(left, right);
                (left, right, None)
            }
        };

        let result = mir::expr::Expr {
            qtype: left.qtype.clone(),
            kind: mir::expr::ExprKind::Binary {
                token: token.clone(),
                left: Box::new(left),
                right: Box::new(right),
            },
            value_kind: mir::expr::ValueKind::Rvalue,
        };

        if let Some(scale_factor) = scale_factor {
            mir::expr::Expr {
                kind: mir::expr::ExprKind::Scale {
                    token,
                    by_amount: scale_factor,
                    direction: mir::expr::ScaleDirection::Down,
                    expr: Box::new(result),
                },
                qtype: QualType::new(Type::Primitive(Primitive::Long(false))),
                value_kind: mir::expr::ValueKind::Rvalue,
            }
        } else {
            result
        }
    }
    fn scalar_conversion(
        left: mir::expr::Expr,
        right: mir::expr::Expr,
    ) -> (mir::expr::Expr, mir::expr::Expr) {
        let (left, right) = Self::pointer_conversion(left, right);
        Self::usual_arithmetic_conversion(left, right)
    }
    fn pointer_conversion(
        left: mir::expr::Expr,
        right: mir::expr::Expr,
    ) -> (mir::expr::Expr, mir::expr::Expr) {
        match (&left.qtype.ty, &right.qtype.ty) {
            // if two pointers always convert to `void*` if exists
            (Type::Pointer(inner), other) if other.is_ptr() && inner.ty.is_void() => {
                (left.clone(), Self::always_cast(right, left.qtype))
            }
            (other, Type::Pointer(inner)) if other.is_ptr() && inner.ty.is_void() => {
                (Self::always_cast(left, right.qtype.clone()), right)
            }

            // if integer type and pointer then result is always the pointer type
            (other, Type::Pointer(_)) if !other.is_ptr() => {
                (Self::always_cast(left, right.qtype.clone()), right)
            }
            (Type::Pointer(_), other) if !other.is_ptr() => {
                (left.clone(), Self::always_cast(right, left.qtype))
            }
            _ => (left, right),
        }
    }
    fn usual_arithmetic_conversion(
        left: mir::expr::Expr,
        right: mir::expr::Expr,
    ) -> (mir::expr::Expr, mir::expr::Expr) {
        if !left.qtype.ty.is_integer() || !right.qtype.ty.is_integer() {
            return (left, right);
        }

        match (&left.qtype.ty, &right.qtype.ty) {
            // cast to bigger type
            (left_type, right_type) if left_type.size() > right_type.size() => {
                (left.clone(), Self::always_cast(right, left.qtype))
            }
            (left_type, right_type) if left_type.size() < right_type.size() => {
                (Self::always_cast(left, right.qtype.clone()), right)
            }
            // if both operands have same size then cast to unsigned type if it exists
            (left_type, right_type) => {
                if left_type.is_unsigned() {
                    (left.clone(), Self::always_cast(right, left.qtype))
                } else if right_type.is_unsigned() {
                    (Self::always_cast(left, right.qtype.clone()), right)
                } else {
                    (left, right)
                }
            }
        }
    }
    fn evaluate_unary(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let right = self.visit_expr(func, right)?;

        if matches!(token.kind, TokenKind::Amp) {
            // array doesn't decay during '&' expression
            self.check_address(token, right)
        } else {
            let right = right.decay(&token)?;

            match token.kind {
                TokenKind::Star => self.check_deref(token, right),
                TokenKind::Bang => {
                    let right = right.to_rval();
                    let right = Box::new(right.maybe_int_promote());

                    if !right.qtype.ty.is_scalar() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidUnary(token.kind.clone(), right.qtype, "scalar"),
                        ));
                    }

                    Ok(mir::expr::Expr {
                        kind: mir::expr::ExprKind::Unary { token, right },
                        qtype: QualType::new(Type::Primitive(Primitive::Int(false))),
                        value_kind: ValueKind::Rvalue,
                    })
                }
                TokenKind::Minus | TokenKind::Tilde | TokenKind::Plus => {
                    let right = right.to_rval();
                    let right = Box::new(right.maybe_int_promote());

                    if !right.qtype.ty.is_integer() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidUnary(token.kind.clone(), right.qtype, "integer"),
                        ));
                    }

                    Ok(mir::expr::Expr {
                        qtype: right.qtype.clone(),
                        kind: mir::expr::ExprKind::Unary { token, right },
                        value_kind: ValueKind::Rvalue,
                    })
                }
                _ => unreachable!(), // ++a or --a are evaluated as compound assignment
            }
        }
    }
    fn check_address(&self, token: Token, right: mir::expr::Expr) -> Result<mir::expr::Expr, Error> {
        if right.value_kind == ValueKind::Lvalue {
            if let mir::expr::ExprKind::Ident(symbol) = &right.kind {
                if symbol.borrow().is_register() {
                    return Err(Error::new(
                        &token,
                        ErrorKind::RegisterAddress(symbol.borrow().token.unwrap_string()),
                    ));
                }
            }

            Ok(mir::expr::Expr {
                qtype: right.qtype.clone().pointer_to(),
                value_kind: ValueKind::Rvalue,
                kind: mir::expr::ExprKind::Unary { token, right: Box::new(right) },
            })
        } else {
            Err(Error::new(&token, ErrorKind::NotLvalue("as unary '&' operand")))
        }
    }
    fn check_deref(&self, token: Token, right: mir::expr::Expr) -> Result<mir::expr::Expr, Error> {
        if let Some(inner) = right.qtype.deref_at() {
            Ok(mir::expr::Expr {
                value_kind: ValueKind::Lvalue,
                qtype: inner,
                kind: mir::expr::ExprKind::Unary { right: Box::new(right), token },
            })
        } else {
            Err(Error::new(&token, ErrorKind::InvalidDerefType(right.qtype)))
        }
    }
}

pub fn align_by(mut offset: usize, type_size: usize) -> usize {
    let remainder = offset % type_size;
    if remainder != 0 {
        offset += type_size - remainder;
    }
    offset
}
pub fn create_label(index: &mut usize) -> usize {
    let prev = *index;
    *index += 1;
    prev
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::parser::tests::setup;
    use crate::setup_type;

    // setup environment (declare variables/types)
    fn setup_env(typechecker: &mut TypeChecker, env: &str) {
        let env = setup(env).parse().unwrap();
        typechecker.check_declarations(env).unwrap();
    }

    fn typecheck(input: &str) -> Result<(), Vec<Error>> {
        let external_decls = setup(input).parse().unwrap();
        match TypeChecker::new().check_declarations(external_decls) {
            Ok(_) => Ok(()),
            Err(e) => Err(e.flatten_multiple()),
        }
    }

    macro_rules! assert_type {
        ($input:expr,$expected_type:expr,$env:expr) => {
            let expr = setup($input).expression().unwrap();

            let mut typechecker = TypeChecker::new();
            setup_env(&mut typechecker, $env);

            let actual = typechecker.visit_expr(&mut None, expr).unwrap();
            let expected_type = setup_type!($expected_type, typechecker);

            assert!(
                actual.qtype == expected_type,
                "actual: {}, expected: {}",
                actual.qtype,
                expected_type.to_string(),
            );
        };
    }

    macro_rules! assert_type_err {
        ($input:expr,$expected_err:pat,$env:expr) => {
            let expr = setup($input).expression().unwrap();

            let mut typechecker = TypeChecker::new();
            setup_env(&mut typechecker, $env);

            let actual = typechecker.visit_expr(&mut None, expr).unwrap_err();

            assert!(
                matches!(actual.kind, $expected_err),
                "actual: {:?}, expected: {}",
                actual,
                stringify!($expected_err),
            );
        };
    }

    macro_rules! assert_const_expr {
        ($input: expr, $expected: expr, $env: expr) => {
            let expr = setup($input).expression().unwrap();

            let mut typechecker = TypeChecker::new();
            setup_env(&mut typechecker, $env);

            let expr = typechecker
                .visit_expr(&mut None, expr)
                .unwrap()
                .decay(&Token::default(TokenKind::Semicolon))
                .unwrap();

            let actual = expr.is_constant();

            assert_eq!(actual, $expected);
        };
    }
    fn setup_init_list(input: &str) -> Result<mir::decl::Init, Error> {
        // TODO: maybe be can parser.parse() so that external declaration doesnt have to be public
        let hir::decl::ExternalDeclaration::Declaration(decls) =
                setup(input).external_declaration().unwrap() else {unreachable!("only passing type")};

        let hir::decl::Declaration { decl_specs, declarators } = decls;
        let mut typechecker = TypeChecker::new();

        let declarator = declarators[0].clone();
        let storage_class = typechecker
            .parse_storage_classes(&decl_specs.storage_classes)
            .unwrap();
        let qtype = typechecker.parse_specifiers(decl_specs.specifiers).unwrap();
        let qtype = TypeChecker::parse_qualifiers(qtype, &decl_specs.qualifiers)?;

        let declarator =
            typechecker.declarator(qtype, storage_class, decl_specs.is_inline, declarator, &mut None)?;

        Ok(declarator.unwrap().init.unwrap())
    }
    fn assert_init(actual: mir::decl::Init, expected: Vec<(usize, &'static str, &'static str)>) {
        let mir::decl::Init::Aggr(actual) = actual else {unreachable!()};
        let mut typechecker = TypeChecker::new();

        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert_eq!(actual.1, expected.0);

            let expected_type = setup_type!(expected.2);
            let expected_expr = TypeChecker::maybe_cast(
                expected_type,
                typechecker
                    .visit_expr(&mut None, setup(expected.1).expression().unwrap())
                    .unwrap(),
            );

            assert_eq!(actual.0, expected_expr);
        }
    }

    #[test]
    fn binary_type() {
        assert_type!("a + '2'", "int", "char a;");
    }

    #[test]
    fn shift_type() {
        assert_type!("1 << a", "int", "long a;");
        assert_type!("a << b", "long", "long a; char b;");
        assert_type!("'1' << a", "int", "char a;");
    }

    #[test]
    fn comp_type() {
        assert_type!("1 == a", "int", "long a;");
        assert_type!("a == b", "int", "char *a,*b;");
        assert_type!("1 <= a", "int", "long a;");
        assert_type!("a > b", "int", "char *a,*b;");
        assert_type!("(void*)1 == a", "int", "long* a;");
        assert_type!("0 == a", "int", "long* a;");
        assert_type!("a == 0", "int", "int* a;");

        assert_type_err!("1 == a", ErrorKind::InvalidComp(..), "long *a;");
        assert_type_err!("a == b", ErrorKind::InvalidComp(..), "int *a; long *b;");
    }
    #[test]
    fn cast_type() {
        assert_type!("(int*)b", "int*", "long* b;");
        assert_type_err!("&(int*)b", ErrorKind::NotLvalue(_), "long* b;");
    }

    #[test]
    fn struct_union_expr() {
        let env = "struct Foo {
            int age;
        } s1, s2;
        union Bar {
            int age;
            char c;
        } u1, u2;
        union Bar u3;
        void* a;";

        assert_type_err!("s1 - 1", ErrorKind::InvalidBinary(..), env);
        assert_type!("&s1 + 1", "struct Foo*", env);
        assert_type!("1 + &s2", "struct Foo*", env);
        assert_type!("&s1 - &s2", "long", env);
        assert_type!("&u1 - &u3", "long", env);
        assert_type_err!("s1 + s2", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("s1 - &s2", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("&s1 - s2", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("(struct Foo*)s2", ErrorKind::InvalidExplicitCast(..), env);
        assert_type!("a = (union Bar*)&s2", "void*", env);

        assert_type!("&s1 == &s2", "int", env);
        assert_type!("&u1 == &u2", "int", env);
        assert_type_err!("u1 == u3", ErrorKind::InvalidComp(..), env);
        assert_type!("&u1 == &u3", "int", env);
        assert_type_err!("&s1 == &u2", ErrorKind::InvalidComp(..), env);
        assert_type!("&s1 == 0", "int", env);
        assert_type!("0 == &s2", "int", env);
        assert_type_err!("s1 == s2", ErrorKind::InvalidComp(..), env);
        assert_type_err!("1 == &s2", ErrorKind::InvalidComp(..), env);
        assert_type_err!("!s1", ErrorKind::InvalidUnary(..), env);
        assert_type_err!("s1 && s2", ErrorKind::InvalidLogical(..), env);
        assert_type_err!("s1 && 1", ErrorKind::InvalidLogical(..), env);
        assert_type_err!("s1 - u1", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("&s1 - &u1", ErrorKind::InvalidBinary(..), env);
    }
    #[test]
    fn func_expr() {
        let env = "
void foo(int a) {}
void bar(int a) {}
int baz(int a) { return a; }
int a;";

        assert_type!("foo - bar", "long", env);
        assert_type!("foo + 1", "void (*)(int)", env);
        assert_type!("foo - 1", "void (*)(int)", env);
        assert_type!("1 + foo", "void (*)(int)", env);

        assert_type!("foo && bar", "int", env);
        assert_type!("foo >= bar", "int", env);
        assert_type!("foo != bar", "int", env);
        assert_type!("!bar", "int", env);
        assert_type!("(int (*)())1", "int (*)(void)", env);

        assert_type_err!("foo - baz", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("foo + baz", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("foo * baz", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("foo * 1", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("1 - foo", ErrorKind::InvalidBinary(..), env);
        assert_type_err!("(int *())a", ErrorKind::InvalidExplicitCast(..), env);
        assert_type_err!("~foo", ErrorKind::InvalidUnary(..), env);
        assert_type_err!("foo--", ErrorKind::NotAssignable(..), env);
        assert_type_err!("*baz = 1", ErrorKind::NotAssignable(..), env);

        // WARN: doesnt catch this because `foo[3]` is syntax sugar for `*(foo + 3)`
        // and the latter doesn't error
        // assert_type_err!("foo[3]",ErrorKind::InvalidSubscript(..),env);
    }

    #[test]
    fn static_constant_test() {
        assert_const_expr!("&a + (int)(3 * 1)", true, "int a;");

        assert_const_expr!("a + (int)(3 * 1)", false, "int *a;");
        assert_const_expr!("\"hi\" + (int)(3 * 1)", true, "");
        assert_const_expr!("&\"hi\" + (int)(3 * 1)", true, "");

        assert_const_expr!("(long*)&a", true, "int a;");

        assert_const_expr!("(long*)1 + 3", true, "");

        assert_const_expr!("&a[3]", true, "int a[4];");

        assert_const_expr!("*&a[3]", false, "int a[4];");

        assert_const_expr!("&a.age", true, "struct { int age; } a;");

        assert_const_expr!("a.age", false, "struct { int age; } a;");
        assert_const_expr!("*a", false, "int* a;");

        assert_const_expr!("(int *)*a", false, "int* a;");

        assert_const_expr!("*a", true, "int a[4][4];");
        assert_const_expr!("*&a[3]", true, "int a[4][4];");

        assert_const_expr!("&a->age", true, "struct { int age; } a[4];");

        assert_const_expr!("a", false, "int a;");
    }

    #[test]
    fn alignes_stack1() {
        let offset = 12;
        let result = align_by(offset, 8);

        assert_eq!(result, 16);
    }
    #[test]
    fn alignes_stack2() {
        let offset = 9;
        let result = align_by(offset, 4);

        assert_eq!(result, 12);
    }
    #[test]
    fn alignes_stackpointer1() {
        let offset = 31;
        let result = align_by(offset, 16);

        assert_eq!(result, 32);
    }
    #[test]
    fn alignes_stackpointer2() {
        let offset = 5;
        let result = align_by(offset, 16);

        assert_eq!(result, 16);
    }
    #[test]
    fn finds_nested_loop() {
        let mut scopes = vec![
            ScopeKind::Loop,
            ScopeKind::Switch(
                QualType::new(Type::Primitive(Primitive::Int(false))),
                Rc::new(RefCell::new(Vec::new())),
            ),
            ScopeKind::Switch(
                QualType::new(Type::Primitive(Primitive::Int(false))),
                Rc::new(RefCell::new(Vec::new())),
            ),
        ];
        let actual = find_scope!(scopes, ScopeKind::Loop).is_some();

        assert!(actual);
    }
    #[test]
    fn doesnt_find_switch() {
        let mut scopes = vec![ScopeKind::Loop, ScopeKind::Loop];
        let actual = find_scope!(scopes, ScopeKind::Switch(..)).is_some();
        let expected = false;

        assert_eq!(actual, expected);
    }
    #[test]
    fn finds_and_mutates_scope() {
        let mut scopes = vec![
            ScopeKind::Loop,
            ScopeKind::Switch(
                QualType::new(Type::Primitive(Primitive::Int(false))),
                Rc::new(RefCell::new(Vec::new())),
            ),
            ScopeKind::Switch(
                QualType::new(Type::Primitive(Primitive::Int(true))),
                Rc::new(RefCell::new(Vec::new())),
            ),
            ScopeKind::Loop,
        ];
        let expected = vec![
            ScopeKind::Loop,
            ScopeKind::Switch(
                QualType::new(Type::Primitive(Primitive::Int(false))),
                Rc::new(RefCell::new(Vec::new())),
            ),
            ScopeKind::Switch(
                QualType::new(Type::Primitive(Primitive::Int(true))),
                Rc::new(RefCell::new(vec![
                    CaseKind::Case(LiteralKind::Unsigned(1)),
                    CaseKind::Default,
                    CaseKind::Case(LiteralKind::Unsigned(3)),
                ])),
            ),
            ScopeKind::Loop,
        ];
        let ScopeKind::Switch(_,labels) =
            find_scope!(scopes, ScopeKind::Switch(..)).unwrap() else {unreachable!()};
        labels.borrow_mut().push(CaseKind::Case(LiteralKind::Unsigned(1)));
        labels.borrow_mut().push(CaseKind::Default);
        labels.borrow_mut().push(CaseKind::Case(LiteralKind::Unsigned(3)));

        assert_eq!(scopes, expected);
    }

    #[test]
    fn array_init_list() {
        let actual = setup_init_list("short a[3] = {1,2};").unwrap();
        let expected = vec![(0, "1", "short"), (2, "2", "short")];

        assert_init(actual, expected);
    }
    #[test]
    fn union_init() {
        let actual = setup_init_list(
            r#"union Foo {
                long n;
                int s[3];
            } a = {3,.s = 1,2};"#,
        )
        .unwrap();
        let expected = vec![(0, "1", "int"), (4, "2", "int")];

        assert_init(actual, expected);
    }
    #[test]
    fn union_overflow() {
        let actual = setup_init_list(
            r#"union Foo {
                long n;
                int s[3];
            } a = {3,.s[2] = 1,2};"#,
        );

        assert!(matches!(
            actual,
            Err(Error {
                kind: ErrorKind::InitializerOverflow(QualType { ty: Type::Union(_), .. }),
                ..
            })
        ));
    }

    #[test]
    fn struct_string_init() {
        let actual = setup_init_list(
            r#"struct Foo {
                char name[5];
                int* self;
            } a = {"hei"};"#,
        )
        .unwrap();
        let expected = vec![
            (0, "'h'", "char"),
            (1, "'e'", "char"),
            (2, "'i'", "char"),
            (3, "'\\0'", "char"),
        ];

        assert_init(actual, expected);
    }

    #[test]
    fn multidimensional_array() {
        let actual = setup_init_list("int a[2][3] = {{1},1,2};").unwrap();
        let expected = vec![(0, "1", "int"), (12, "1", "int"), (16, "2", "int")];

        assert_init(actual, expected);
    }

    #[test]
    fn nested_arr_struct_init() {
        let actual = setup_init_list(
            r#"struct Foo {
                struct Bar {
                    int age;
                    long number[3];
                } other[2];
                int arr[3];
            } a = {{1,2,[1].age = 21,[1].number[1] = 3,4},.arr = {1,[2] = 2}};"#,
        )
        .unwrap();
        let expected = vec![
            (0, "1", "int"),
            (4, "2", "long"),
            (28, "21", "int"),
            (40, "3", "long"),
            (48, "4", "long"),
            (56, "1", "int"),
            (64, "2", "int"),
        ];

        assert_init(actual, expected);
    }

    #[test]
    fn nested_struct_string_init() {
        let actual = setup_init_list(
            r#"struct Foo {
                char c;
                char name[3];
                int arr[2];
            } a = {2,"me",{1,[0] = 2,4}};"#,
        )
        .unwrap();
        let expected = vec![
            (0, "2", "char"),
            (1, "'m'", "char"),
            (2, "'e'", "char"),
            (3, "'\\0'", "char"),
            (4, "2", "int"),
            (8, "4", "int"),
        ];

        assert_init(actual, expected);
    }
    #[test]
    fn nested_union_designators() {
        let actual = setup_init_list(
            "struct Outer {
                struct {
                  char s[2];
                  union {
                    long n;
                    char arr[3];
                  } inner_union;
                } inner_struct;
              } a = {.inner_struct.inner_union.arr = '1', '3'};",
        )
        .unwrap();
        let expected = vec![(2, "'1'", "char"), (3, "'3'", "char")];

        assert_init(actual, expected);
    }
    #[test]
    fn scalar_designator_overflow() {
        let actual = setup_init_list(
            "struct Outer {
                struct {
                  char s[2];
                  union {
                    long n;
                    char arr[3];
                  } inner_union;
                } inner_struct;
              } a = {.inner_struct.inner_union.arr[0] = {1, 3}};",
        );

        assert!(matches!(
            actual,
            Err(Error { kind: ErrorKind::ScalarOverflow, .. })
        ));
    }
    #[test]
    fn array_size_overflow() {
        let actual_overflow = setup_init_list("int arr[2305843009213693952];");
        assert!(matches!(
            actual_overflow,
            Err(Error { kind: ErrorKind::ArraySizeOverflow, .. })
        ));

        let actual_no_overflow = setup_init_list("int arr[2305843009213693951] = {0};");
        assert!(actual_no_overflow.is_ok());
    }
    #[test]
    fn partial_nested_arr_override() {
        let actual = setup_init_list(
            "struct Outer {
                struct {
                  char s[2];
                  union {
                    long n;
                    char arr[3];
                  } inner_union;
                } inner_struct;
              } a = {.inner_struct.inner_union.arr = 1, 3,.inner_struct.inner_union.arr[1] = 5};",
        )
        .unwrap();
        let expected = vec![(2, "1", "char"), (3, "5", "char")];

        assert_init(actual, expected);
    }
    #[test]
    fn partial_union_override() {
        let actual = setup_init_list(
            "struct Outer {
                struct {
                  char s[2];
                  union {
                    long n;
                    char arr[3];
                  } inner_union;
                } inner_struct;
              } a = {.inner_struct.inner_union.arr = {1, 3},.inner_struct.inner_union.n = 5,
                     .inner_struct.inner_union.arr[1] = 8};",
        )
        .unwrap();
        let expected = vec![(3, "8", "char")];

        assert_init(actual, expected);
    }
    #[test]
    fn partial_aggr_override() {
        // also happens on structs
        let actual = setup_init_list(
            "union Foo {
                int arr[3];
                long n;
              } my_union = {{1, 2}, .arr = 3};",
        )
        .unwrap();
        let expected = vec![(0, "3", "int"), (4, "2", "int")];

        assert_init(actual, expected);
    }

    #[test]
    fn unsized_array() {
        let actual = setup_init_list("int a[] = {1,2,3};").unwrap();
        let expected = vec![(0, "1", "int"), (4, "2", "int"), (8, "3", "int")];

        assert_init(actual, expected);
    }

    #[test]
    fn unsized_array_string() {
        let actual = setup_init_list("char s[] = \"foo\";").unwrap();
        let expected = vec![
            (0, "'f'", "char"),
            (1, "'o'", "char"),
            (2, "'o'", "char"),
            (3, "'\0'", "char"),
        ];

        assert_init(actual, expected);
    }

    #[test]
    fn nested_unsized_array() {
        let actual = setup_init_list("int s[][2] = {{1,2},1,2,{4},6};").unwrap();
        let expected = vec![
            (0, "1", "int"),
            (4, "2", "int"),
            (8, "1", "int"),
            (12, "2", "int"),
            (16, "4", "int"),
            (24, "6", "int"),
        ];

        assert_init(actual, expected);
    }

    #[test]
    fn nested_unsized_array_overflow() {
        let actual = setup_init_list("long s[][2] = {{1,2},1,{2,3},4};");

        assert!(matches!(
            actual,
            Err(Error { kind: ErrorKind::ScalarOverflow, .. })
        ));
    }

    #[test]
    fn invalid_storage_classes() {
        let actual = typecheck(
            "
auto int a();
auto struct B foo;
register char* foo;
extern int more = 4;
int func();

int main(){
    extern int some = 4;
    register int b();
    static int bar();
    static int array[] = {func()};

    extern int boo();
    auto int c;
    int other;
    register int d;
}
",
        )
        .unwrap_err();

        assert!(matches!(
            actual
                .into_iter()
                .map(|e| e.kind)
                .collect::<Vec<ErrorKind>>()
                .as_slice(),
            &[
                ErrorKind::InvalidStorageClass(mir::decl::StorageClass::Auto, "function"),
                ErrorKind::InvalidStorageClass(mir::decl::StorageClass::Auto, "global variable"),
                ErrorKind::InvalidStorageClass(mir::decl::StorageClass::Register, "global variable"),
                ErrorKind::Regular("variable declared with 'extern' cannot have initializer"),
                ErrorKind::Regular("variable declared with 'extern' cannot have initializer"),
                ErrorKind::InvalidStorageClass(mir::decl::StorageClass::Register, "function"),
                ErrorKind::Regular(
                    "function declared in block scope cannot have 'static' storage-class"
                ),
                ErrorKind::NotConstantInit("static variables")
            ]
        ));
    }

    #[test]
    fn allowed_tentative_storage_classes() {
        let actual = typecheck(
            "
extern void a;
struct Foo some;
int array[];

int main() {
    extern void c;
    extern union Bar u;
}

struct Foo {
    int age;
};
",
        );

        assert!(actual.is_ok());
    }
    #[test]
    fn invalid_tentative_storage_classes() {
        let actual = typecheck(
            "
extern void a;
void a;

struct Bar b;

int func(char*, ...);

int main(){
    struct Foo some;
    func(\"print\",some);
}
    ",
        )
        .unwrap_err();

        assert!(matches!(
            actual.as_slice(),
            &[
                Error {
                    kind: ErrorKind::IncompleteType(QualType {
                        ty: Type::Primitive(Primitive::Void),
                        ..
                    }),
                    line_index: 3,
                    ..
                },
                Error {
                    kind: ErrorKind::IncompleteType(QualType { ty: Type::Struct(_), .. }),
                    ..
                },
                Error {
                    kind: ErrorKind::IncompleteArgType(1, QualType { ty: Type::Struct(_), .. }),
                    ..
                },
                Error {
                    kind: ErrorKind::IncompleteTentative(QualType { ty: Type::Struct(_), .. }),
                    line_index: 5,
                    ..
                }
            ]
        ));
    }
    #[test]
    fn inline() {
        let actual = typecheck(
            "
inline static foo();
inline int bar;

int main() {
    extern inline char goo(inline some);

    inline char zoo();
    char zoo();

    typedef inline boo(void);
}
",
        )
        .unwrap_err();

        assert!(matches!(
            actual.as_slice(),
            &[
                Error {
                    kind: ErrorKind::Regular(..),
                    line_index: 3,
                    ..
                },
                Error {
                    kind: ErrorKind::Regular("cannot have 'inline' on function parameters"),
                    line_index: 6,
                    ..
                },
                Error {
                    kind: ErrorKind::Regular("'inline' not allowed with 'typedef' storage-class"),
                    ..
                },
            ]
        ));
    }
    #[test]
    fn missing_goto() {
        let actual = typecheck(
            "
int foo(){
    char c = &1;
    goto b;
    int *p = c;
}
        ",
        )
        .unwrap_err();

        assert!(matches!(
            actual.as_slice(),
            &[
                Error { kind: ErrorKind::NotLvalue(..), .. },
                Error { kind: ErrorKind::IllegalAssign(..), .. },
                Error { kind: ErrorKind::UndeclaredLabel(..), .. },
            ]
        ));
    }
    #[test]
    fn const_array_assign() {
        let actual = typecheck(
            "
int main() {
    typedef int A[2][3];
    const A a = {{4, 5, 6}, {7, 8, 9}};
    int *pi = a[0];
}
",
        )
        .unwrap_err();

        assert!(matches!(
            actual.as_slice(),
            &[Error {
                kind: ErrorKind::IllegalAssign(..),
                line_index: 5,
                ..
            },]
        ));
    }
    #[test]
    fn restrict_qualifier() {
        let actual = typecheck(
            "
int main() {
  restrict int *sig;
  int (*restrict f0)(void);
  int (**restrict f1)(void); // fine
}
",
        )
        .unwrap_err();
        assert!(matches!(
            actual.as_slice(),
            &[
                Error {
                    kind: ErrorKind::InvalidRestrict(..),
                    line_index: 3,
                    ..
                },
                Error {
                    kind: ErrorKind::InvalidRestrict(..),
                    line_index: 4,
                    ..
                }
            ]
        ));
    }
}
