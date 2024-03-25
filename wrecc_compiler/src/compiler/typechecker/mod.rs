pub mod mir;

use crate::compiler::codegen::align;
use crate::compiler::codegen::register::*;
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::parser::hir;

use self::mir::decl::{CaseKind, ScopeKind};
use self::mir::expr::{CastDirection, ValueKind};
use crate::find_scope;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

pub struct TypeChecker {
    // TODO: shouldn't be public
    // symbol table
    pub env: Environment,

    // label with its associated label index
    const_labels: HashMap<String, usize>,

    // label index counter
    const_label_count: usize,
}

// Converts hir-parsetree to type-annotated mir-ast. Also does typechecking and semantic analysis
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
    ) -> Result<(Vec<mir::decl::ExternalDeclaration>, HashMap<String, usize>), Vec<Error>> {
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
            hir::decl::ExternalDeclaration::Function(decl_type, name, body) => {
                self.function_definition(decl_type, name, body)
            }
        }
    }

    fn declaration(
        &mut self,
        decl: hir::decl::Declaration,
        mut func: Option<&mut mir::decl::Function>,
    ) -> Result<Vec<mir::decl::Declarator>, Error> {
        let mut declarators = Vec::new();
        let specifier_type = self.parse_specifiers(decl.specifiers.clone())?;

        for declarator in decl.declarators {
            if let Some(d) =
                self.declarator(specifier_type.clone(), decl.is_typedef, declarator, &mut func)?
            {
                declarators.push(d);
            }
        }

        Ok(declarators)
    }
    fn declarator(
        &mut self,
        specifier_type: Type,
        is_typedef: bool,
        (declarator, init): (hir::decl::Declarator, Option<hir::decl::Init>),
        func: &mut Option<&mut mir::decl::Function>,
    ) -> Result<Option<mir::decl::Declarator>, Error> {
        let parsed_type = self.parse_modifiers(specifier_type, declarator.modifiers)?;

        if let Some(name) = declarator.name {
            let symbol = if is_typedef {
                Symbols::TypeDef(parsed_type.clone())
            } else {
                Symbols::Variable(SymbolInfo {
                    kind: if init.is_some() {
                        InitType::Definition
                    } else {
                        InitType::Declaration
                    },
                    token: name.clone(),
                    type_decl: parsed_type.clone(),
                    // since global variable declarations can be used before initialization already
                    // insert its register.
                    // also have to insert function-labels otherwise their registers are never filled,
                    // since they are ignored in codegen.
                    reg: if self.env.is_global() || parsed_type.is_func() {
                        Some(Register::Label(LabelRegister::Var(
                            name.unwrap_string(),
                            parsed_type.clone(),
                        )))
                    } else {
                        None
                    },
                })
            };

            let entry = self.env.declare_symbol(&name, symbol)?;

            return match (&*entry.borrow(), init) {
                (Symbols::Variable(_), init) if parsed_type.is_func() => {
                    if init.is_some() {
                        return Err(Error::new(
                            &name,
                            ErrorKind::Regular("only variables can be initialized"),
                        ));
                    }
                    // function declarations don't need any codegen
                    Ok(None)
                }
                (Symbols::Variable(_), Some(init)) => {
                    if !parsed_type.is_complete() {
                        return Err(Error::new(&name, ErrorKind::IncompleteType(parsed_type)));
                    }
                    let init = self.init_check(func, &parsed_type, init)?;

                    if let Some(func) = func {
                        func.increment_stack_size(&parsed_type);
                    }

                    Ok(Some(mir::decl::Declarator {
                        name,
                        entry: Rc::clone(&entry),
                        init: Some(init),
                    }))
                }
                (Symbols::Variable(_), None) => {
                    let tentative_decl = self.env.is_global() && parsed_type.is_aggregate();
                    if !parsed_type.is_complete() && !tentative_decl {
                        return Err(Error::new(&name, ErrorKind::IncompleteType(parsed_type)));
                    }
                    if let Some(func) = func {
                        func.increment_stack_size(&parsed_type);
                    }

                    Ok(Some(mir::decl::Declarator {
                        name,
                        entry: Rc::clone(&entry),
                        init: None,
                    }))
                }
                (_, Some(_)) => Err(Error::new(
                    &name,
                    ErrorKind::Regular("only variables can be initialized"),
                )),
                _ => Ok(None),
            };
        } else {
            Ok(None)
        }
    }
    pub fn parse_type(&mut self, decl_type: hir::decl::DeclType) -> Result<Type, Error> {
        let specifier_type = self.parse_specifiers(decl_type.specifiers)?;
        let parsed_type = self.parse_modifiers(specifier_type, decl_type.modifiers)?;

        Ok(parsed_type)
    }
    fn parse_specifiers(&mut self, specifiers: Vec<hir::decl::DeclSpecifier>) -> Result<Type, Error> {
        if specifiers.is_empty() {
            // WARN: since C99 this should at least issue a warning
            return Ok(Type::Primitive(Primitive::Int));
        }

        let token = specifiers[0].token.clone();

        let mut specifier_kind_list: Vec<hir::decl::SpecifierKind> =
            specifiers.into_iter().map(|spec| spec.kind).collect();

        specifier_kind_list.sort_by(|s1, s2| s2.order().cmp(&s1.order()));

        match specifier_kind_list.as_slice() {
            [hir::decl::SpecifierKind::Struct(name, members)]
            | [hir::decl::SpecifierKind::Union(name, members)] => {
                self.struct_or_union_specifier(token, name, members)
            }
            [hir::decl::SpecifierKind::Enum(name, enum_constants)] => {
                self.enum_specifier(token, name, enum_constants)
            }
            [hir::decl::SpecifierKind::UserType] => self.env.get_symbol(&token).and_then(|symbol| {
                if let Symbols::TypeDef(type_decl) = symbol.borrow().clone() {
                    Ok(type_decl)
                } else {
                    Err(Error::new(
                        &token,
                        ErrorKind::InvalidSymbol(token.unwrap_string(), "user-type"),
                    ))
                }
            }),

            [hir::decl::SpecifierKind::Void] => Ok(Type::Primitive(Primitive::Void)),
            [hir::decl::SpecifierKind::Char] => Ok(Type::Primitive(Primitive::Char)),
            [hir::decl::SpecifierKind::Int] => Ok(Type::Primitive(Primitive::Int)),
            [hir::decl::SpecifierKind::Long]
            | [hir::decl::SpecifierKind::Long, hir::decl::SpecifierKind::Int]
            | [hir::decl::SpecifierKind::Long, hir::decl::SpecifierKind::Long]
            | [hir::decl::SpecifierKind::Long, hir::decl::SpecifierKind::Long, hir::decl::SpecifierKind::Int] => {
                Ok(Type::Primitive(Primitive::Long))
            }
            _ => Err(Error::new(
                &token,
                ErrorKind::Regular("invalid combination of type-specifiers"),
            )),
        }
    }
    fn parse_modifiers(
        &mut self,
        mut parsed_type: Type,
        modifiers: Vec<hir::decl::DeclModifier>,
    ) -> Result<Type, Error> {
        for m in modifiers {
            parsed_type = match m {
                hir::decl::DeclModifier::Pointer => parsed_type.pointer_to(),
                hir::decl::DeclModifier::Array(token, mut expr) => {
                    let size = expr.get_literal_constant(self, &token, "Array size specifier")?;

                    if parsed_type.is_func() {
                        return Err(Error::new(&token, ErrorKind::InvalidArray(parsed_type)));
                    }

                    if size > 0 {
                        parsed_type.array_of(size as usize)
                    } else {
                        return Err(Error::new(&token, ErrorKind::NegativeArraySize));
                    }
                }
                hir::decl::DeclModifier::Function { token, params, variadic } => {
                    // func-params have own scope (their types too)
                    self.env.enter();
                    let params = self
                        .parse_params(&token, params)?
                        .into_iter()
                        .map(|(type_decl, _)| type_decl)
                        .collect();
                    self.env.exit();

                    if parsed_type.is_func() || parsed_type.is_array() {
                        return Err(Error::new(&token, ErrorKind::InvalidReturnType(parsed_type)));
                    }

                    parsed_type.function_of(params, variadic)
                }
            };
        }

        Ok(parsed_type)
    }
    fn struct_or_union_specifier(
        &mut self,
        token: Token,
        name: &Option<Token>,
        members: &Option<Vec<hir::decl::MemberDeclaration>>,
    ) -> Result<Type, Error> {
        let members = match (&name, members) {
            (Some(name), Some(members)) => {
                let custom_type = self
                    .env
                    .declare_type(name, Tags::Aggregate(StructRef::new(token.clone().kind, true)))?;

                let members = self.struct_declaration(members.clone())?;

                if let Tags::Aggregate(struct_ref) = &*custom_type.borrow_mut() {
                    struct_ref.update(members);
                }
                let members = custom_type.borrow().clone().unwrap_aggr();

                StructInfo::Named(name.unwrap_string(), members)
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

                StructInfo::Named(name.unwrap_string(), members)
            }
            (None, Some(members)) => {
                let members = self.struct_declaration(members.clone())?;
                StructInfo::Unnamed(token.clone(), members)
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
        members: Vec<hir::decl::MemberDeclaration>,
    ) -> Result<Vec<(Type, Token)>, Error> {
        let mut parsed_members = Vec::new();

        for (spec, declarators) in members {
            let specifier_type = self.parse_specifiers(spec)?;

            for hir::decl::MemberDeclarator { name, modifiers } in declarators {
                let parsed_type = self.parse_modifiers(specifier_type.clone(), modifiers)?;

                if !parsed_type.is_complete() {
                    return Err(Error::new(&name, ErrorKind::IncompleteType(parsed_type)));
                }
                if parsed_type.is_func() {
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
    fn check_duplicate_members(vec: &Vec<(Type, Token)>) -> Result<(), Error> {
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
        let mut index: i32 = 0;

        for (name, init) in constants {
            if let Some(mut init_expr) = init {
                index = init_expr.get_literal_constant(self, &name, "Enum Constant")? as i32;
            }

            // insert enum constant into symbol table
            self.env.declare_symbol(
                &name,
                Symbols::Variable(SymbolInfo {
                    token: name.clone(),
                    type_decl: Type::Primitive(Primitive::Int),
                    kind: InitType::Definition,
                    reg: Some(Register::Literal(index as i64, Type::Primitive(Primitive::Int))),
                }),
            )?;

            parsed_constants.push((name.clone(), index));

            if let Some(inc) = index.checked_add(1) {
                index = inc;
            } else {
                return Err(Error::new(&name, ErrorKind::EnumOverflow));
            }
        }

        Ok(parsed_constants)
    }
    fn parse_params(
        &mut self,
        token: &Token,
        params: Vec<(Vec<hir::decl::DeclSpecifier>, hir::decl::Declarator)>,
    ) -> Result<Vec<(Type, Option<(Token, VarSymbol)>)>, Error> {
        let mut parsed_params = Vec::new();

        for (specifiers, declarator) in params {
            let specifier_type = self.parse_specifiers(specifiers.clone())?;
            let mut parsed_type = self.parse_modifiers(specifier_type, declarator.modifiers)?;

            parsed_type = match parsed_type {
                Type::Array { of, .. } => of.pointer_to(),
                Type::Function { .. } => parsed_type.pointer_to(),
                ty => ty,
            };

            let name = if let Some(name) = declarator.name {
                let symbol = self.env.declare_symbol(
                    &name,
                    Symbols::Variable(SymbolInfo {
                        token: name.clone(),
                        type_decl: parsed_type.clone(),
                        kind: InitType::Declaration,
                        reg: None,
                    }),
                )?;

                Some((name, symbol))
            } else {
                None
            };

            parsed_params.push((parsed_type, name));
        }

        // single unnamed void param is equivalent to empty params
        if let [(Type::Primitive(Primitive::Void), None)] = parsed_params.as_slice() {
            parsed_params.pop();
        } else if parsed_params.iter().any(|(type_decl, _)| type_decl.is_void()) {
            return Err(Error::new(token, ErrorKind::VoidFuncArg));
        }

        Ok(parsed_params)
    }

    fn init_check(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        type_decl: &Type,
        mut init: hir::decl::Init,
    ) -> Result<mir::decl::Init, Error> {
        if let Some((amount, s)) = Self::is_string_init(type_decl, &init)? {
            init.kind = Self::char_array(init.token.clone(), s, amount)?;
        }

        match init.kind {
            hir::decl::InitKind::Scalar(expr) => self.init_scalar(func, type_decl, &init.token, expr),
            hir::decl::InitKind::Aggr(list) => self.init_aggregate(func, type_decl, init.token, list),
        }
    }
    fn init_scalar(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        type_decl: &Type,
        token: &Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::decl::Init, Error> {
        let expr = self.visit_expr(func, expr)?;

        let expr = expr.decay();
        Self::check_type_compatibility(token, type_decl, &expr)?;
        let expr = Self::maybe_cast(type_decl.clone(), expr);

        if self.env.is_global() && !expr.is_constant() {
            return Err(Error::new(token, ErrorKind::NotConstantInit("Global variables")));
        }

        Ok(mir::decl::Init::Scalar(expr))
    }
    fn init_aggregate(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        type_decl: &Type,
        token: Token,
        mut list: Vec<Box<hir::decl::Init>>,
    ) -> Result<mir::decl::Init, Error> {
        match type_decl {
            Type::Array { .. } | Type::Struct(_) | Type::Union(_) => {
                let mut new_list = Vec::new();
                let mut objects = CurrentObjects::new(type_decl.clone());

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
                    let mut sub_type = objects.current_type();
                    if let hir::decl::InitKind::Scalar(expr) = first.kind.clone() {
                        // placeholder expression
                        let left = mir::expr::Expr {
                            kind: mir::expr::ExprKind::Nop,
                            type_decl: sub_type.clone(),
                            value_kind: ValueKind::Lvalue,
                        };
                        let right = self.visit_expr(func, expr)?;

                        while !sub_type.is_scalar()
                            && Self::is_string_init(sub_type, first)?.is_none()
                            && self
                                .assign_var(left.clone(), token.clone(), right.clone())
                                .is_err()
                        {
                            let new_sub_type = objects.current_type().at(0).unwrap();
                            objects.0.push((0, 0, new_sub_type));

                            sub_type = objects.current_type();
                        }
                    }

                    let init = self.init_check(func, sub_type, *list.remove(0))?;
                    let init_offset = objects.offset();

                    // remove overriding elements
                    let init_interval = if let Some((offset, size)) = objects.find_same_union(&new_list)
                    {
                        offset..offset + size as i64
                    } else {
                        init_offset..init_offset + sub_type.size() as i64
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
                    objects.update_current();
                }

                new_list.sort_by(|(.., offset1), (.., offset2)| offset1.cmp(&offset2));
                Ok(mir::decl::Init::Aggr(
                    new_list
                        .into_iter()
                        .map(|(_, expr, offset)| (expr, offset as usize))
                        .collect(),
                ))
            }
            _ => match list.as_slice() {
                [single_init] if matches!(single_init.kind, hir::decl::InitKind::Scalar(_)) => {
                    self.init_check(func, type_decl, *single_init.clone())
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
        type_decl: &Type,
        designator: hir::decl::Designator,
    ) -> Result<(i64, i64, Type), Error> {
        match (designator.kind, type_decl) {
            (hir::decl::DesignatorKind::Array(mut expr), Type::Array { amount, of }) => {
                let literal = expr.get_literal_constant(self, &designator.token, "Array designator")?;
                if literal < 0 {
                    return Err(Error::new(
                        &designator.token,
                        ErrorKind::Regular("array designator must be positive number"),
                    ));
                }

                if literal >= *amount as i64 {
                    Err(Error::new(
                        &designator.token,
                        ErrorKind::DesignatorOverflow(*amount, literal),
                    ))
                } else {
                    Ok((literal, literal, *of.clone()))
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
                ErrorKind::InvalidArrayDesignator(type_decl.clone()),
            )),
            (hir::decl::DesignatorKind::Member(m), Type::Struct(s) | Type::Union(s)) => {
                if let Some(i) = s
                    .members()
                    .iter()
                    .position(|(_, m_token)| *m == m_token.unwrap_string())
                {
                    // unions only have single index
                    if let Type::Union(_) = type_decl {
                        Ok((0, i as i64, s.member_type(&m)))
                    } else {
                        Ok((i as i64, i as i64, s.member_type(&m)))
                    }
                } else {
                    Err(Error::new(
                        &designator.token,
                        ErrorKind::NonExistantMember(m.clone(), type_decl.clone()),
                    ))
                }
            }

            (..) => Err(Error::new(
                &designator.token,
                ErrorKind::NonAggregateDesignator(type_decl.clone()),
            )),
        }
    }
    // detects if char-array is initialized with a string
    // both valid:
    // - char arr[4] = "foo";
    // - char arr[4] = {"foo"};
    fn is_string_init(
        type_decl: &Type,
        init: &hir::decl::Init,
    ) -> Result<Option<(usize, String)>, Error> {
        if let Some(amount) = type_decl.is_char_array() {
            match &init.kind {
                hir::decl::InitKind::Scalar(hir::expr::ExprKind::String(s)) => {
                    return Ok(Some((amount, s.unwrap_string())))
                }
                hir::decl::InitKind::Aggr(list) => match list.as_slice() {
                    [single_init] if single_init.designator.is_none() => {
                        if let hir::decl::InitKind::Scalar(hir::expr::ExprKind::String(s)) =
                            &single_init.kind
                        {
                            return Ok(Some((amount, s.unwrap_string())));
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
    fn char_array(token: Token, mut s: String, amount: usize) -> Result<hir::decl::InitKind, Error> {
        // char s[] = "abc" identical to char s[] = {'a','b','c','\0'} (6.7.8)
        if amount < s.len() {
            return Err(Error::new(
                &token,
                ErrorKind::TooLong("initializer-string", amount, s.len()),
            ));
        }
        let mut diff = amount - s.len();
        while diff > 0 {
            diff -= 1;
            s.push('\0'); // append implicit NULL terminator to string
        }

        Ok(hir::decl::InitKind::Aggr(
            s.as_bytes()
                .iter()
                .map(|c| {
                    Box::new(hir::decl::Init {
                        token: token.clone(),
                        kind: hir::decl::InitKind::Scalar(hir::expr::ExprKind::Literal(
                            *c as i64,
                            Type::Primitive(Primitive::Char),
                        )),
                        designator: None,
                    })
                })
                .collect(),
        ))
    }

    fn function_definition(
        &mut self,
        mut decl_type: hir::decl::DeclType,
        name: Token,
        body: Vec<hir::stmt::Stmt>,
    ) -> Result<mir::decl::ExternalDeclaration, Error> {
        let name_string = name.unwrap_string();

        // have to pop of last modifier first so that params can have other scope than return type
        let Some(hir::decl::DeclModifier::Function { params, variadic,token }) = decl_type.modifiers.pop() else {
            unreachable!("last modifier has to be function to be func-def");
        };
        let return_type = self.parse_type(decl_type)?;

        if return_type.is_func() || return_type.is_array() {
            return Err(Error::new(&token, ErrorKind::InvalidReturnType(return_type)));
        }

        if !return_type.is_complete() && !return_type.is_void() {
            return Err(Error::new(
                &name,
                ErrorKind::IncompleteReturnType(name_string, return_type),
            ));
        }

        // have to push scope before declaring local variables
        self.env.enter();

        let params = self.parse_params(&token, params)?;

        let mut func = mir::decl::Function::new(name_string.clone(), return_type.clone(), variadic);

        let type_decl = Type::Function(FuncType {
            return_type: Box::new(return_type),
            params: params.iter().map(|(ty, _)| ty.clone()).collect(),
            variadic,
        });
        self.env.declare_global(
            &name,
            Symbols::Variable(SymbolInfo {
                type_decl: type_decl.clone(),
                kind: InitType::Definition,
                reg: Some(Register::Label(LabelRegister::Var(
                    name_string.clone(),
                    type_decl,
                ))),
                token: name.clone(),
            }),
        )?;

        for (type_decl, param_name) in params.into_iter() {
            if !type_decl.is_complete() {
                return Err(Error::new(
                    &name,
                    ErrorKind::IncompleteFuncArg(name_string, type_decl),
                ));
            }
            if let Some((_, var_symbol)) = param_name {
                func.increment_stack_size(&type_decl);

                func.params.push(var_symbol);
            } else {
                return Err(Error::new(&name, ErrorKind::UnnamedFuncParams));
            }
        }

        // check function body
        let body = self.block(&mut func, body);

        func.compare_gotos()?;

        let mir::stmt::Stmt::Block(mut body) = body? else {unreachable!()};

        func.main_return(&name, &mut body)?;

        if !func.return_type.is_void() && !func.returns_all_paths {
            func.returns_all_paths = false;

            Err(Error::new(&name, ErrorKind::NoReturnAllPaths(name_string)))
        } else {
            func.returns_all_paths = false;

            Ok(mir::decl::ExternalDeclaration::Function(func, body))
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
        if !cond.type_decl.is_integer() {
            return Err(Error::new(
                &token,
                ErrorKind::NotInteger("switch conditional", cond.type_decl),
            ));
        }
        func.scope.push(ScopeKind::Switch(Vec::new()));
        let stmt = self.visit_stmt(func, body);

        let Some(ScopeKind::Switch(labels)) = func.scope.pop() else {
            unreachable!("all other scopes should be popped off by themselves")
        };

        func.switches.push_back(labels);

        Ok(mir::stmt::Stmt::Switch(cond, Box::new(stmt?)))
    }
    fn case_statement(
        &mut self,
        func: &mut mir::decl::Function,
        token: Token,
        mut value: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let value = value.get_literal_constant(self, &token, "case value")?;

        match find_scope!(&mut func.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(labels)) => {
                if !labels.contains(&CaseKind::Case(value)) {
                    labels.push(CaseKind::Case(value))
                } else {
                    return Err(Error::new(&token, ErrorKind::DuplicateCase(value)));
                }
            }
            _ => {
                return Err(Error::new(&token, ErrorKind::NotIn("case", "switch")));
            }
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
        match find_scope!(&mut func.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(labels)) => {
                if !labels.contains(&CaseKind::Default) {
                    labels.push(CaseKind::Default)
                } else {
                    return Err(Error::new(&token, ErrorKind::MultipleDefaults));
                }
            }
            _ => {
                return Err(Error::new(&token, ErrorKind::NotIn("default", "switch")));
            }
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
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::NotScalar("conditional", cond.type_decl),
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

        let init = init.map(|init| self.visit_stmt(func, *init)).transpose()?;

        let cond = if let Some(cond) = cond {
            let cond = self.visit_expr(&mut Some(func), cond)?;
            if !cond.type_decl.is_scalar() {
                return Err(Error::new(
                    &left_paren,
                    ErrorKind::NotScalar("conditional", cond.type_decl),
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
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &left_paren,
                ErrorKind::NotScalar("conditional", cond.type_decl),
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
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &keyword,
                ErrorKind::NotScalar("conditional", cond.type_decl),
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

            let expr = expr.decay();
            if !func.return_type.type_compatible(&expr.type_decl, &expr) {
                return Err(Error::new(
                    &keyword,
                    ErrorKind::MismatchedFunctionReturn(func.return_type.clone(), expr.type_decl),
                ));
            }
            let expr = Self::maybe_cast(func.return_type.clone(), expr);

            Some(expr)
        } else {
            let return_type = Type::Primitive(Primitive::Void);
            let return_expr = hir::expr::ExprKind::Nop;

            if !func.return_type.type_compatible(&return_type, &return_expr) {
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
        mut parse_tree: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        parse_tree.integer_const_fold(self)?;

        match parse_tree {
            hir::expr::ExprKind::Binary { left, token, right } => {
                self.evaluate_binary(func, *left, token, *right)
            }
            hir::expr::ExprKind::Unary { token, right } => self.evaluate_unary(func, token, *right),
            hir::expr::ExprKind::Grouping { expr } => self.visit_expr(func, *expr),
            hir::expr::ExprKind::Literal(n, type_decl) => Ok(mir::expr::Expr {
                kind: mir::expr::ExprKind::Literal(n),
                type_decl,
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

                self.assign_var(left, token, right)
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
            hir::expr::ExprKind::SizeofType { decl_type } => self.sizeof_type(decl_type),
            hir::expr::ExprKind::SizeofExpr { expr } => self.sizeof_expr(func, *expr),
            hir::expr::ExprKind::Nop => Ok(mir::expr::Expr {
                kind: mir::expr::ExprKind::Nop,
                type_decl: Type::Primitive(Primitive::Void),
                value_kind: ValueKind::Rvalue,
            }),
        }
    }
    fn check_type_compatibility(
        token: &Token,
        left_type: &Type,
        right: &mir::expr::Expr,
    ) -> Result<(), Error> {
        if left_type.is_void()
            || right.type_decl.is_void()
            || !left_type.type_compatible(&right.type_decl, right)
        {
            Err(Error::new(
                token,
                ErrorKind::IllegalAssign(left_type.clone(), right.type_decl.clone()),
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
        let expr = self.visit_expr(func, expr)?.decay();
        let new_type = self.parse_type(decl_type)?;

        if !new_type.is_void() && (!expr.type_decl.is_scalar() || !new_type.is_scalar()) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidExplicitCast(expr.type_decl, new_type.clone()),
            ));
        }

        Ok(match expr.type_decl.size().cmp(&new_type.size()) {
            Ordering::Less => expr.cast_to(new_type, CastDirection::Up),
            Ordering::Greater => expr.cast_to(new_type, CastDirection::Down),
            Ordering::Equal => expr.cast_to(new_type, CastDirection::Equal),
        })
    }
    fn maybe_cast(new_type: Type, expr: mir::expr::Expr) -> mir::expr::Expr {
        match expr.type_decl.size().cmp(&new_type.size()) {
            Ordering::Less => expr.cast_to(new_type, CastDirection::Up),
            Ordering::Greater => expr.cast_to(new_type, CastDirection::Down),
            Ordering::Equal => expr,
        }
    }

    fn sizeof_type(&mut self, decl_type: hir::decl::DeclType) -> Result<mir::expr::Expr, Error> {
        let type_decl = self.parse_type(decl_type)?;

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Literal(type_decl.size() as i64),
            type_decl: Type::Primitive(Primitive::Int),
            value_kind: ValueKind::Rvalue,
        })
    }

    fn sizeof_expr(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(func, expr)?;

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Literal(expr.type_decl.size() as i64),
            type_decl: Type::Primitive(Primitive::Int),
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
            type_decl: right.type_decl.clone(),
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
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::NotScalar("conditional", cond.type_decl),
            ));
        }
        let true_expr = self.visit_expr(func, true_expr)?;
        let false_expr = self.visit_expr(func, false_expr)?;

        if !true_expr
            .type_decl
            .type_compatible(&false_expr.type_decl, &false_expr)
        {
            return Err(Error::new(
                &token,
                ErrorKind::TypeMismatch(true_expr.type_decl, false_expr.type_decl),
            ));
        }

        let true_expr = true_expr.maybe_int_promote();
        let false_expr = false_expr.maybe_int_promote();

        let (true_expr, false_expr) = match true_expr.type_decl.size().cmp(&false_expr.type_decl.size())
        {
            Ordering::Greater => (
                true_expr.clone(),
                false_expr.cast_to(true_expr.type_decl, CastDirection::Up),
            ),
            Ordering::Less => (
                true_expr.cast_to(false_expr.type_decl.clone(), CastDirection::Up),
                false_expr,
            ),
            Ordering::Equal => (true_expr, false_expr),
        };

        Ok(mir::expr::Expr {
            type_decl: true_expr.type_decl.clone(),
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

        return match &*symbol.borrow() {
            Symbols::Variable(info) => Ok(mir::expr::Expr {
                type_decl: info.get_type(),
                kind: mir::expr::ExprKind::Ident(Rc::clone(&symbol)),
                value_kind: ValueKind::Lvalue,
            }),
            Symbols::TypeDef(..) => Err(Error::new(
                &token,
                ErrorKind::InvalidSymbol(token.unwrap_string(), "variable"),
            )),
        };
    }
    fn member_access(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        member: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(func, expr)?;

        if !expr.type_decl.is_complete() {
            return Err(Error::new(
                &token,
                ErrorKind::IncompleteMemberAccess(expr.type_decl),
            ));
        }

        match &expr.type_decl {
            Type::Struct(s) | Type::Union(s) => {
                let member = member.unwrap_string();

                if let Some((member_type, _)) = s
                    .members()
                    .iter()
                    .find(|(_, name)| name.unwrap_string() == member)
                {
                    Ok(mir::expr::Expr {
                        kind: mir::expr::ExprKind::MemberAccess { member, expr: Box::new(expr) },
                        type_decl: member_type.clone(),
                        value_kind: ValueKind::Lvalue,
                    })
                } else {
                    Err(Error::new(
                        &token,
                        ErrorKind::NonExistantMember(member, expr.type_decl),
                    ))
                }
            }
            _ => Err(Error::new(&token, ErrorKind::InvalidMemberAccess(expr.type_decl))),
        }
    }
    fn evaluate_postunary(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        token: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let type_decl = self.visit_expr(func, expr.clone())?.type_decl;

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
                r_expr: Box::new(hir::expr::ExprKind::Literal(1, Type::Primitive(Primitive::Int))),
            }),
            token: Token { kind: bin_op, ..token },
            right: Box::new(hir::expr::ExprKind::Literal(1, Type::Primitive(Primitive::Int))),
        };

        // need to cast back to left-type since binary operation integer promotes
        // char c; typeof(c--) == char
        Ok(Self::maybe_cast(
            type_decl,
            self.visit_expr(func, postunary_sugar)?,
        ))
    }
    fn string(&mut self, data: String) -> Result<mir::expr::Expr, Error> {
        let len = data.len() + 1; // extra byte for \0-Terminator
        self.const_labels
            .insert(data.clone(), create_label(&mut self.const_label_count));

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::String(data),
            type_decl: Type::Array {
                of: Box::new(Type::Primitive(Primitive::Char)),
                amount: len,
            },
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
        let type_decl = self.visit_expr(func, l_expr.clone())?.type_decl;

        // to not evaluate l-expr twice convert `A op= B` to `tmp = &A, *tmp = *tmp op B`
        self.env.enter();
        let tmp_token = Token {
            // have to generate unique name so normal variables are not confused for tmp
            kind: TokenKind::Ident(format!("tmp{}{}", token.line_index, token.column)),
            ..token.clone()
        };
        let tmp_type = type_decl.pointer_to();

        let tmp_symbol = self
            .env
            .declare_symbol(
                &tmp_token,
                Symbols::Variable(SymbolInfo {
                    type_decl: tmp_type.clone(),
                    kind: InitType::Declaration,
                    reg: None,
                    token: token.clone(),
                }),
            )
            .expect("always valid to declare tmp in new scope");

        if let Some(func) = func {
            func.increment_stack_size(&tmp_type);
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
            type_decl: expr.type_decl.clone(),
            kind: mir::expr::ExprKind::CompoundAssign { tmp_symbol, expr: Box::new(expr) },
            value_kind: ValueKind::Rvalue,
        })
    }
    fn assign_var(
        &mut self,
        left: mir::expr::Expr,
        token: Token,
        right: mir::expr::Expr,
    ) -> Result<mir::expr::Expr, Error> {
        if left.type_decl.is_array() || left.type_decl.is_func() {
            return Err(Error::new(&token, ErrorKind::NotAssignable(left.type_decl)));
        }

        if left.value_kind != ValueKind::Lvalue {
            return Err(Error::new(&token, ErrorKind::NotLvalue));
        }

        let right = right.decay();
        Self::check_type_compatibility(&token, &left.type_decl, &right)?;
        let right = Self::maybe_cast(left.type_decl.clone(), right);

        Ok(mir::expr::Expr {
            type_decl: left.type_decl.clone(),
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
        for expr in parsed_args.into_iter() {
            let arg = self.visit_expr(func, expr)?.decay().maybe_int_promote();
            args.push(arg);
        }

        let func_type = match caller.type_decl.clone() {
            Type::Function(func_type) => func_type,
            ty => {
                let mut pointer_to_func = None;
                if let Type::Pointer(to) = ty {
                    if let Type::Function(func_type) = *to {
                        pointer_to_func = Some(func_type)
                    }
                }
                if let Some(pointer_to_func) = pointer_to_func {
                    pointer_to_func
                } else {
                    return Err(Error::new(
                        &left_paren,
                        ErrorKind::InvalidCaller(caller.type_decl),
                    ));
                }
            }
        };

        if (!func_type.variadic && func_type.params.len() != args.len())
            || (func_type.variadic && func_type.params.len() > args.len())
        {
            return Err(Error::new(
                &left_paren,
                ErrorKind::MismatchedArity(caller.type_decl, func_type.params.len(), args.len()),
            ));
        }
        let args = self.args_and_params_match(&left_paren, &caller.type_decl, func_type.params, args)?;

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Call { caller: Box::new(caller), args },
            type_decl: *func_type.return_type,
            value_kind: ValueKind::Rvalue,
        })
    }
    fn args_and_params_match(
        &self,
        left_paren: &Token,
        type_decl: &Type,
        params: Vec<Type>,
        mut args: Vec<mir::expr::Expr>,
    ) -> Result<Vec<mir::expr::Expr>, Error> {
        let mut new_args = Vec::new();

        // previously checked that args >= params, can be more args because of variadic params
        let remaining_args: Vec<mir::expr::Expr> = args.drain(params.len()..).collect();

        for (index, (arg, param_type)) in args.into_iter().zip(params).enumerate() {
            Self::check_type_compatibility(left_paren, &param_type, &arg).or(Err(Error::new(
                left_paren,
                ErrorKind::MismatchedArgs(
                    index,
                    type_decl.clone(),
                    param_type.clone(),
                    arg.type_decl.clone(),
                ),
            )))?;

            // cast argument to the correct parameter type
            new_args.push(if param_type.size() > Type::Primitive(Primitive::Char).size() {
                Self::maybe_cast(param_type, arg)
            } else {
                arg
            });
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
        let mut left = self.visit_expr(func, left)?;
        let mut right = self.visit_expr(func, right)?;

        left.to_rval();
        right.to_rval();

        let left = left.decay();
        let right = right.decay();

        if !left.type_decl.is_scalar() || !right.type_decl.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidLogical(token.kind.clone(), left.type_decl, right.type_decl),
            ));
        }

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Logical {
                left: Box::new(left),
                right: Box::new(right),
                operator: token.kind,
            },
            type_decl: Type::Primitive(Primitive::Int),
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
        let mut left = self.visit_expr(func, left)?;
        let mut right = self.visit_expr(func, right)?;

        left.to_rval();
        right.to_rval();

        let left = left.decay();
        let right = right.decay();

        if !is_valid_comp(&left.type_decl, &left, &right.type_decl, &right) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidComp(token.kind.clone(), left.type_decl, right.type_decl),
            ));
        }

        let mut left = left.maybe_int_promote();
        let mut right = right.maybe_int_promote();

        match left.type_decl.size().cmp(&right.type_decl.size()) {
            Ordering::Greater => right = right.cast_to(left.type_decl.clone(), CastDirection::Up),
            Ordering::Less => left = left.cast_to(right.type_decl.clone(), CastDirection::Up),
            Ordering::Equal => (),
        }

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Comparison {
                operator: token.kind,
                left: Box::new(left),
                right: Box::new(right),
            },
            type_decl: Type::Primitive(Primitive::Int),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn evaluate_binary(
        &mut self,
        func: &mut Option<&mut mir::decl::Function>,
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let mut left = self.visit_expr(func, left)?;
        let mut right = self.visit_expr(func, right)?;

        left.to_rval();
        right.to_rval();

        let left = left.decay();
        let right = right.decay();

        if !is_valid_bin(&token.kind, &left.type_decl, &right.type_decl, &right) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidBinary(token.kind.clone(), left.type_decl, right.type_decl),
            ));
        }

        let mut left = left.maybe_int_promote();
        let mut right = right.maybe_int_promote();

        if let Some((expr, amount)) = maybe_scale_index(
            &left.type_decl.clone(),
            &right.type_decl.clone(),
            &mut left,
            &mut right,
        ) {
            expr.kind = mir::expr::ExprKind::ScaleUp { by: amount, expr: Box::new(expr.clone()) };
        }

        Ok(Self::binary_type_promotion(token.kind, left, right))
    }
    fn binary_type_promotion(
        operator: TokenKind,
        left: mir::expr::Expr,
        right: mir::expr::Expr,
    ) -> mir::expr::Expr {
        let (left, right, scale_factor) =
            match (left.type_decl.clone(), right.type_decl.clone(), &operator) {
                // shift operations always have the type of the left operand
                (.., TokenKind::GreaterGreater | TokenKind::LessLess) => (left, right, None),

                // if pointer - pointer, scale result before operation to match left-pointers type
                (Type::Pointer(inner), Type::Pointer(_), _) => (left, right, Some(inner.size())),
                // if integer type and pointer always cast to pointer
                (_, right_type @ Type::Pointer(_), _) => {
                    (left.cast_to(right_type, CastDirection::Up), right, None)
                }
                (left_type @ Type::Pointer(_), ..) => {
                    (left, right.cast_to(left_type, CastDirection::Up), None)
                }

                // otherwise cast to bigger type if unequal types
                (left_type, right_type, _) if left_type.size() > right_type.size() => {
                    (left, right.cast_to(left_type, CastDirection::Up), None)
                }
                (left_type, right_type, _) if left_type.size() < right_type.size() => {
                    (left.cast_to(right_type, CastDirection::Up), right, None)
                }
                _ => (left, right, None),
            };

        let result = mir::expr::Expr {
            type_decl: left.type_decl.clone(),
            kind: mir::expr::ExprKind::Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            },
            value_kind: mir::expr::ValueKind::Rvalue,
        };

        if let Some(scale_factor) = scale_factor {
            mir::expr::Expr {
                kind: mir::expr::ExprKind::ScaleDown {
                    shift_amount: log_2(scale_factor as i32),
                    expr: Box::new(result),
                },
                type_decl: Type::Primitive(Primitive::Long),
                value_kind: mir::expr::ValueKind::Rvalue,
            }
        } else {
            result
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
            let mut right = right.decay();

            match token.kind {
                TokenKind::Star => self.check_deref(token, right),
                TokenKind::Bang => {
                    right.to_rval();
                    let right = Box::new(right.maybe_int_promote());

                    if !right.type_decl.is_scalar() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidUnary(token.kind.clone(), right.type_decl, "scalar"),
                        ));
                    }

                    Ok(mir::expr::Expr {
                        kind: mir::expr::ExprKind::Unary { operator: token.kind, right },
                        type_decl: Type::Primitive(Primitive::Int),
                        value_kind: ValueKind::Rvalue,
                    })
                }
                TokenKind::Minus | TokenKind::Tilde | TokenKind::Plus => {
                    right.to_rval();
                    let right = Box::new(right.maybe_int_promote());

                    if !right.type_decl.is_integer() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidUnary(token.kind.clone(), right.type_decl, "integer"),
                        ));
                    }

                    Ok(mir::expr::Expr {
                        type_decl: right.type_decl.clone(),
                        kind: mir::expr::ExprKind::Unary { operator: token.kind, right },
                        value_kind: ValueKind::Rvalue,
                    })
                }
                _ => unreachable!(), // ++a or --a are evaluated as compound assignment
            }
        }
    }
    fn check_address(&self, token: Token, right: mir::expr::Expr) -> Result<mir::expr::Expr, Error> {
        if right.value_kind == ValueKind::Lvalue {
            Ok(mir::expr::Expr {
                type_decl: right.type_decl.clone().pointer_to(),
                value_kind: ValueKind::Rvalue,
                kind: mir::expr::ExprKind::Unary {
                    right: Box::new(right),
                    operator: token.kind,
                },
            })
        } else {
            Err(Error::new(
                &token,
                ErrorKind::Regular("address-of operator '&' requires lvalue as operand"),
            ))
        }
    }
    fn check_deref(&self, token: Token, right: mir::expr::Expr) -> Result<mir::expr::Expr, Error> {
        if let Some(inner) = right.type_decl.deref_at() {
            Ok(mir::expr::Expr {
                value_kind: ValueKind::Lvalue,
                type_decl: inner,
                kind: mir::expr::ExprKind::Unary {
                    right: Box::new(right),
                    operator: token.kind,
                },
            })
        } else {
            Err(Error::new(&token, ErrorKind::InvalidDerefType(right.type_decl)))
        }
    }
}

#[derive(Clone)]
struct CurrentObjects(Vec<(i64, i64, Type)>);
impl CurrentObjects {
    fn new(type_decl: Type) -> Self {
        CurrentObjects(vec![(0, 0, type_decl)])
    }
    fn update(&mut self, (i, union_index, new_type): (i64, i64, Type)) {
        self.0.last_mut().unwrap().0 = i;
        self.0.last_mut().unwrap().1 = union_index;
        self.0.push((0, 0, new_type));
    }
    fn current(&self) -> &(i64, i64, Type) {
        self.0.last().unwrap()
    }
    fn current_type(&self) -> &Type {
        if let Some((.., type_decl)) = self.0.last() {
            type_decl
        } else {
            unreachable!("always at least one current objects")
        }
    }
    fn offset(&self) -> i64 {
        self.0
            .iter()
            .fold(0, |acc, (i, _, type_decl)| acc + type_decl.offset(*i))
    }
    fn update_current(&mut self) {
        let mut remove_idx = None;
        for (obj_index, (i, _, type_decl)) in self.0.iter().enumerate().rev() {
            if obj_index != 0 && (i + 1 >= type_decl.len() as i64) {
                remove_idx = Some(obj_index);
            } else {
                break;
            }
        }
        // if new current objects also full then remove too
        if let Some(i) = remove_idx {
            self.0.truncate(i);
        }

        // increment the index of the current object
        self.0.last_mut().unwrap().0 += 1;
    }
    // removes all objects except base-type
    fn clear(&mut self) {
        self.0.truncate(1);
    }

    fn find_same_union(
        &self,
        new_list: &Vec<(CurrentObjects, mir::expr::Expr, i64)>,
    ) -> Option<(i64, usize)> {
        for (objects, ..) in new_list {
            let mut offset = 0;
            for (other_obj, current_obj) in objects.0.iter().zip(&self.0) {
                match (other_obj, current_obj) {
                    ((_, i1, type_decl @ Type::Union(_)), (_, i2, Type::Union(_))) if i1 != i2 => {
                        return Some((offset, type_decl.size()))
                    }
                    ((i1, ..), (i2, ..)) if *i1 != *i2 => break,
                    ((i, _, type_decl), ..) => offset += type_decl.offset(*i),
                }
            }
        }
        None
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

// cannot just pass mir-expr since also used in fold which uses hir
pub fn is_valid_bin(
    operator: &TokenKind,
    left_type: &Type,
    right_type: &Type,
    right_expr: &impl hir::expr::IsZero,
) -> bool {
    match (&left_type, &right_type) {
        (Type::Primitive(Primitive::Void), _)
        | (_, Type::Primitive(Primitive::Void))
        | (Type::Struct(..), _)
        | (_, Type::Struct(..))
        | (Type::Union(..), _)
        | (_, Type::Union(..)) => false,

        (Type::Pointer(_), Type::Pointer(_)) => {
            if left_type.type_compatible(right_type, right_expr) {
                operator == &TokenKind::Minus
            } else {
                false
            }
        }
        (_, Type::Pointer(_)) => operator == &TokenKind::Plus,
        (Type::Pointer(_), _) => operator == &TokenKind::Plus || operator == &TokenKind::Minus,
        _ => true,
    }
}
pub fn is_valid_comp(
    left_type: &Type,
    left_expr: &impl hir::expr::IsZero,
    right_type: &Type,
    right_expr: &impl hir::expr::IsZero,
) -> bool {
    let integer_operands = left_type.is_integer() && right_type.is_integer();
    let compatible_pointers = (left_type.is_ptr() || right_type.is_ptr())
                // have to unfortunately check in both directions since either expr can be 0 literal
            && (left_type.type_compatible(right_type, right_expr)
            || right_type.type_compatible(left_type, left_expr));

    integer_operands || compatible_pointers
}

// scale index when pointer arithmetic
pub fn maybe_scale_index<'a, T>(
    left_type: &Type,
    right_type: &Type,
    left_expr: &'a mut T,
    right_expr: &'a mut T,
) -> Option<(&'a mut T, usize)> {
    match (left_type, right_type) {
        (t, Type::Pointer(inner)) if !t.is_ptr() && inner.size() > 1 => Some((left_expr, inner.size())),
        (Type::Pointer(inner), t) if !t.is_ptr() && inner.size() > 1 => Some((right_expr, inner.size())),
        _ => None,
    }
}

// helper function for calculating log2
const fn num_bits<T>() -> usize {
    std::mem::size_of::<T>() * 8
}

fn log_2(x: i32) -> usize {
    assert!(x > 0);
    (num_bits::<i32>() as u32 - x.leading_zeros() - 1) as usize
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

    macro_rules! assert_type {
        ($input:expr,$expected_type:expr,$env:expr) => {
            let expr = setup($input).expression().unwrap();

            let mut typechecker = TypeChecker::new();
            setup_env(&mut typechecker, $env);

            let actual = typechecker.visit_expr(&mut None, expr).unwrap();
            let expected_type = setup_type!($expected_type, typechecker);

            assert!(
                actual.type_decl == expected_type,
                "actual: {}, expected: {}",
                actual.type_decl,
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

            let expr = typechecker.visit_expr(&mut None, expr).unwrap().decay();

            let actual = expr.is_constant();

            assert_eq!(actual, $expected);
        };
    }
    fn setup_init_list(input: &str) -> Result<mir::decl::Init, Error> {
        // TODO: maybe be can parser.parse() so that external declaration doesnt have to be public
        let hir::decl::ExternalDeclaration::Declaration(decls) =
                setup(input).external_declaration().unwrap() else {unreachable!("only passing type")};

        let hir::decl::Declaration { specifiers, declarators, is_typedef } = decls;
        let mut typechecker = TypeChecker::new();

        let decl = declarators[0].clone();
        let specifier_type = typechecker.parse_specifiers(specifiers).unwrap();
        let declarator = typechecker.declarator(specifier_type, is_typedef, decl, &mut None)?;

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
            ScopeKind::Switch(Vec::new()),
            ScopeKind::Switch(Vec::new()),
        ];
        let expected = true;
        let actual = find_scope!(scopes, ScopeKind::Loop).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn doesnt_find_switch() {
        let mut scopes = vec![ScopeKind::Loop, ScopeKind::Loop];
        let expected = false;
        let actual = find_scope!(scopes, ScopeKind::Switch(..)).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn finds_and_mutates_scope() {
        let mut scopes = vec![
            ScopeKind::Loop,
            ScopeKind::Switch(Vec::new()),
            ScopeKind::Switch(Vec::new()),
            ScopeKind::Loop,
        ];
        let expected = vec![
            ScopeKind::Loop,
            ScopeKind::Switch(Vec::new()),
            ScopeKind::Switch(vec![CaseKind::Case(1), CaseKind::Default, CaseKind::Case(3)]),
            ScopeKind::Loop,
        ];
        let ScopeKind::Switch(labels) =
            find_scope!(scopes, ScopeKind::Switch(..)).unwrap() else {unreachable!()};
        labels.push(CaseKind::Case(1));
        labels.push(CaseKind::Default);
        labels.push(CaseKind::Case(3));

        assert_eq!(scopes, expected);
    }

    #[test]
    fn array_init_list() {
        let actual = setup_init_list("int a[3] = {1,2};").unwrap();
        let expected = vec![(0, "1", "int"), (4, "2", "int")];

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
                kind: ErrorKind::InitializerOverflow(Type::Union(_)),
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
            (4, "'\\0'", "char"),
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
}
