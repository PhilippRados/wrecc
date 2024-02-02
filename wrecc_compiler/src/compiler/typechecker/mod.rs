pub mod mir;

use crate::compiler::codegen::align;
use crate::compiler::codegen::register::*;
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::parser::hir;

use self::mir::expr::{CastDirection, ValueKind};

use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

macro_rules! find_scope {
    ($scope:expr,$($expected:pat_param)|+) => {{
        let mut result = None;
        for current in $scope.0.iter_mut().rev() {
            if matches!(current, $($expected)|+) {
                result = Some(current);
                break;
            }
        }
        result
    }};
}

pub struct TypeChecker {
    // keeps track of current scope-kind
    scope: Scope,

    // symbol table
    pub env: Environment,

    // TODO: this should be done via control-flow-graph
    // checks if all paths return from a function
    returns_all_paths: bool,

    // label with its associated label index
    const_labels: HashMap<String, usize>,

    // label index counter
    const_label_count: usize,

    // save encountered switch-statements together with info about their cases and defaults,
    // allows for simpler codegen
    switches: Vec<Vec<Option<i64>>>,
}

// Converts hir-parsetree to type-annotated mir-ast. Also does typechecking and semantic analysis
impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            scope: Scope(vec![ScopeKind::Global]),
            env: Environment::new(),
            returns_all_paths: false,
            const_labels: HashMap::new(),
            const_label_count: 0,
            switches: Vec::new(),
        }
    }
    pub fn check(
        mut self,
        external_decls: Vec<hir::decl::ExternalDeclaration>,
    ) -> Result<
        (
            Vec<mir::decl::ExternalDeclaration>,
            HashMap<String, usize>,
            Vec<Vec<Option<i64>>>,
        ),
        Vec<Error>,
    > {
        match self.check_declarations(external_decls) {
            Ok(mir) => Ok((mir, self.const_labels, self.switches)),
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
                .declaration(decl)
                .map(mir::decl::ExternalDeclaration::Declaration),
            hir::decl::ExternalDeclaration::Function(decl_type, name, body) => {
                self.function_definition(decl_type, name, body)
            }
        }
    }

    fn declaration(
        &mut self,
        decl: hir::decl::Declaration,
    ) -> Result<Vec<mir::decl::Declarator>, Error> {
        let mut declarators = Vec::new();
        let specifier_type = self.parse_specifiers(decl.specifiers.clone())?;

        for declarator in decl.declarators {
            if let Some(d) = self.declarator(specifier_type.clone(), decl.is_typedef, declarator)? {
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
    ) -> Result<Option<mir::decl::Declarator>, Error> {
        let parsed_type = self.parse_modifiers(specifier_type, declarator.modifiers)?;

        if let Some(name) = declarator.name {
            let symbol = if is_typedef {
                Symbols::TypeDef(parsed_type.clone())
            } else if let Type::Function { return_type, params, variadic } = parsed_type.clone() {
                let func = Function::new(*return_type, params, variadic, InitType::Declaration);
                Symbols::Func(func)
            } else {
                Symbols::Variable(SymbolInfo {
                    kind: if init.is_some() {
                        InitType::Definition
                    } else {
                        InitType::Declaration
                    },
                    token: name.clone(),
                    type_decl: parsed_type.clone(),
                    is_global: self.env.is_global(),
                    // since global variable declarations can be used before initialization already
                    // insert its register
                    reg: if self.env.is_global() {
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
                (Symbols::Variable(_), Some(init)) => {
                    if !parsed_type.is_complete() {
                        return Err(Error::new(&name, ErrorKind::IncompleteType(parsed_type)));
                    }
                    let init = self.init_check(&parsed_type, init)?;

                    if !self.env.is_global() {
                        self.scope.increment_stack_size(&parsed_type);
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
                    if !self.env.is_global() {
                        self.scope.increment_stack_size(&parsed_type);
                    }
                    Ok(Some(mir::decl::Declarator {
                        name,
                        entry: Rc::clone(&entry),
                        init: None,
                    }))
                }
                (_, Some(_)) => Err(Error::new(
                    &name,
                    ErrorKind::Regular("Only variables can be initialized"),
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
    fn parse_specifiers(
        &mut self,
        specifiers: Vec<hir::decl::DeclSpecifier>,
    ) -> Result<Type, Error> {
        if specifiers.is_empty() {
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
            [hir::decl::SpecifierKind::UserType] => {
                if let Ok(Symbols::TypeDef(type_decl)) = self
                    .env
                    .get_symbol(&token)
                    .map(|symbol| symbol.borrow().clone())
                {
                    Ok(type_decl)
                } else {
                    Err(Error::new(
                        &token,
                        ErrorKind::InvalidSymbol(token.unwrap_string(), "user-type"),
                    ))
                }
            }

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
                ErrorKind::Regular("Invalid combination of type-specifiers"),
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
                        .map(|(type_decl, name)| {
                            if let Some((token, _)) = name {
                                (type_decl, Some(token))
                            } else {
                                (type_decl, None)
                            }
                        })
                        .collect();
                    self.env.exit();

                    if parsed_type.is_func() || parsed_type.is_array() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidReturnType(parsed_type),
                        ));
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
                let custom_type = self.env.declare_type(
                    name,
                    Tags::Aggregate(StructRef::new(token.clone().token, true)),
                )?;

                let members = self.struct_declaration(members.clone())?;

                if let Tags::Aggregate(struct_ref) = &*custom_type.borrow_mut() {
                    struct_ref.update(members);
                }
                let members = custom_type.borrow().clone().unwrap_aggr();

                StructInfo::Named(name.unwrap_string(), members)
            }

            (Some(name), None) => {
                let custom_type = self.env.get_type(name).or_else(|_| {
                    self.env.declare_type(
                        name,
                        Tags::Aggregate(StructRef::new(token.clone().token, false)),
                    )
                })?;

                if &token.token != custom_type.borrow().get_kind() {
                    return Err(Error::new(
                        name,
                        ErrorKind::TypeAlreadyExists(name.unwrap_string(), token.token.clone()),
                    ));
                }

                let members = custom_type.borrow().clone().unwrap_aggr();

                StructInfo::Named(name.unwrap_string(), members)
            }
            (None, Some(members)) => {
                let members = self.struct_declaration(members.clone())?;
                StructInfo::Anonymous(token.clone(), members)
            }
            (None, None) => {
                return Err(Error::new(
                    &token,
                    ErrorKind::EmptyAggregate(token.token.clone()),
                ));
            }
        };

        Ok(match token.token {
            TokenType::Struct => Type::Struct(members),
            TokenType::Union => Type::Union(members),
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
                // TODO: also cant have pure function

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

                if &token.token != custom_type.borrow().get_kind() {
                    return Err(Error::new(
                        name,
                        ErrorKind::TypeAlreadyExists(name.unwrap_string(), token.token.clone()),
                    ));
                }
                let constants = custom_type.borrow().clone().unwrap_enum();

                Ok(Type::Enum(Some(name.unwrap_string()), constants))
            }
            (None, Some(values)) => Ok(Type::Enum(None, self.enumerator_list(values.clone())?)),
            (None, None) => Err(Error::new(
                &token,
                ErrorKind::EmptyAggregate(token.token.clone()),
            )),
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
                    is_global: self.env.is_global(),
                    reg: Some(Register::Literal(
                        index as i64,
                        Type::Primitive(Primitive::Int),
                    )),
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
                        is_global: false,
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
        } else if parsed_params
            .iter()
            .any(|(type_decl, _)| type_decl.is_void())
        {
            return Err(Error::new(token, ErrorKind::VoidFuncArg));
        }

        Ok(parsed_params)
    }

    fn init_check(
        &mut self,
        type_decl: &Type,
        mut init: hir::decl::Init,
    ) -> Result<mir::decl::Init, Error> {
        if let Some((amount, s)) = Self::is_string_init(type_decl, &init)? {
            init.kind = Self::char_array(init.token.clone(), s, amount)?;
        }

        match init.kind {
            hir::decl::InitKind::Scalar(expr) => self.init_scalar(type_decl, &init.token, expr),
            hir::decl::InitKind::Aggr(list) => self.init_aggregate(type_decl, init.token, list),
        }
    }
    fn init_scalar(
        &mut self,
        type_decl: &Type,
        token: &Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::decl::Init, Error> {
        let expr = self.visit_expr(expr)?;

        let expr = expr.array_decay();
        Self::check_type_compatibility(token, type_decl, &expr)?;
        let expr = Self::maybe_cast(type_decl.clone(), expr);

        if self.env.is_global() && !expr.is_constant() {
            return Err(Error::new(
                token,
                ErrorKind::NotConstantInit("Global variables"),
            ));
        }

        Ok(mir::decl::Init::Scalar(expr))
    }
    fn init_aggregate(
        &mut self,
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
                            let designator_info =
                                self.designator_index(objects.current_type(), d)?;
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
                        let right = self.visit_expr(expr)?;

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

                    let init = self.init_check(sub_type, *list.remove(0))?;
                    let init_offset = objects.offset();

                    // remove overriding elements
                    let init_interval =
                        if let Some((offset, size)) = objects.find_same_union(&new_list) {
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
                    self.init_check(type_decl, *single_init.clone())
                }
                [single_init] => Err(Error::new(
                    &single_init.token,
                    ErrorKind::Regular("Too many braces around scalar initializer"),
                )),
                [_, second_init, ..] => {
                    Err(Error::new(&second_init.token, ErrorKind::ScalarOverflow))
                }
                [] => Err(Error::new(
                    &token,
                    ErrorKind::Regular("Scalar initializer cannot be empty"),
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
                let literal =
                    expr.get_literal_constant(self, &designator.token, "Array designator")?;
                if literal < 0 {
                    return Err(Error::new(
                        &designator.token,
                        ErrorKind::Regular("Array designator must be positive number"),
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
                    "Can only use member designator on type 'struct' and 'union' not 'array'",
                ),
            )),

            (hir::decl::DesignatorKind::Array(_), Type::Struct(_) | Type::Union(_)) => {
                Err(Error::new(
                    &designator.token,
                    ErrorKind::InvalidArrayDesignator(type_decl.clone()),
                ))
            }
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
                                ErrorKind::Regular("Excess elements in char array initializer"),
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
    fn char_array(
        token: Token,
        mut s: String,
        amount: usize,
    ) -> Result<hir::decl::InitKind, Error> {
        // char s[] = "abc" identical to char s[] = {'a','b','c','\0'} (6.7.8)
        if amount < s.len() {
            return Err(Error::new(
                &token,
                ErrorKind::TooLong("Initializer-string", amount, s.len()),
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
        let Some(hir::decl::DeclModifier::Function { params, variadic,token }) = decl_type.modifiers.pop() else {
            unreachable!("last modifier has to be function to be func-def");
        };
        let return_type = self.parse_type(decl_type)?;

        if return_type.is_func() || return_type.is_array() {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidReturnType(return_type),
            ));
        }

        if !return_type.is_complete() && !return_type.is_void() {
            return Err(Error::new(
                &name,
                ErrorKind::IncompleteReturnType(name.unwrap_string(), return_type),
            ));
        }

        // have to push scope before declaring local variables
        self.env.enter();

        let params = self.parse_params(&token, params)?;

        let func = Function::new(
            return_type.clone(),
            params
                .clone()
                .into_iter()
                .map(|(type_decl, name)| {
                    if let Some((token, _)) = name {
                        (type_decl, Some(token))
                    } else {
                        (type_decl, None)
                    }
                })
                .collect(),
            variadic,
            InitType::Definition,
        );

        let symbol = self.env.declare_global(&name, Symbols::Func(func))?;

        self.scope
            .0
            .push(ScopeKind::Function(Rc::clone(&symbol), Vec::new()));

        let mut mir_params = Vec::new();
        for (type_decl, param_name) in params.into_iter() {
            if !type_decl.is_complete() {
                return Err(Error::new(
                    &name,
                    ErrorKind::IncompleteFuncArg(name.unwrap_string(), type_decl),
                ));
            }
            if let Some((_, var_symbol)) = param_name {
                self.scope.increment_stack_size(&type_decl);

                mir_params.push(var_symbol);
            } else {
                return Err(Error::new(&name, ErrorKind::UnnamedFuncParams));
            }
        }

        // check function body
        let body = self.block(body);

        self.scope.compare_gotos()?;
        self.scope.0.pop();

        let mir::stmt::Stmt::Block(mut body) = body? else {unreachable!()};

        Self::main_returns_int(&name, &return_type)?;
        self.implicit_return_main(Rc::clone(&symbol), &name, &mut body);

        if !return_type.is_void() && !self.returns_all_paths {
            self.returns_all_paths = false;

            Err(Error::new(
                &name,
                ErrorKind::NoReturnAllPaths(name.unwrap_string()),
            ))
        } else {
            self.returns_all_paths = false;

            Ok(mir::decl::ExternalDeclaration::Function(
                name.unwrap_string(),
                symbol,
                mir_params,
                body,
            ))
        }
    }
    fn main_returns_int(name_token: &Token, return_type: &Type) -> Result<(), Error> {
        if name_token.unwrap_string() == "main" && *return_type != Type::Primitive(Primitive::Int) {
            Err(Error::new(
                name_token,
                ErrorKind::InvalidMainReturn(return_type.clone()),
            ))
        } else {
            Ok(())
        }
    }
    fn implicit_return_main(
        &mut self,
        func_symbol: FuncSymbol,
        name_token: &Token,
        body: &mut Vec<mir::stmt::Stmt>,
    ) {
        if name_token.unwrap_string() == "main" && !self.returns_all_paths {
            self.returns_all_paths = true;

            body.push(mir::stmt::Stmt::Return(
                func_symbol,
                Some(mir::expr::Expr {
                    kind: mir::expr::ExprKind::Literal(0),
                    type_decl: Type::Primitive(Primitive::Int),
                    value_kind: ValueKind::Rvalue,
                }),
            ));
        }
    }
    fn visit_stmt(&mut self, statement: hir::stmt::Stmt) -> Result<mir::stmt::Stmt, Error> {
        match statement {
            hir::stmt::Stmt::Declaration(decls) => {
                self.declaration(decls).map(mir::stmt::Stmt::Declaration)
            }
            hir::stmt::Stmt::Return(keyword, value) => self.return_statement(keyword, value),
            hir::stmt::Stmt::Expr(expr) => Ok(mir::stmt::Stmt::Expr(self.visit_expr(expr)?)),
            hir::stmt::Stmt::Block(statements) => {
                self.env.enter();
                self.block(statements)
            }
            hir::stmt::Stmt::If(keyword, cond, then_branch, else_branch) => {
                self.if_statement(keyword, cond, *then_branch, else_branch)
            }
            hir::stmt::Stmt::While(left_paren, cond, body) => {
                self.while_statement(left_paren, cond, *body)
            }
            hir::stmt::Stmt::Do(keyword, body, cond) => self.do_statement(keyword, *body, cond),
            hir::stmt::Stmt::For(left_paren, init, cond, inc, body) => {
                self.for_statement(left_paren, init, cond, inc, *body)
            }
            hir::stmt::Stmt::Break(keyword) => self.break_statement(keyword),
            hir::stmt::Stmt::Continue(keyword) => self.continue_statement(keyword),
            hir::stmt::Stmt::Switch(keyword, cond, body) => {
                self.switch_statement(keyword, cond, *body)
            }
            hir::stmt::Stmt::Case(keyword, value, body) => {
                self.case_statement(keyword, value, *body)
            }
            hir::stmt::Stmt::Default(keyword, body) => self.default_statement(keyword, *body),
            hir::stmt::Stmt::Goto(label) => self.goto_statement(label),
            hir::stmt::Stmt::Label(name, body) => self.label_statement(name, *body),
        }
    }
    fn goto_statement(&mut self, label: Token) -> Result<mir::stmt::Stmt, Error> {
        let func_symbol = self.scope.insert_goto(label.clone())?;

        Ok(mir::stmt::Stmt::Goto(func_symbol, label.unwrap_string()))
    }
    fn label_statement(
        &mut self,
        name_token: Token,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let func_symbol = self.scope.insert_label(&name_token)?;
        let body = self.visit_stmt(body)?;

        Ok(mir::stmt::Stmt::Label(
            func_symbol,
            name_token.unwrap_string(),
            Box::new(body),
        ))
    }
    fn switch_statement(
        &mut self,
        token: Token,
        cond: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let cond = self.visit_expr(cond)?;
        if !cond.type_decl.is_integer() {
            return Err(Error::new(
                &token,
                ErrorKind::NotInteger("Switch conditional", cond.type_decl),
            ));
        }
        self.scope.0.push(ScopeKind::Switch(vec![]));
        let stmt = self.visit_stmt(body);

        let Some(ScopeKind::Switch(labels)) = self.scope.0.pop() else {
            unreachable!("all other scopes should be popped off by themselves")
        };

        self.switches.push(labels);

        Ok(mir::stmt::Stmt::Switch(cond, Box::new(stmt?)))
    }
    fn case_statement(
        &mut self,
        token: Token,
        mut value: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let value = value.get_literal_constant(self, &token, "Case value")?;

        match find_scope!(&mut self.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(labels)) => {
                if !labels.contains(&Some(value)) {
                    labels.push(Some(value))
                } else {
                    return Err(Error::new(&token, ErrorKind::DuplicateCase(value)));
                }
            }
            _ => {
                return Err(Error::new(&token, ErrorKind::NotIn("case", "switch")));
            }
        }

        let body = self.visit_stmt(body)?;

        Ok(mir::stmt::Stmt::Case(Box::new(body)))
    }
    fn default_statement(
        &mut self,
        token: Token,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        match find_scope!(&mut self.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(labels)) => {
                if !labels.contains(&None) {
                    labels.push(None)
                } else {
                    return Err(Error::new(&token, ErrorKind::MultipleDefaults));
                }
            }
            _ => {
                return Err(Error::new(&token, ErrorKind::NotIn("default", "switch")));
            }
        }
        let body = self.visit_stmt(body)?;

        Ok(mir::stmt::Stmt::Default(Box::new(body)))
    }
    fn do_statement(
        &mut self,
        token: Token,
        body: hir::stmt::Stmt,
        cond: hir::expr::ExprKind,
    ) -> Result<mir::stmt::Stmt, Error> {
        self.scope.0.push(ScopeKind::Loop);
        let body = self.visit_stmt(body)?;
        self.scope.0.pop();

        let cond = self.visit_expr(cond)?;
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::NotScalar("Conditional", cond.type_decl),
            ));
        }

        self.returns_all_paths = false;

        Ok(mir::stmt::Stmt::Do(Box::new(body), cond))
    }
    fn for_statement(
        &mut self,
        left_paren: Token,
        init: Option<Box<hir::stmt::Stmt>>,
        cond: Option<hir::expr::ExprKind>,
        inc: Option<hir::expr::ExprKind>,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        self.env.enter();

        let init = init.map(|init| self.visit_stmt(*init)).transpose()?;

        let cond = if let Some(cond) = cond {
            let cond = self.visit_expr(cond)?;
            if !cond.type_decl.is_scalar() {
                return Err(Error::new(
                    &left_paren,
                    ErrorKind::NotScalar("Conditional", cond.type_decl),
                ));
            }
            Some(cond)
        } else {
            None
        };

        self.scope.0.push(ScopeKind::Loop);
        let body = self.visit_stmt(body)?;

        let inc = inc.map(|inc| self.visit_expr(inc)).transpose()?;

        self.scope.0.pop();
        self.env.exit();

        self.returns_all_paths = false;

        Ok(mir::stmt::Stmt::For(
            init.map(Box::new),
            cond,
            inc,
            Box::new(body),
        ))
    }
    fn break_statement(&mut self, token: Token) -> Result<mir::stmt::Stmt, Error> {
        if find_scope!(&mut self.scope, ScopeKind::Loop | ScopeKind::Switch(..)).is_none() {
            Err(Error::new(
                &token,
                ErrorKind::NotIn("break", "loop/switch-statement"),
            ))
        } else {
            Ok(mir::stmt::Stmt::Break)
        }
    }
    fn continue_statement(&mut self, token: Token) -> Result<mir::stmt::Stmt, Error> {
        if find_scope!(&mut self.scope, ScopeKind::Loop).is_none() {
            Err(Error::new(&token, ErrorKind::NotIn("continue", "loop")))
        } else {
            Ok(mir::stmt::Stmt::Continue)
        }
    }

    fn while_statement(
        &mut self,
        left_paren: Token,
        cond: hir::expr::ExprKind,
        body: hir::stmt::Stmt,
    ) -> Result<mir::stmt::Stmt, Error> {
        let cond = self.visit_expr(cond)?;
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &left_paren,
                ErrorKind::NotScalar("Conditional", cond.type_decl),
            ));
        }

        self.scope.0.push(ScopeKind::Loop);
        let body = self.visit_stmt(body)?;
        self.scope.0.pop();

        self.returns_all_paths = false;

        Ok(mir::stmt::Stmt::While(cond, Box::new(body)))
    }

    fn if_statement(
        &mut self,
        keyword: Token,
        cond: hir::expr::ExprKind,
        then_branch: hir::stmt::Stmt,
        else_branch: Option<Box<hir::stmt::Stmt>>,
    ) -> Result<mir::stmt::Stmt, Error> {
        let cond = self.visit_expr(cond)?;
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &keyword,
                ErrorKind::NotScalar("Conditional", cond.type_decl),
            ));
        }

        let then_branch = self.visit_stmt(then_branch)?;
        let then_return = self.returns_all_paths;
        self.returns_all_paths = false;

        let else_branch = else_branch
            .map(|stmt| {
                let else_branch = self.visit_stmt(*stmt);
                let else_return = self.returns_all_paths;

                if !then_return || !else_return {
                    self.returns_all_paths = false;
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
        keyword: Token,
        expr: Option<hir::expr::ExprKind>,
    ) -> Result<mir::stmt::Stmt, Error> {
        self.returns_all_paths = true;

        let Some(ScopeKind::Function(func_symbol,..)) = find_scope!(&mut self.scope, ScopeKind::Function(..)) else {
            unreachable!("parser ensures that statements can only be contained in functions");
        };
        let function_type = func_symbol.borrow().unwrap_func().return_type.clone();
        let func_symbol = Rc::clone(func_symbol);

        let expr = if let Some(expr) = expr {
            let expr = self.visit_expr(expr)?;

            let expr = expr.array_decay();
            if !function_type.type_compatible(&expr.type_decl, &expr) {
                return Err(Error::new(
                    &keyword,
                    ErrorKind::MismatchedFunctionReturn(function_type, expr.type_decl),
                ));
            }
            let expr = Self::maybe_cast(function_type, expr);

            Some(expr)
        } else {
            let return_type = Type::Primitive(Primitive::Void);
            let return_expr = hir::expr::ExprKind::Nop;

            if !function_type.type_compatible(&return_type, &return_expr) {
                return Err(Error::new(
                    &keyword,
                    ErrorKind::MismatchedFunctionReturn(function_type, return_type),
                ));
            }

            None
        };

        Ok(mir::stmt::Stmt::Return(func_symbol, expr))
    }

    fn block(&mut self, body: Vec<hir::stmt::Stmt>) -> Result<mir::stmt::Stmt, Error> {
        let mut errors = Vec::new();
        let mut stmts = Vec::new();

        for stmt in body {
            match self.visit_stmt(stmt) {
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
        mut parse_tree: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        parse_tree.integer_const_fold(self)?;

        match parse_tree {
            hir::expr::ExprKind::Binary { left, token, right } => {
                self.evaluate_binary(*left, token, *right)
            }
            hir::expr::ExprKind::Unary { token, right } => self.evaluate_unary(token, *right),
            hir::expr::ExprKind::Grouping { expr } => self.visit_expr(*expr),
            hir::expr::ExprKind::Literal(n, type_decl) => Ok(mir::expr::Expr {
                kind: mir::expr::ExprKind::Literal(n),
                type_decl,
                value_kind: ValueKind::Rvalue,
            }),
            hir::expr::ExprKind::String(token) => self.string(token.unwrap_string()),
            hir::expr::ExprKind::Logical { left, token, right } => {
                self.evaluate_logical(*left, token, *right)
            }
            hir::expr::ExprKind::Comparison { left, token, right } => {
                self.evaluate_comparison(*left, token, *right)
            }
            hir::expr::ExprKind::Ident(token) => self.ident(token),
            hir::expr::ExprKind::Assign { l_expr, token, r_expr } => {
                let left = self.visit_expr(*l_expr)?;
                let right = self.visit_expr(*r_expr)?;

                self.assign_var(left, token, right)
            }
            hir::expr::ExprKind::CompoundAssign { l_expr, token, r_expr } => {
                self.compound_assign(*l_expr, token, *r_expr)
            }
            hir::expr::ExprKind::Call { left_paren, name, args } => {
                self.evaluate_call(left_paren, name, args)
            }
            hir::expr::ExprKind::PostUnary { left, token } => self.evaluate_postunary(token, *left),
            hir::expr::ExprKind::MemberAccess { token, expr, member } => {
                self.member_access(token, member, *expr)
            }
            hir::expr::ExprKind::Cast { token, decl_type, expr } => {
                self.explicit_cast(token, *expr, decl_type)
            }
            hir::expr::ExprKind::Ternary { token, cond, true_expr, false_expr } => {
                self.ternary(token, *cond, *true_expr, *false_expr)
            }
            hir::expr::ExprKind::Comma { left, right } => self.comma(*left, *right),
            hir::expr::ExprKind::SizeofType { decl_type } => self.sizeof_type(decl_type),
            hir::expr::ExprKind::SizeofExpr { expr } => self.sizeof_expr(*expr),
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
        token: Token,
        expr: hir::expr::ExprKind,
        decl_type: hir::decl::DeclType,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(expr)?.array_decay();
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

    fn sizeof_expr(&mut self, expr: hir::expr::ExprKind) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(expr)?;

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Literal(expr.type_decl.size() as i64),
            type_decl: Type::Primitive(Primitive::Int),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn comma(
        &mut self,
        left: hir::expr::ExprKind,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let left = self.visit_expr(left)?;
        let right = self.visit_expr(right)?;

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
        token: Token,
        cond: hir::expr::ExprKind,
        true_expr: hir::expr::ExprKind,
        false_expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let cond = self.visit_expr(cond)?;
        if !cond.type_decl.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::NotScalar("Conditional", cond.type_decl),
            ));
        }
        let true_expr = self.visit_expr(true_expr)?;
        let false_expr = self.visit_expr(false_expr)?;

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

        let (true_expr, false_expr) =
            match true_expr.type_decl.size().cmp(&false_expr.type_decl.size()) {
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
            Symbols::TypeDef(..) | Symbols::Func(..) => Err(Error::new(
                &token,
                ErrorKind::InvalidSymbol(token.unwrap_string(), "variable"),
            )),
        };
    }
    fn member_access(
        &mut self,
        token: Token,
        member: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let expr = self.visit_expr(expr)?;

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
            _ => Err(Error::new(
                &token,
                ErrorKind::InvalidMemberAccess(expr.type_decl),
            )),
        }
    }
    fn evaluate_postunary(
        &mut self,
        token: Token,
        expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let type_decl = self.visit_expr(expr.clone())?.type_decl;

        let (comp_op, bin_op) = match token.token {
            TokenType::PlusPlus => (TokenType::PlusEqual, TokenType::Minus),
            TokenType::MinusMinus => (TokenType::MinusEqual, TokenType::Plus),
            _ => unreachable!("not a postunary token"),
        };

        // A++ <=> (A += 1) - 1 or A-- <=> (A -= 1) + 1
        let postunary_sugar = hir::expr::ExprKind::Binary {
            left: Box::new(hir::expr::ExprKind::CompoundAssign {
                l_expr: Box::new(expr),
                token: Token { token: comp_op, ..token.clone() },
                r_expr: Box::new(hir::expr::ExprKind::Literal(
                    1,
                    Type::Primitive(Primitive::Int),
                )),
            }),
            token: Token { token: bin_op, ..token },
            right: Box::new(hir::expr::ExprKind::Literal(
                1,
                Type::Primitive(Primitive::Int),
            )),
        };

        // need to cast back to left-type since binary operation integer promotes
        // char c; typeof(c--) == char
        Ok(Self::maybe_cast(
            type_decl,
            self.visit_expr(postunary_sugar)?,
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
        l_expr: hir::expr::ExprKind,
        token: Token,
        r_expr: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let type_decl = self.visit_expr(l_expr.clone())?.type_decl;

        // to not evaluate l-expr twice convert `A op= B` to `tmp = &A, *tmp = *tmp op B`
        self.env.enter();
        let tmp_token = Token {
            token: TokenType::Ident("tmp".to_string()),
            ..token.clone()
        };
        let tmp_type = type_decl.pointer_to();

        self.scope.increment_stack_size(&tmp_type);

        let tmp_symbol = self
            .env
            .declare_symbol(
                &tmp_token,
                Symbols::Variable(SymbolInfo {
                    type_decl: tmp_type,
                    kind: InitType::Declaration,
                    reg: None,
                    is_global: false,
                    token: token.clone(),
                }),
            )
            .expect("always valid to declare tmp in new scope");

        // tmp = &A, *tmp = *tmp op B
        let compound_sugar = hir::expr::ExprKind::Comma {
            left: Box::new(hir::expr::ExprKind::Assign {
                l_expr: Box::new(hir::expr::ExprKind::Ident(tmp_token.clone())),
                token: token.clone(),
                r_expr: Box::new(hir::expr::ExprKind::Unary {
                    token: Token { token: TokenType::Amp, ..token.clone() },
                    right: Box::new(l_expr),
                }),
            }),
            right: Box::new(hir::expr::ExprKind::Assign {
                l_expr: Box::new(hir::expr::ExprKind::Unary {
                    token: Token { token: TokenType::Star, ..token.clone() },
                    right: Box::new(hir::expr::ExprKind::Ident(tmp_token.clone())),
                }),
                token: token.clone(),
                r_expr: Box::new(hir::expr::ExprKind::Binary {
                    left: Box::new(hir::expr::ExprKind::Unary {
                        token: Token { token: TokenType::Star, ..token.clone() },
                        right: Box::new(hir::expr::ExprKind::Ident(tmp_token.clone())),
                    }),
                    token: Token {
                        token: token.token.comp_to_binary(),
                        ..token
                    },
                    right: Box::new(r_expr),
                }),
            }),
        };

        let expr = self.visit_expr(compound_sugar).map_err(|err| {
            self.env.exit();
            err
        })?;

        self.env.exit();

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
        if matches!(left.type_decl, Type::Array { .. }) {
            return Err(Error::new(&token, ErrorKind::NotAssignable(left.type_decl)));
        }

        if left.value_kind != ValueKind::Lvalue {
            return Err(Error::new(&token, ErrorKind::NotLvalue));
        }

        let right = right.array_decay();
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
        left_paren: Token,
        func_name: Token,
        parsed_args: Vec<hir::expr::ExprKind>,
    ) -> Result<mir::expr::Expr, Error> {
        let mut args: Vec<mir::expr::Expr> = Vec::new();
        for expr in parsed_args.into_iter() {
            let arg = self.visit_expr(expr)?.array_decay().maybe_int_promote();
            args.push(arg);
        }

        let symbol = self.env.get_symbol(&func_name)?;

        return match &*symbol.borrow() {
            Symbols::Variable(_) | Symbols::TypeDef(..) => Err(Error::new(
                &left_paren,
                ErrorKind::InvalidSymbol(func_name.unwrap_string(), "function"),
            )),
            Symbols::Func(function) => {
                if (function.variadic && function.arity() <= args.len())
                    || (!function.variadic && function.arity() == args.len())
                {
                    let args = self.args_and_params_match(
                        &left_paren,
                        func_name.unwrap_string(),
                        &function.clone().params,
                        args,
                    )?;

                    Ok(mir::expr::Expr {
                        kind: mir::expr::ExprKind::Call { name: func_name.unwrap_string(), args },
                        type_decl: function.return_type.clone(),
                        value_kind: ValueKind::Rvalue,
                    })
                } else {
                    Err(Error::new(
                        &left_paren,
                        ErrorKind::MismatchedArity(
                            func_name.unwrap_string(),
                            function.arity(),
                            args.len(),
                        ),
                    ))
                }
            }
        };
    }
    fn args_and_params_match(
        &self,
        left_paren: &Token,
        func_name: String,
        params: &[(Type, Option<Token>)],
        mut args: Vec<mir::expr::Expr>,
    ) -> Result<Vec<mir::expr::Expr>, Error> {
        let mut new_args = Vec::new();

        // previously checked that args >= params, can be more args because of variadic params
        let remaining_args: Vec<mir::expr::Expr> = args.drain(params.len()..).collect();

        for (index, (arg, (param_type, param_token))) in args.into_iter().zip(params).enumerate() {
            Self::check_type_compatibility(left_paren, param_type, &arg).or(Err(Error::new(
                left_paren,
                ErrorKind::MismatchedArgs(
                    index,
                    func_name.clone(),
                    param_token.clone(),
                    param_type.clone(),
                    arg.type_decl.clone(),
                ),
            )))?;

            // cast argument to the correct parameter type
            new_args.push(
                if param_type.size() > Type::Primitive(Primitive::Char).size() {
                    Self::maybe_cast(param_type.clone(), arg)
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
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let mut left = self.visit_expr(left)?;
        let mut right = self.visit_expr(right)?;

        left.to_rval();
        right.to_rval();

        if !left.type_decl.is_scalar() || !right.type_decl.is_scalar() {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidLogical(token.token.clone(), left.type_decl, right.type_decl),
            ));
        }

        Ok(mir::expr::Expr {
            kind: mir::expr::ExprKind::Logical {
                left: Box::new(left),
                right: Box::new(right),
                operator: token.token,
            },
            type_decl: Type::Primitive(Primitive::Int),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn evaluate_comparison(
        &mut self,
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let mut left = self.visit_expr(left)?;
        let mut right = self.visit_expr(right)?;

        left.to_rval();
        right.to_rval();

        let left = left.array_decay();
        let right = right.array_decay();

        if Self::check_type_compatibility(&token, &left.type_decl, &right).is_err() {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidComp(token.token.clone(), left.type_decl, right.type_decl),
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
                operator: token.token,
                left: Box::new(left),
                right: Box::new(right),
            },
            type_decl: Type::Primitive(Primitive::Int),
            value_kind: ValueKind::Rvalue,
        })
    }
    fn evaluate_binary(
        &mut self,
        left: hir::expr::ExprKind,
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let mut left = self.visit_expr(left)?;
        let mut right = self.visit_expr(right)?;

        left.to_rval();
        right.to_rval();

        let left = left.array_decay();
        let right = right.array_decay();

        // check valid operations
        if !is_valid_bin(&token.token, &left.type_decl, &right.type_decl, &right) {
            return Err(Error::new(
                &token,
                ErrorKind::InvalidBinary(token.token.clone(), left.type_decl, right.type_decl),
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

        Ok(Self::binary_type_promotion(token.token, left, right))
    }
    fn binary_type_promotion(
        operator: TokenType,
        left: mir::expr::Expr,
        right: mir::expr::Expr,
    ) -> mir::expr::Expr {
        let (left, right, scale_factor) =
            match (left.type_decl.clone(), right.type_decl.clone(), &operator) {
                // shift operations always have the type of the left operand
                (.., TokenType::GreaterGreater | TokenType::LessLess) => (left, right, None),

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
        token: Token,
        right: hir::expr::ExprKind,
    ) -> Result<mir::expr::Expr, Error> {
        let right = self.visit_expr(right)?;

        if matches!(token.token, TokenType::Amp) {
            // array doesn't decay during '&' expression
            self.check_address(token, right)
        } else {
            let mut right = right.array_decay();

            match token.token {
                TokenType::Star => self.check_deref(token, right),
                TokenType::Bang => {
                    right.to_rval();
                    let right = Box::new(right.maybe_int_promote());

                    if !right.type_decl.is_scalar() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidUnary(token.token.clone(), right.type_decl, "scalar"),
                        ));
                    }

                    Ok(mir::expr::Expr {
                        kind: mir::expr::ExprKind::Unary { operator: token.token, right },
                        type_decl: Type::Primitive(Primitive::Int),
                        value_kind: ValueKind::Rvalue,
                    })
                }
                TokenType::Minus | TokenType::Tilde | TokenType::Plus => {
                    right.to_rval();
                    let right = Box::new(right.maybe_int_promote());

                    if !right.type_decl.is_integer() {
                        return Err(Error::new(
                            &token,
                            ErrorKind::InvalidUnary(
                                token.token.clone(),
                                right.type_decl,
                                "integer",
                            ),
                        ));
                    }

                    Ok(mir::expr::Expr {
                        type_decl: right.type_decl.clone(),
                        kind: mir::expr::ExprKind::Unary { operator: token.token, right },
                        value_kind: ValueKind::Rvalue,
                    })
                }
                _ => unreachable!(), // ++a or --a are evaluated as compound assignment
            }
        }
    }
    fn check_address(
        &self,
        token: Token,
        right: mir::expr::Expr,
    ) -> Result<mir::expr::Expr, Error> {
        if right.value_kind == ValueKind::Lvalue {
            Ok(mir::expr::Expr {
                type_decl: right.type_decl.clone().pointer_to(),
                value_kind: ValueKind::Rvalue,
                kind: mir::expr::ExprKind::Unary {
                    right: Box::new(right),
                    operator: token.token,
                },
            })
        } else {
            Err(Error::new(
                &token,
                ErrorKind::Regular("Can't call '&' on r-value"),
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
                    operator: token.token,
                },
            })
        } else {
            Err(Error::new(
                &token,
                ErrorKind::InvalidDerefType(right.type_decl),
            ))
        }
    }
}

#[derive(Debug, PartialEq)]
enum ScopeKind {
    Global,
    Loop,
    // (function entry in symbol table, save all gotos so that can error if no matching label)
    Function(FuncSymbol, Vec<Token>),
    // all cases and defaults that are in a switch
    // if Some(value) then case, if None then default
    Switch(Vec<Option<i64>>),
}

// vector to go through and check if certain statements are
// enclosed by others. eg: return only in functions, break only in switch/loops
#[derive(Debug, PartialEq)]
struct Scope(Vec<ScopeKind>);
impl Scope {
    fn increment_stack_size(&mut self, type_decl: &Type) {
        let ScopeKind::Function(func_symbol, _) = find_scope!(self, ScopeKind::Function(..))
            .expect("can only be called inside a function") else {unreachable!()};
        let stack_size = func_symbol.borrow().unwrap_func().stack_size;

        let mut size = stack_size + type_decl.size();
        size = align(size, type_decl);

        func_symbol.borrow_mut().unwrap_func_mut().stack_size = size;
    }
    fn insert_label(&mut self, name_token: &Token) -> Result<FuncSymbol, Error> {
        let name = name_token.unwrap_string();
        let ScopeKind::Function(func_symbol, _) = find_scope!(self,ScopeKind::Function(..))
            .expect("ensured by parser that label is always inside function") else {unreachable!()};

        if func_symbol
            .borrow()
            .unwrap_func()
            .labels
            .contains_key(&name)
        {
            return Err(Error::new(
                name_token,
                ErrorKind::Redefinition("Label", name),
            ));
        }
        let len = func_symbol.borrow().unwrap_func().labels.len();
        func_symbol
            .borrow_mut()
            .unwrap_func_mut()
            .labels
            .insert(name, len);

        Ok(Rc::clone(&func_symbol))
    }
    fn insert_goto(&mut self, name_token: Token) -> Result<FuncSymbol, Error> {
        let ScopeKind::Function(func_symbol, gotos) = find_scope!(self,ScopeKind::Function(..))
            .expect("ensured by parser that label is always inside function") else {unreachable!()};

        gotos.push(name_token);
        Ok(Rc::clone(&func_symbol))
    }
    fn compare_gotos(&mut self) -> Result<(), Error> {
        let ScopeKind::Function(func_symbol, gotos) = find_scope!(self,ScopeKind::Function(..))
            .expect("ensured by parser that label is always inside function") else {unreachable!()};

        for g in gotos {
            let label = g.unwrap_string();
            if !func_symbol
                .borrow()
                .unwrap_func()
                .labels
                .contains_key(&label)
            {
                return Err(Error::new(g, ErrorKind::UndeclaredLabel(label)));
            }
        }
        Ok(())
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

pub fn is_valid_bin(
    operator: &TokenType,
    left_type: &Type,
    right_type: &Type,
    right_expr: &impl hir::expr::IsZero,
) -> bool {
    match (&left_type, &right_type) {
        (Type::Primitive(Primitive::Void), _) | (_, Type::Primitive(Primitive::Void)) => false,
        (Type::Pointer(_), Type::Pointer(_)) => {
            if left_type.type_compatible(right_type, right_expr) {
                operator == &TokenType::Minus
            } else {
                false
            }
        }
        (_, Type::Pointer(_)) => operator == &TokenType::Plus,
        (Type::Pointer(_), _) => operator == &TokenType::Plus || operator == &TokenType::Minus,
        (Type::Struct(..), _)
        | (_, Type::Struct(..))
        | (Type::Union(..), _)
        | (_, Type::Union(..)) => false,
        _ => true,
    }
}

// scale index when pointer arithmetic
pub fn maybe_scale_index<'a, T>(
    left_type: &Type,
    right_type: &Type,
    left_expr: &'a mut T,
    right_expr: &'a mut T,
) -> Option<(&'a mut T, usize)> {
    match (left_type, right_type) {
        (t, Type::Pointer(inner)) if !t.is_ptr() && inner.size() > 1 => {
            Some((left_expr, inner.size()))
        }
        (Type::Pointer(inner), t) if !t.is_ptr() && inner.size() > 1 => {
            Some((right_expr, inner.size()))
        }
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
    use crate::compiler::common::environment::tests::var_template;
    use crate::compiler::common::types::tests::setup_type;
    use crate::compiler::parser::tests::setup;

    macro_rules! assert_type {
        ($input:expr,$expected_type:expr) => {
            let mut parser = setup($input);
            let expr = parser.expression().unwrap();

            let mut typechecker = TypeChecker::new();
            let actual = typechecker.visit_expr(expr).unwrap();
            let expected_type = setup_type($expected_type);

            assert!(
                actual.type_decl == expected_type,
                "actual: {:?}, expected: {}",
                actual,
                expected_type.to_string(),
            );
        };
    }

    macro_rules! assert_type_err {
        ($input:expr,$expected_err:pat) => {
            let mut parser = setup($input);
            let expr = parser.expression().unwrap();

            let mut typechecker = TypeChecker::new();
            let actual = typechecker.visit_expr(expr).unwrap_err();

            assert!(
                matches!(actual.kind, $expected_err),
                "actual: {:?}, expected: {}",
                actual,
                stringify!($expected_err),
            );
        };
    }

    macro_rules! assert_const_expr {
        ($input: expr, $expected: expr, $symbols: expr) => {
            let mut parser = setup($input);
            let expr = parser.expression().unwrap();

            let mut typechecker = TypeChecker::new();
            for (name, ty) in $symbols {
                let (token, symbol) = var_template(name, ty, InitType::Declaration);
                typechecker.env.declare_symbol(&token, symbol).unwrap();
            }

            let mut expr = typechecker.visit_expr(expr).unwrap();

            // have to do manual array decay because is constant expects array to be decayed already
            if let Type::Array { .. } = expr.type_decl {
                expr.kind = mir::expr::ExprKind::Unary {
                    operator: TokenType::Amp,
                    right: Box::new(expr.clone()),
                };
            }

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
        let declarator = typechecker.declarator(specifier_type, is_typedef, decl)?;

        Ok(declarator.unwrap().init.unwrap())
    }
    fn assert_init(actual: mir::decl::Init, expected: Vec<(usize, &'static str, &'static str)>) {
        let mir::decl::Init::Aggr(actual) = actual else {unreachable!()};
        let mut typechecker = TypeChecker::new();

        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert_eq!(actual.1, expected.0);

            let expected_type = setup_type(expected.2);
            let expected_expr = TypeChecker::maybe_cast(
                expected_type,
                typechecker
                    .visit_expr(setup(expected.1).expression().unwrap())
                    .unwrap(),
            );

            assert_eq!(actual.0, expected_expr);
        }
    }

    #[test]
    fn binary_integer_promotion() {
        assert_type!("'1' + '2'", "int");
    }

    #[test]
    fn shift_type() {
        assert_type!("1 << (long)2", "int");
        assert_type!("(long)1 << (char)2", "long");
        assert_type!("'1' << (char)2", "int");
    }

    #[test]
    fn comp_type() {
        assert_type!("1 == (long)2", "int");
        assert_type!("(char*)1 == (char*)2", "int");
        assert_type!("1 <= (long)2", "int");
        assert_type!("(char*)1 > (char*)2", "int");
        assert_type!("(void*)1 == (long*)2", "int");

        assert_type_err!("1 == (long*)2", ErrorKind::InvalidComp(..));
        assert_type_err!("(int*)1 == (long*)2", ErrorKind::InvalidComp(..));
    }

    #[test]
    fn static_constant_test() {
        assert_const_expr!("&a + (int)(3 * 1)", true, vec![("a", "int")]);

        assert_const_expr!("a + (int)(3 * 1)", false, vec![("a", "int*")]);
        assert_const_expr!("\"hi\" + (int)(3 * 1)", true, Vec::new());
        assert_const_expr!("&\"hi\" + (int)(3 * 1)", true, Vec::new());

        assert_const_expr!("(long*)&a", true, vec![("a", "int")]);

        assert_const_expr!("(long*)1 + 3", true, Vec::new());

        assert_const_expr!("&a[3]", true, vec![("a", "int[4]")]);

        assert_const_expr!("*&a[3]", false, vec![("a", "int[4]")]);

        assert_const_expr!(
            "&a.age",
            true,
            vec![(
                "a",
                "struct {
                    int age;
                }"
            )]
        );

        assert_const_expr!(
            "a.age",
            false,
            vec![(
                "a",
                "struct {
                    int age;
                }"
            )]
        );
        assert_const_expr!("*a", false, vec![("a", "int*")]);

        assert_const_expr!("(int *)*a", false, vec![("a", "int*")]);

        assert_const_expr!("*a", true, vec![("a", "int[4][4]")]);
        assert_const_expr!("*&a[3]", true, vec![("a", "int[4][4]")]);

        assert_const_expr!(
            "&a->age",
            true,
            vec![(
                "a",
                "struct {
                    int age;
                }[4]"
            )]
        );

        assert_const_expr!("a", false, vec![("a", "int")]);
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
        let mut scopes = Scope(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![]),
            ScopeKind::Switch(vec![]),
        ]);
        let expected = true;
        let actual = find_scope!(scopes, ScopeKind::Loop).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn doesnt_find_switch() {
        let mut scopes = Scope(vec![ScopeKind::Global, ScopeKind::Loop, ScopeKind::Loop]);
        let expected = false;
        let actual = find_scope!(scopes, ScopeKind::Switch(..)).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn finds_and_mutates_scope() {
        let mut scopes = Scope(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![]),
            ScopeKind::Switch(vec![]),
            ScopeKind::Loop,
        ]);
        let expected = Scope(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![]),
            ScopeKind::Switch(vec![Some(1), None, Some(3)]),
            ScopeKind::Loop,
        ]);
        let ScopeKind::Switch(labels) =
            find_scope!(scopes, ScopeKind::Switch(..)).unwrap() else {unreachable!()};
        labels.push(Some(1));
        labels.push(None);
        labels.push(Some(3));

        assert_eq!(scopes.0.len(), expected.0.len());
        for (actual, expected) in scopes.0.into_iter().zip(expected.0) {
            assert!(match (actual, expected) {
                (ScopeKind::Function(_, g1), ScopeKind::Function(_, g2)) => g1 == g2,
                (l, r) => l == r,
            });
        }
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
