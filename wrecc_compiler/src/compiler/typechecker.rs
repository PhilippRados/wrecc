use crate::compiler::ast::{decl::*, expr::*, stmt::*};
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::wrecc_codegen::codegen::align;
use crate::compiler::wrecc_codegen::register::*;
use std::cmp::Ordering;
use std::collections::HashMap;

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
    scope: ScopeLevel,

    // symbol table
    pub env: Environment,

    // TODO: this should be done via control-flow-graph
    // checks if all paths return from a function
    returns_all_paths: bool,

    // label with its associated label index
    const_labels: HashMap<String, usize>,

    // label index counter
    const_label_count: usize,

    // save encountered switch-statements together with with info about their cases and defaults,
    // so that codegen is simpler
    switches: Vec<Vec<Option<i64>>>,
}

macro_rules! cast {
    ($ex:expr,$new_type:expr,$direction:path) => {
        *$ex = Expr {
            kind: ExprKind::Cast {
                token: Token::default(TokenType::LeftParen),
                direction: Some($direction),
                new_type: $new_type,
                decl_type: DeclType {
                    specifiers: Vec::new(),
                    modifiers: Vec::new(),
                },
                expr: Box::new($ex.clone()),
            },
            type_decl: Some($new_type),
            value_kind: $ex.value_kind.clone(),
        }
    };
}

impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            scope: ScopeLevel(vec![ScopeKind::Global]),
            env: Environment::new(),
            returns_all_paths: false,
            const_labels: HashMap::new(),
            const_label_count: 0,
            switches: Vec::new(),
        }
    }
    pub fn check(
        mut self,
        external_decls: &mut Vec<ExternalDeclaration>,
    ) -> Result<(HashMap<String, usize>, Vec<Vec<Option<i64>>>), Vec<Error>> {
        match self.check_declarations(external_decls) {
            Ok(_) => Ok((self.const_labels, self.switches)),
            Err(e) => Err(e.flatten_multiple()),
        }
    }
    fn check_declarations(
        &mut self,
        external_decls: &mut Vec<ExternalDeclaration>,
    ) -> Result<(), Error> {
        let mut errors = Vec::new();

        for decl in external_decls {
            if let Err(e) = self.visit_decl(decl) {
                errors.push(e);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    fn visit_decl(&mut self, external_decl: &mut ExternalDeclaration) -> Result<(), Error> {
        match external_decl {
            ExternalDeclaration::Declaration(decl) => self.declaration(decl),
            ExternalDeclaration::Function(decl_type, name, body) => {
                self.function_definition(decl_type, name, body)
            }
        }
    }

    fn visit_stmt(&mut self, statement: &mut Stmt) -> Result<(), Error> {
        match statement {
            Stmt::Declaration(decls) => self.declaration(decls),
            Stmt::Return(keyword, value) => self.return_statement(keyword, value),
            Stmt::Expr(expr) => self.expr_type(expr).map(|_| ()),
            Stmt::Block(statements) => {
                self.env.enter();
                self.block(statements)
            }
            Stmt::If(keyword, cond, then_branch, else_branch) => {
                self.if_statement(keyword, cond, then_branch, else_branch)
            }
            Stmt::While(left_paren, cond, body) => self.while_statement(left_paren, cond, body),
            Stmt::Do(keyword, body, cond) => self.do_statement(keyword, body, cond),
            Stmt::For(left_paren, init, cond, inc, body) => {
                self.for_statement(left_paren, init, cond, inc, body)
            }
            Stmt::Break(keyword) => self.break_statement(keyword),
            Stmt::Continue(keyword) => self.continue_statement(keyword),
            Stmt::Switch(keyword, cond, body) => self.switch_statement(keyword, cond, body),
            Stmt::Case(keyword, value, body) => self.case_statement(keyword, value, body),
            Stmt::Default(keyword, body) => self.default_statement(keyword, body),
            Stmt::Goto(label) => self.goto_statement(label),
            Stmt::Label(name, body) => self.label_statement(name, body),
        }
    }
    fn goto_statement(&mut self, label: &Token) -> Result<(), Error> {
        self.scope.insert_goto(label.clone())?;
        Ok(())
    }
    fn label_statement(&mut self, name_token: &Token, body: &mut Stmt) -> Result<(), Error> {
        self.scope.insert_label(name_token)?;
        self.visit_stmt(body)?;
        Ok(())
    }
    fn switch_statement(
        &mut self,
        token: &Token,
        cond: &mut Expr,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_integer() {
            return Err(Error::new(
                token,
                ErrorKind::NotInteger("Switch conditional", cond_type),
            ));
        }
        self.scope.0.push(ScopeKind::Switch(vec![]));
        let err = self.visit_stmt(body);

        let Some(ScopeKind::Switch(labels)) = self.scope.0.pop() else {
            unreachable!("all other scopes should be popped off by themselves")
        };

        self.switches.push(labels);

        err?;

        // TODO: check returns in all paths

        Ok(())
    }
    fn case_statement(
        &mut self,
        token: &Token,
        value: &mut Expr,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        let value = value.get_literal_constant(self, token, "Case value")?;

        match find_scope!(&mut self.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(labels)) => {
                if !labels.contains(&Some(value)) {
                    labels.push(Some(value))
                } else {
                    return Err(Error::new(token, ErrorKind::DuplicateCase(value)));
                }
            }
            _ => {
                return Err(Error::new(token, ErrorKind::NotIn("case", "switch")));
            }
        }

        self.visit_stmt(body)?;
        Ok(())
    }
    fn default_statement(&mut self, token: &Token, body: &mut Stmt) -> Result<(), Error> {
        match find_scope!(&mut self.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(labels)) => {
                if !labels.contains(&None) {
                    labels.push(None)
                } else {
                    return Err(Error::new(token, ErrorKind::MultipleDefaults));
                }
            }
            _ => {
                return Err(Error::new(token, ErrorKind::NotIn("default", "switch")));
            }
        }
        self.visit_stmt(body)?;
        Ok(())
    }
    fn do_statement(
        &mut self,
        token: &Token,
        body: &mut Stmt,
        cond: &mut Expr,
    ) -> Result<(), Error> {
        self.scope.0.push(ScopeKind::Loop);
        self.visit_stmt(body)?;
        self.scope.0.pop();

        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                token,
                ErrorKind::NotScalar("Conditional", cond_type),
            ));
        }

        self.returns_all_paths = false;

        Ok(())
    }
    fn for_statement(
        &mut self,
        left_paren: &Token,
        init: &mut Option<Box<Stmt>>,
        cond: &mut Option<Expr>,
        inc: &mut Option<Expr>,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        self.env.enter();

        if let Some(init) = init {
            self.visit_stmt(&mut *init)?;
        }
        if let Some(cond) = cond {
            let cond_type = self.expr_type(cond)?;
            if !cond_type.is_scalar() {
                return Err(Error::new(
                    left_paren,
                    ErrorKind::NotScalar("Conditional", cond_type),
                ));
            }
        }

        self.scope.0.push(ScopeKind::Loop);
        self.visit_stmt(body)?;

        if let Some(inc) = inc {
            self.expr_type(inc)?;
        }

        self.scope.0.pop();
        self.env.exit();

        self.returns_all_paths = false;
        Ok(())
    }
    fn break_statement(&mut self, token: &Token) -> Result<(), Error> {
        if find_scope!(&mut self.scope, ScopeKind::Loop | ScopeKind::Switch(..)).is_none() {
            Err(Error::new(
                token,
                ErrorKind::NotIn("break", "loop/switch-statement"),
            ))
        } else {
            Ok(())
        }
    }
    fn continue_statement(&mut self, token: &Token) -> Result<(), Error> {
        if find_scope!(&mut self.scope, ScopeKind::Loop).is_none() {
            Err(Error::new(token, ErrorKind::NotIn("continue", "loop")))
        } else {
            Ok(())
        }
    }

    fn while_statement(
        &mut self,
        left_paren: &Token,
        cond: &mut Expr,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                left_paren,
                ErrorKind::NotScalar("Conditional", cond_type),
            ));
        }

        self.scope.0.push(ScopeKind::Loop);
        self.visit_stmt(body)?;
        self.scope.0.pop();

        self.returns_all_paths = false;
        Ok(())
    }

    fn declaration(&mut self, decl: &mut Declaration) -> Result<(), Error> {
        let specifier_type = self.parse_specifiers(decl.specifiers.clone())?;

        for declarator in &mut decl.declarators {
            self.declarator(specifier_type.clone(), decl.is_typedef, declarator)?;
        }

        Ok(())
    }
    fn declarator(
        &mut self,
        specifier_type: NEWTypes,
        is_typedef: bool,
        (declarator, init): &mut (Declarator, Option<Init>),
    ) -> Result<(), Error> {
        let parsed_type = self.parse_modifiers(specifier_type, &mut declarator.modifiers)?;

        if let Some(name) = &mut declarator.name {
            let symbol = if is_typedef {
                Symbols::TypeDef(parsed_type.clone())
            } else if let NEWTypes::Function { return_type, params, variadic } = parsed_type.clone()
            {
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

            let already_exists = self
                .env
                .symbols
                .get_current(&name.unwrap_string())
                .is_some();
            let entry = self.env.declare_symbol(&name, symbol)?;
            name.token.update_entry(TableEntry::Symbol(entry));

            let is_var = !parsed_type.is_func() && !is_typedef;

            if let Some(init) = init {
                if !is_var {
                    return Err(Error::new(
                        name,
                        ErrorKind::Regular("Only variables can be initialized"),
                    ));
                }
                if !parsed_type.is_complete() {
                    return Err(Error::new(name, ErrorKind::IncompleteType(parsed_type)));
                }

                self.init_check(&parsed_type, init)?;
            } else if is_var {
                let tentative_decl = self.env.is_global() && parsed_type.is_aggregate();
                if !parsed_type.is_complete() && !tentative_decl {
                    return Err(Error::new(name, ErrorKind::IncompleteType(parsed_type)));
                }
            }

            if is_var && !self.env.is_global() && !already_exists {
                self.scope.increment_stack_size(&parsed_type);
            }
        }

        Ok(())
    }
    pub fn parse_type(&mut self, decl_type: &mut DeclType) -> Result<NEWTypes, Error> {
        let specifier_type = self.parse_specifiers(decl_type.specifiers.clone())?;
        let parsed_type = self.parse_modifiers(specifier_type, &mut decl_type.modifiers)?;

        Ok(parsed_type)
    }
    fn parse_specifiers(&mut self, specifiers: Vec<DeclSpecifier>) -> Result<NEWTypes, Error> {
        if specifiers.is_empty() {
            return Ok(NEWTypes::Primitive(Types::Int));
        }

        let token = specifiers[0].token.clone();

        let mut specifier_kind_list: Vec<SpecifierKind> =
            specifiers.into_iter().map(|spec| spec.kind).collect();

        specifier_kind_list.sort_by(|s1, s2| s2.order().cmp(&s1.order()));

        match specifier_kind_list.as_slice() {
            [SpecifierKind::Struct(name, members)] | [SpecifierKind::Union(name, members)] => {
                self.struct_or_union_specifier(token, name, members)
            }
            [SpecifierKind::Enum(name, enum_constants)] => {
                self.enum_specifier(token, name, enum_constants)
            }
            [SpecifierKind::UserType] => {
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

            [SpecifierKind::Void] => Ok(NEWTypes::Primitive(Types::Void)),
            [SpecifierKind::Char] => Ok(NEWTypes::Primitive(Types::Char)),
            [SpecifierKind::Int] => Ok(NEWTypes::Primitive(Types::Int)),
            [SpecifierKind::Long]
            | [SpecifierKind::Long, SpecifierKind::Int]
            | [SpecifierKind::Long, SpecifierKind::Long]
            | [SpecifierKind::Long, SpecifierKind::Long, SpecifierKind::Int] => {
                Ok(NEWTypes::Primitive(Types::Long))
            }
            _ => Err(Error::new(
                &token,
                ErrorKind::Regular("Invalid combination of type-specifiers"),
            )),
        }
    }
    fn parse_modifiers(
        &mut self,
        mut parsed_type: NEWTypes,
        modifiers: &mut Vec<DeclModifier>,
    ) -> Result<NEWTypes, Error> {
        for m in modifiers {
            parsed_type = match m {
                DeclModifier::Pointer => parsed_type.pointer_to(),
                DeclModifier::Array(token, expr) => {
                    let size = expr.get_literal_constant(self, token, "Array size specifier")?;

                    if parsed_type.is_func() {
                        return Err(Error::new(token, ErrorKind::InvalidArray(parsed_type)));
                    }

                    if size > 0 {
                        parsed_type.array_of(size as usize)
                    } else {
                        return Err(Error::new(token, ErrorKind::NegativeArraySize));
                    }
                }
                DeclModifier::Function { token, params, variadic } => {
                    // func-params have own scope (their types too)
                    self.env.enter();
                    let params = self.parse_params(&token, params)?;
                    self.env.exit();

                    if parsed_type.is_func() || parsed_type.is_array() {
                        return Err(Error::new(token, ErrorKind::InvalidReturnType(parsed_type)));
                    }

                    parsed_type.function_of(params, *variadic)
                }
            };
        }

        Ok(parsed_type)
    }
    fn struct_or_union_specifier(
        &mut self,
        token: Token,
        name: &Option<Token>,
        members: &Option<Vec<MemberDeclaration>>,
    ) -> Result<NEWTypes, Error> {
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
            TokenType::Struct => NEWTypes::Struct(members),
            TokenType::Union => NEWTypes::Union(members),
            _ => unreachable!("not struct/union specifier"),
        })
    }
    fn struct_declaration(
        &mut self,
        members: Vec<MemberDeclaration>,
    ) -> Result<Vec<(NEWTypes, Token)>, Error> {
        let mut parsed_members = Vec::new();

        for (spec, declarators) in members {
            let specifier_type = self.parse_specifiers(spec)?;

            for Declarator { name, mut modifiers } in declarators {
                let parsed_type = self.parse_modifiers(specifier_type.clone(), &mut modifiers)?;
                let name = name.expect("cannot have abstract declarators in structs");

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
    fn check_duplicate_members(vec: &Vec<(NEWTypes, Token)>) -> Result<(), Error> {
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
        constants: &Option<Vec<(Token, Option<Expr>)>>,
    ) -> Result<NEWTypes, Error> {
        match (&name, constants) {
            (Some(name), Some(values)) => {
                let members = self.enumerator_list(values.clone())?;
                self.env.declare_type(name, Tags::Enum(members.clone()))?;

                Ok(NEWTypes::Enum(Some(name.unwrap_string()), members))
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

                Ok(NEWTypes::Enum(Some(name.unwrap_string()), constants))
            }
            (None, Some(values)) => Ok(NEWTypes::Enum(None, self.enumerator_list(values.clone())?)),
            (None, None) => Err(Error::new(
                &token,
                ErrorKind::EmptyAggregate(token.token.clone()),
            )),
        }
    }
    fn enumerator_list(
        &mut self,
        constants: Vec<(Token, Option<Expr>)>,
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
                    type_decl: NEWTypes::Primitive(Types::Int),
                    kind: InitType::Definition,
                    is_global: self.env.is_global(),
                    reg: Some(Register::Literal(
                        index as i64,
                        NEWTypes::Primitive(Types::Int),
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
        params: &mut Vec<(Vec<DeclSpecifier>, Declarator)>,
    ) -> Result<Vec<(NEWTypes, Option<Token>)>, Error> {
        let mut parsed_params = Vec::new();

        for (specifiers, declarator) in params {
            let specifier_type = self.parse_specifiers(specifiers.clone())?;
            let mut parsed_type =
                self.parse_modifiers(specifier_type, &mut declarator.modifiers)?;

            parsed_type = match parsed_type {
                NEWTypes::Array { of, .. } => of.pointer_to(),
                NEWTypes::Function { .. } => parsed_type.pointer_to(),
                ty => ty,
            };

            if let Some(name) = &mut declarator.name {
                // insert parameters into symbol table
                let symbol = self.env.declare_symbol(
                    name,
                    Symbols::Variable(SymbolInfo {
                        token: name.clone(),
                        type_decl: parsed_type.clone(),
                        kind: InitType::Declaration,
                        is_global: false,
                        reg: None,
                    }),
                )?;
                name.token.update_entry(TableEntry::Symbol(symbol));
            }

            parsed_params.push((parsed_type, declarator.name.clone()));
        }

        // single unnamed void param is equivalent to empty params
        if let [(NEWTypes::Primitive(Types::Void), None)] = parsed_params.as_slice() {
            parsed_params.pop();
        } else if parsed_params
            .iter()
            .any(|(type_decl, _)| type_decl.is_void())
        {
            return Err(Error::new(token, ErrorKind::VoidFuncArg));
        }

        Ok(parsed_params)
    }

    fn init_check(&mut self, type_decl: &NEWTypes, init: &mut Init) -> Result<(), Error> {
        if let Some((amount, s)) = Self::is_string_init(type_decl, init)? {
            init.kind = Self::char_array(init.token.clone(), s, amount)?;
        }

        match &mut init.kind {
            InitKind::Scalar(expr) => self.init_scalar(type_decl, &init.token, expr),
            InitKind::Aggr(list) => self.init_aggregate(type_decl, &init.token, list),
        }
    }
    fn init_scalar(
        &mut self,
        type_decl: &NEWTypes,
        token: &Token,
        expr: &mut Expr,
    ) -> Result<(), Error> {
        let mut value_type = self.expr_type(expr)?;

        crate::arr_decay!(value_type, expr, token);
        self.check_type_compatibility(token, type_decl, &value_type, &expr.kind)?;
        self.maybe_cast(type_decl, &value_type, expr);

        if self.env.is_global() && !is_constant(expr) {
            return Err(Error::new(
                token,
                ErrorKind::NotConstantInit("Global variables"),
            ));
        }

        Ok(())
    }
    fn init_aggregate(
        &mut self,
        type_decl: &NEWTypes,
        token: &Token,
        list: &mut Vec<Box<Init>>,
    ) -> Result<(), Error> {
        match type_decl {
            NEWTypes::Array { .. } | NEWTypes::Struct(_) | NEWTypes::Union(_) => {
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
                    if let InitKind::Scalar(ref mut expr) = first.kind.clone() {
                        let r_type = self.expr_type(expr)?;
                        let mut l_expr = Expr::new(ExprKind::Nop, ValueKind::Lvalue); // placeholder expression

                        while !sub_type.is_scalar()
                            && Self::is_string_init(sub_type, first)?.is_none()
                            && self
                                .assign_var(
                                    &mut l_expr,
                                    sub_type.clone(),
                                    token,
                                    expr,
                                    r_type.clone(),
                                )
                                .is_err()
                        {
                            let new_sub_type = objects.current_type().at(0).unwrap();
                            objects.0.push((0, 0, new_sub_type));

                            sub_type = objects.current_type();
                        }
                    }

                    let mut init = Init {
                        offset: objects.offset(),
                        ..*list.remove(0)
                    };

                    self.init_check(sub_type, &mut init)?;

                    // remove overriding elements
                    let init_interval =
                        if let Some((offset, size)) = find_same_union(&new_list, &objects) {
                            offset..offset + size as i64
                        } else {
                            init.offset..init.offset + sub_type.size() as i64
                        };
                    new_list.retain(|(_, init): &(_, Init)| !init_interval.contains(&init.offset));

                    // push init elements into new_list
                    if let InitKind::Aggr(mut list) = init.kind {
                        list.iter_mut()
                            .for_each(|nested_init| nested_init.offset += init.offset);
                        for init in list {
                            new_list.push((objects.clone(), *init))
                        }
                    } else {
                        new_list.push((objects.clone(), init))
                    }

                    // pop off sub-type
                    objects.0.pop();
                    objects.update_current();
                }

                new_list.sort_by(|(_, init1), (_, init2)| init1.offset.cmp(&init2.offset));
                *list = new_list
                    .into_iter()
                    .map(|(_, init)| Box::new(init))
                    .collect();
                Ok(())
            }
            _ => match list.as_mut_slice() {
                [single_init] if matches!(single_init.kind, InitKind::Scalar(_)) => {
                    self.init_check(type_decl, single_init)
                }
                [single_init] => Err(Error::new(
                    &single_init.token,
                    ErrorKind::Regular("Too many braces around scalar initializer"),
                )),
                [_, second_init, ..] => {
                    Err(Error::new(&second_init.token, ErrorKind::ScalarOverflow))
                }
                [] => Err(Error::new(
                    token,
                    ErrorKind::Regular("Scalar initializer cannot be empty"),
                )),
            },
        }
    }

    fn designator_index(
        &mut self,
        type_decl: &NEWTypes,
        designator: Designator,
    ) -> Result<(i64, i64, NEWTypes), Error> {
        match (designator.kind, type_decl) {
            (DesignatorKind::Array(mut expr), NEWTypes::Array { amount, of }) => {
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
            (DesignatorKind::Member(_), NEWTypes::Array { .. }) => Err(Error::new(
                &designator.token,
                ErrorKind::Regular(
                    "Can only use member designator on type 'struct' and 'union' not 'array'",
                ),
            )),

            (DesignatorKind::Array(_), NEWTypes::Struct(_) | NEWTypes::Union(_)) => {
                Err(Error::new(
                    &designator.token,
                    ErrorKind::InvalidArrayDesignator(type_decl.clone()),
                ))
            }
            (DesignatorKind::Member(m), NEWTypes::Struct(s) | NEWTypes::Union(s)) => {
                if let Some(i) = s
                    .members()
                    .iter()
                    .position(|(_, m_token)| *m == m_token.unwrap_string())
                {
                    // unions only have single index
                    if let NEWTypes::Union(_) = type_decl {
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
    fn is_string_init(type_decl: &NEWTypes, init: &Init) -> Result<Option<(usize, String)>, Error> {
        if let Some(amount) = type_decl.is_char_array() {
            match &init.kind {
                InitKind::Scalar(Expr { kind: ExprKind::String(s), .. }) => {
                    return Ok(Some((amount, s.unwrap_string())))
                }
                InitKind::Aggr(list) => match list.as_slice() {
                    [single_init] if single_init.designator.is_none() => {
                        if let InitKind::Scalar(Expr { kind: ExprKind::String(s), .. }) =
                            &single_init.kind
                        {
                            return Ok(Some((amount, s.unwrap_string())));
                        }
                    }
                    [first_init, second_init] if first_init.designator.is_none() => {
                        if let InitKind::Scalar(Expr { kind: ExprKind::String(_), .. }) =
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
    fn char_array(token: Token, mut s: String, amount: usize) -> Result<InitKind, Error> {
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

        Ok(InitKind::Aggr(
            s.as_bytes()
                .iter()
                .map(|c| {
                    Box::new(Init {
                        token: token.clone(),
                        kind: InitKind::Scalar(Expr::new_literal(*c as i64, Types::Char)),
                        designator: None,
                        offset: 0,
                    })
                })
                .collect(),
        ))
    }

    fn check_type_compatibility(
        &self,
        token: &Token,
        left: &NEWTypes,
        right: &NEWTypes,
        right_expr: &ExprKind,
    ) -> Result<(), Error> {
        if left.is_void() || right.is_void() || !left.type_compatible(right, right_expr) {
            Err(Error::new(
                token,
                ErrorKind::IllegalAssign(left.clone(), right.clone()),
            ))
        } else {
            Ok(())
        }
    }
    // TODO: display warning when casting down
    fn explicit_cast(
        &mut self,
        token: &Token,
        expr: &mut Expr,
        decl_type: &mut DeclType,
        new_type: &mut NEWTypes,
        direction: &mut Option<CastDirection>,
    ) -> Result<NEWTypes, Error> {
        let mut old_type = self.expr_type(expr)?;
        *new_type = self.parse_type(decl_type)?;

        crate::arr_decay!(old_type, expr, token);

        if !new_type.is_void() && (!old_type.is_scalar() || !new_type.is_scalar()) {
            return Err(Error::new(
                token,
                ErrorKind::InvalidExplicitCast(old_type, new_type.clone()),
            ));
        }

        *direction = Some(match old_type.size().cmp(&new_type.size()) {
            Ordering::Less => CastDirection::Up,
            Ordering::Greater => CastDirection::Down,
            Ordering::Equal => CastDirection::Equal,
        });
        Ok(new_type.clone())
    }
    fn maybe_cast(&self, new_type: &NEWTypes, old_type: &NEWTypes, expr: &mut Expr) {
        match old_type.size().cmp(&new_type.size()) {
            Ordering::Less => cast!(expr, new_type.clone(), CastDirection::Up),
            Ordering::Greater => cast!(expr, new_type.clone(), CastDirection::Down),
            Ordering::Equal => (),
        }
    }
    fn if_statement(
        &mut self,
        keyword: &Token,
        cond: &mut Expr,
        then_branch: &mut Stmt,
        else_branch: &mut Option<Box<Stmt>>,
    ) -> Result<(), Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                keyword,
                ErrorKind::NotScalar("Conditional", cond_type),
            ));
        }

        self.visit_stmt(then_branch)?;
        let then_return = self.returns_all_paths;
        self.returns_all_paths = false;

        if let Some(else_branch) = else_branch {
            self.visit_stmt(else_branch)?;
            let else_return = self.returns_all_paths;

            if !then_return || !else_return {
                self.returns_all_paths = false;
            }
        }
        Ok(())
    }
    fn function_definition(
        &mut self,
        decl_type: &mut DeclType,
        name: &mut Token,
        body: &mut Vec<Stmt>,
    ) -> Result<(), Error> {
        let Some(DeclModifier::Function { mut params, variadic,token }) = decl_type.modifiers.pop() else {
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
                name,
                ErrorKind::IncompleteReturnType(name.unwrap_string(), return_type),
            ));
        }

        // have to push scope before declaring local variables
        self.env.enter();

        let params = self.parse_params(&token, &mut params)?;

        if let Some(param_type) = params
            .iter()
            .map(|(type_decl, _)| type_decl)
            .find(|type_decl| !type_decl.is_complete())
        {
            return Err(Error::new(
                name,
                ErrorKind::IncompleteFuncArg(name.unwrap_string(), param_type.clone()),
            ));
        }

        if params
            .iter()
            .map(|(_, name)| name)
            .any(|name| name.is_none())
        {
            return Err(Error::new(name, ErrorKind::UnnamedFuncParams));
        }

        let func = Function::new(
            return_type.clone(),
            params.clone(),
            variadic,
            InitType::Definition,
        );

        let symbol = self.env.declare_global(name, Symbols::Func(func))?;
        name.token.update_entry(TableEntry::Symbol(symbol.clone()));

        self.scope.0.push(ScopeKind::Function(
            name.clone(),
            return_type.clone(),
            Vec::new(),
        ));
        for (type_decl, _) in params.iter().by_ref() {
            self.scope.increment_stack_size(type_decl);
        }

        // check function body
        let err = self.block(body);

        self.scope.compare_gotos()?;
        self.scope.0.pop();

        err?;

        self.main_returns_int(name, &return_type)?;
        self.implicit_return_main(name, body);

        if !return_type.is_void() && !self.returns_all_paths {
            Err(Error::new(
                name,
                ErrorKind::NoReturnAllPaths(name.unwrap_string()),
            ))
        } else {
            self.returns_all_paths = false;
            Ok(())
        }
    }
    fn main_returns_int(&self, name_token: &Token, return_type: &NEWTypes) -> Result<(), Error> {
        if name_token.unwrap_string() == "main" && *return_type != NEWTypes::Primitive(Types::Int) {
            Err(Error::new(
                name_token,
                ErrorKind::InvalidMainReturn(return_type.clone()),
            ))
        } else {
            Ok(())
        }
    }
    fn implicit_return_main(&mut self, name_token: &Token, body: &mut Vec<Stmt>) {
        if name_token.unwrap_string() == "main" && !self.returns_all_paths {
            self.returns_all_paths = true;

            body.push(Stmt::Return(
                name_token.clone(),
                Some(Expr::new_literal(0, Types::Int)),
            ));
        }
    }
    fn return_statement(&mut self, keyword: &Token, expr: &mut Option<Expr>) -> Result<(), Error> {
        self.returns_all_paths = true;

        let Some(ScopeKind::Function(_,function_type,_)) = find_scope!(&mut self.scope, ScopeKind::Function(..)) else {
            unreachable!("parser ensures that statements can only be contained in functions");
        };
        let function_type = function_type.clone();

        if let Some(expr) = expr {
            let mut body_return = self.expr_type(expr)?;

            crate::arr_decay!(body_return, expr, keyword);
            self.check_return_compatibility(keyword, &function_type, &body_return, &expr.kind)?;
            self.maybe_cast(&function_type, &body_return, expr);
        } else {
            let body_return = &NEWTypes::Primitive(Types::Void);
            let return_expr = ExprKind::Nop;

            self.check_return_compatibility(keyword, &function_type, &body_return, &return_expr)?;
        }
        Ok(())
    }

    pub fn expr_type(&mut self, ast: &mut Expr) -> Result<NEWTypes, Error> {
        ast.integer_const_fold(self)?;

        ast.type_decl = Some(match &mut ast.kind {
            ExprKind::Binary { left, token, right } => {
                let (type_decl, scale_factor) = self.evaluate_binary(left, token, right)?;
                Self::maybe_scale_result(scale_factor, ast);
                type_decl
            }
            ExprKind::Unary { token, right } => {
                self.evaluate_unary(token, right, &mut ast.value_kind)?
            }
            ExprKind::Grouping { expr } => self.evaluate_grouping(expr)?,
            ExprKind::Literal(_) => ast.type_decl.clone().unwrap(),
            ExprKind::String(token) => self.string(token.unwrap_string())?,
            ExprKind::Logical { left, token, right } => {
                self.evaluate_logical(left, token, right)?
            }
            ExprKind::Comparison { left, token, right } => {
                self.evaluate_comparison(left, token, right)?
            }
            ExprKind::Ident(token) => self.ident(token)?,
            ExprKind::Assign { l_expr, token, r_expr } => {
                let l_type = self.expr_type(l_expr)?;
                let r_type = self.expr_type(r_expr)?;

                self.assign_var(l_expr, l_type, token, r_expr, r_type)?
            }
            ExprKind::CompoundAssign { l_expr, token, r_expr } => {
                self.compound_assign(l_expr, token, r_expr)?
            }
            ExprKind::Call { left_paren, name, args } => {
                self.evaluate_call(left_paren, name, args)?
            }
            ExprKind::PostUnary { left, token, by_amount } => {
                self.evaluate_postunary(token, left, by_amount)?
            }
            ExprKind::MemberAccess { token, expr, member } => {
                self.member_access(token, member, expr)?
            }
            ExprKind::Cast {
                token,
                decl_type,
                expr,
                direction,
                new_type,
            } => self.explicit_cast(token, expr, decl_type, new_type, direction)?,
            ExprKind::Ternary { token, cond, true_expr, false_expr } => {
                self.ternary(token, cond, true_expr, false_expr)?
            }
            ExprKind::Comma { left, right } => self.comma(left, right)?,
            // doesn't matter because it can only occur in expression-statements where type doesn't matter
            ExprKind::Nop { .. } => NEWTypes::Primitive(Types::Void),
            ExprKind::SizeofType { .. } => NEWTypes::Primitive(Types::Long),
            ExprKind::SizeofExpr { expr, value } => self.sizeof_expr(expr, value)?,
            ExprKind::ScaleUp { .. } => unreachable!("is only used in codegen"),
            ExprKind::ScaleDown { .. } => unreachable!("is only used in codegen"),
        });

        Ok(ast.type_decl.clone().unwrap())
    }
    fn sizeof_expr(&mut self, expr: &mut Expr, value: &mut usize) -> Result<NEWTypes, Error> {
        let expr_type = self.expr_type(expr)?;
        *value = expr_type.size();

        Ok(NEWTypes::Primitive(Types::Long))
    }
    fn comma(&mut self, left: &mut Expr, right: &mut Expr) -> Result<NEWTypes, Error> {
        self.expr_type(left)?;

        self.expr_type(right)
    }
    fn ternary(
        &mut self,
        token: &Token,
        cond: &mut Expr,
        true_expr: &mut Expr,
        false_expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                token,
                ErrorKind::NotScalar("Conditional", cond_type),
            ));
        }
        let mut true_type = self.expr_type(true_expr)?;
        let mut false_type = self.expr_type(false_expr)?;

        if !true_type.type_compatible(&false_type, &false_expr.kind) {
            return Err(Error::new(
                token,
                ErrorKind::TypeMismatch(true_type, false_type),
            ));
        }

        self.maybe_int_promote(true_expr, &mut true_type);
        self.maybe_int_promote(false_expr, &mut false_type);

        match true_type.size().cmp(&false_type.size()) {
            Ordering::Greater => {
                cast!(false_expr, true_type.clone(), CastDirection::Up);
                Ok(true_type)
            }
            Ordering::Less => {
                cast!(true_expr, false_type.clone(), CastDirection::Up);
                Ok(false_type)
            }
            Ordering::Equal => Ok(true_type),
        }
    }
    fn ident(&mut self, token: &mut Token) -> Result<NEWTypes, Error> {
        let symbol = self.env.get_symbol(token)?;
        token.token.update_entry(TableEntry::Symbol(symbol.clone()));

        return match &*symbol.borrow() {
            Symbols::Variable(v) => Ok(v.get_type()),
            Symbols::TypeDef(..) | Symbols::Func(..) => Err(Error::new(
                token,
                ErrorKind::InvalidSymbol(token.unwrap_string(), "variable"),
            )),
        };
    }
    fn member_access(
        &mut self,
        token: &Token,
        member: &Token,
        expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let expr_type = self.expr_type(expr)?;

        if !expr_type.is_complete() {
            return Err(Error::new(
                token,
                ErrorKind::IncompleteMemberAccess(expr_type),
            ));
        }

        match expr_type.clone() {
            NEWTypes::Struct(s) | NEWTypes::Union(s) => {
                let member = member.unwrap_string();

                if let Some((member_type, _)) = s
                    .members()
                    .iter()
                    .find(|(_, name)| name.unwrap_string() == member)
                {
                    Ok(member_type.clone())
                } else {
                    Err(Error::new(
                        token,
                        ErrorKind::NonExistantMember(member, expr_type),
                    ))
                }
            }
            _ => Err(Error::new(token, ErrorKind::InvalidMemberAccess(expr_type))),
        }
    }
    fn evaluate_postunary(
        &mut self,
        token: &Token,
        expr: &mut Expr,
        by_amount: &mut usize,
    ) -> Result<NEWTypes, Error> {
        let expr_type = self.expr_type(expr)?;

        if matches!(expr_type, NEWTypes::Array { .. } | NEWTypes::Struct(..)) {
            return Err(Error::new(
                token,
                ErrorKind::InvalidIncrementType(expr_type),
            ));
        } else if expr.value_kind == ValueKind::Rvalue {
            return Err(Error::new(token, ErrorKind::InvalidRvalueIncrement));
        }

        // scale depending on type-size
        if let NEWTypes::Pointer(inner) = &expr_type {
            *by_amount *= inner.size()
        }

        Ok(expr_type)
    }
    fn string(&mut self, data: String) -> Result<NEWTypes, Error> {
        let len = data.len() + 1; // extra byte for \0-Terminator
        self.const_labels
            .insert(data, create_label(&mut self.const_label_count));

        Ok(NEWTypes::Array {
            of: Box::new(NEWTypes::Primitive(Types::Char)),
            amount: len,
        })
    }
    fn compound_assign(
        &mut self,
        l_expr: &mut Expr,
        token: &Token,
        r_expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        // create temporary-expression so that l_expr isn't overwritten
        let mut tmp = l_expr.clone();

        let l_type = self.expr_type(l_expr)?;

        // convert compound token into valid binary token
        let bin_token = &Token {
            token: token.comp_to_binary(),
            ..token.clone()
        };

        // can ignore scale-down because ptr -= ptr is a type-error
        let r_type = self.evaluate_binary(&mut tmp, bin_token, r_expr)?.0;

        // have to clone r_expr so that change from evaluate_binary isn't overwritten
        let type_decl = self.assign_var(l_expr, l_type, token, &mut r_expr.clone(), r_type)?;

        Ok(type_decl)
    }
    fn assign_var(
        &mut self,
        l_expr: &mut Expr,
        l_type: NEWTypes,
        token: &Token,
        r_expr: &mut Expr,
        mut r_type: NEWTypes,
    ) -> Result<NEWTypes, Error> {
        if matches!(l_type, NEWTypes::Array { .. }) {
            return Err(Error::new(token, ErrorKind::NotAssignable(l_type)));
        }

        if l_expr.value_kind != ValueKind::Lvalue {
            return Err(Error::new(token, ErrorKind::NotLvalue));
        }

        crate::arr_decay!(r_type, r_expr, token);

        self.check_type_compatibility(token, &l_type, &r_type, &r_expr.kind)?;
        self.maybe_cast(&l_type, &r_type, r_expr);

        Ok(l_type)
    }

    fn evaluate_call(
        &mut self,
        left_paren: &Token,
        func_name: &mut Token,
        args: &mut Vec<Expr>,
    ) -> Result<NEWTypes, Error> {
        let mut arg_types: Vec<(&mut Expr, NEWTypes)> = Vec::new();
        for expr in args.iter_mut() {
            let mut t = self.expr_type(expr)?;

            crate::arr_decay!(t, expr, left_paren);
            self.maybe_int_promote(expr, &mut t);
            arg_types.push((expr, t));
        }

        let symbol = self.env.get_symbol(func_name)?;
        func_name
            .token
            .update_entry(TableEntry::Symbol(symbol.clone()));

        return match &*symbol.borrow() {
            Symbols::Variable(_) | Symbols::TypeDef(..) => Err(Error::new(
                left_paren,
                ErrorKind::InvalidSymbol(func_name.unwrap_string(), "function"),
            )),
            Symbols::Func(function) => {
                if (function.variadic && function.arity() <= arg_types.len())
                    || (!function.variadic && function.arity() == arg_types.len())
                {
                    self.args_and_params_match(
                        left_paren,
                        func_name.unwrap_string(),
                        &function.clone().params,
                        arg_types,
                    )?;

                    Ok(function.clone().return_type)
                } else {
                    Err(Error::new(
                        left_paren,
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
        params: &[(NEWTypes, Option<Token>)],
        args: Vec<(&mut Expr, NEWTypes)>,
    ) -> Result<(), Error> {
        for (index, ((expr, arg_type), (param_type, param_token))) in
            args.into_iter().zip(params).enumerate()
        {
            self.check_type_compatibility(left_paren, param_type, &arg_type, &expr.kind)
                .or(Err(Error::new(
                    left_paren,
                    ErrorKind::MismatchedArgs(
                        index,
                        func_name.clone(),
                        param_token.clone(),
                        param_type.clone(),
                        arg_type.clone(),
                    ),
                )))?;

            // since char is integer promoted don't cast it back down
            if param_type.size() > NEWTypes::Primitive(Types::Char).size() {
                self.maybe_cast(param_type, &arg_type, expr);
            }
        }
        Ok(())
    }
    fn block(&mut self, body: &mut Vec<Stmt>) -> Result<(), Error> {
        let mut errors = vec![];

        for stmt in body {
            if let Err(e) = self.visit_stmt(stmt) {
                errors.push(e);
            }
        }

        self.env.exit();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(Error::new_multiple(errors))
        }
    }

    fn evaluate_logical(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let left_type = self.expr_type(left)?;
        let right_type = self.expr_type(right)?;

        Self::lval_to_rval(left);
        Self::lval_to_rval(right);

        if !left_type.is_scalar() || !right_type.is_scalar() {
            return Err(Error::new(
                token,
                ErrorKind::InvalidLogical(token.token.clone(), left_type, right_type),
            ));
        }

        Ok(NEWTypes::Primitive(Types::Int))
    }
    fn evaluate_comparison(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let mut left_type = self.expr_type(left)?;
        let mut right_type = self.expr_type(right)?;

        Self::lval_to_rval(left);
        Self::lval_to_rval(right);

        crate::arr_decay!(left_type, left, token);
        crate::arr_decay!(right_type, right, token);

        if self
            .check_type_compatibility(token, &left_type, &right_type, &right.kind)
            .is_err()
        {
            return Err(Error::new(
                token,
                ErrorKind::InvalidComp(token.token.clone(), left_type, right_type),
            ));
        }

        self.maybe_int_promote(left, &mut left_type);
        self.maybe_int_promote(right, &mut right_type);

        match left_type.size().cmp(&right_type.size()) {
            Ordering::Greater => {
                cast!(right, left_type.clone(), CastDirection::Up);
            }
            Ordering::Less => {
                cast!(left, right_type.clone(), CastDirection::Up);
            }
            Ordering::Equal => (),
        }

        Ok(NEWTypes::Primitive(Types::Int))
    }
    fn lval_to_rval(expr: &mut Expr) {
        expr.value_kind = ValueKind::Rvalue;
    }
    fn evaluate_binary(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<(NEWTypes, Option<usize>), Error> {
        let mut left_type = self.expr_type(left)?;
        let mut right_type = self.expr_type(right)?;

        Self::lval_to_rval(left);
        Self::lval_to_rval(right);

        crate::arr_decay!(left_type, left, token);
        crate::arr_decay!(right_type, right, token);

        // check valid operations
        if !is_valid_bin(token, &left_type, &right_type, &right.kind) {
            return Err(Error::new(
                token,
                ErrorKind::InvalidBinary(token.token.clone(), left_type, right_type),
            ));
        }

        self.maybe_int_promote(left, &mut left_type);
        self.maybe_int_promote(right, &mut right_type);

        // scale index when pointer arithmetic
        if let Some((expr, amount)) = maybe_scale(&left_type, &right_type, left, right) {
            expr.kind = ExprKind::ScaleUp { by: amount, expr: Box::new(expr.clone()) };
        }

        Ok(Self::binary_type_promotion(
            &token.token,
            left_type,
            right_type,
            left,
            right,
        ))
    }
    fn binary_type_promotion(
        token: &TokenType,
        left_type: NEWTypes,
        right_type: NEWTypes,
        left: &mut Expr,
        right: &mut Expr,
    ) -> (NEWTypes, Option<usize>) {
        match (&left_type, &right_type, token) {
            (.., TokenType::GreaterGreater | TokenType::LessLess) => (left_type, None),

            // if pointer - pointer, scale result before operation to match left-pointers type
            (NEWTypes::Pointer(inner), NEWTypes::Pointer(_), _) => {
                (NEWTypes::Primitive(Types::Long), Some(inner.size()))
            }
            // if integer type and pointer always cast to pointer
            (_, NEWTypes::Pointer(_), _) => {
                cast!(left, right_type.clone(), CastDirection::Up);
                (right_type, None)
            }
            (NEWTypes::Pointer(_), ..) => {
                cast!(right, left_type.clone(), CastDirection::Up);
                (left_type, None)
            }

            (l, r, _) if l.size() > r.size() => {
                cast!(right, left_type.clone(), CastDirection::Up);
                (left_type, None)
            }
            (l, r, _) if l.size() < r.size() => {
                cast!(left, right_type.clone(), CastDirection::Up);
                (right_type, None)
            }
            _ => (left_type, None),
        }
    }
    fn maybe_scale_result(scale_factor: Option<usize>, ast: &mut Expr) {
        if let Some(scale_factor) = scale_factor {
            ast.kind = ExprKind::ScaleDown {
                shift_amount: log_2(scale_factor as i32),
                expr: Box::new(ast.clone()),
            };
        }
    }
    fn maybe_int_promote(&self, expr: &mut Expr, type_decl: &mut NEWTypes) {
        if !matches!(type_decl, NEWTypes::Primitive(_)) || type_decl.is_void() {
            return;
        }
        if type_decl.size() < NEWTypes::Primitive(Types::Int).size() {
            cast!(expr, NEWTypes::Primitive(Types::Int), CastDirection::Up);
            *type_decl = NEWTypes::Primitive(Types::Int);
        }
    }
    fn evaluate_unary(
        &mut self,
        token: &Token,
        right: &mut Expr,
        ast_valuekind: &mut ValueKind,
    ) -> Result<NEWTypes, Error> {
        let mut right_type = self.expr_type(right)?;

        if matches!(token.token, TokenType::Amp) {
            // array doesn't decay during '&' expression
            Ok(self.check_address(token, right_type, right, ast_valuekind)?)
        } else {
            crate::arr_decay!(right_type, right, token);
            Ok(match token.token {
                TokenType::Star => self.check_deref(token, right_type, ast_valuekind)?,
                TokenType::Bang => {
                    Self::lval_to_rval(right);
                    self.maybe_int_promote(right, &mut right_type);

                    if !right_type.is_scalar() {
                        return Err(Error::new(
                            token,
                            ErrorKind::InvalidUnary(token.token.clone(), right_type, "scalar"),
                        ));
                    }

                    NEWTypes::Primitive(Types::Int)
                }
                TokenType::Minus | TokenType::Tilde | TokenType::Plus => {
                    Self::lval_to_rval(right);
                    self.maybe_int_promote(right, &mut right_type);

                    if !right_type.is_integer() {
                        return Err(Error::new(
                            token,
                            ErrorKind::InvalidUnary(token.token.clone(), right_type, "integer"),
                        ));
                    }

                    right_type
                }
                _ => unreachable!(), // ++a or --a are evaluated as compound assignment
            })
        }
    }
    fn check_address(
        &self,
        token: &Token,
        type_decl: NEWTypes,
        expr: &mut Expr,
        ast_valuekind: &mut ValueKind,
    ) -> Result<NEWTypes, Error> {
        if expr.value_kind == ValueKind::Lvalue {
            *ast_valuekind = ValueKind::Rvalue;
            Ok(NEWTypes::Pointer(Box::new(type_decl)))
        } else {
            Err(Error::new(
                token,
                ErrorKind::Regular("Can't call '&' on r-value"),
            ))
        }
    }
    fn check_deref(
        &self,
        token: &Token,
        type_decl: NEWTypes,
        ast_valuekind: &mut ValueKind,
    ) -> Result<NEWTypes, Error> {
        if let Some(inner) = type_decl.deref_at() {
            *ast_valuekind = ValueKind::Lvalue;
            Ok(inner)
        } else {
            Err(Error::new(token, ErrorKind::InvalidDerefType(type_decl)))
        }
    }
    fn evaluate_grouping(&mut self, expr: &mut Expr) -> Result<NEWTypes, Error> {
        self.expr_type(expr)
    }
    fn check_return_compatibility(
        &mut self,
        keyword: &Token,
        function_type: &NEWTypes,
        body_return: &NEWTypes,
        return_expr: &ExprKind,
    ) -> Result<(), Error> {
        if !function_type.type_compatible(body_return, return_expr) {
            Err(Error::new(
                keyword,
                ErrorKind::MismatchedFunctionReturn(function_type.clone(), body_return.clone()),
            ))
        } else {
            Ok(())
        }
    }
}

#[derive(PartialEq, Debug)]
enum ScopeKind {
    Global,
    Loop,
    // (function name, return type, save all gotos so that can error if no matching label)
    Function(Token, NEWTypes, Vec<Token>),
    // all cases and defaults that are in a switch
    // if Some(value) then case, if None then default
    Switch(Vec<Option<i64>>),
}

// vector to go through and check if certain statements are
// enclosed by others. eg: return only in functions, break only in switch/loops
#[derive(PartialEq, Debug)]
struct ScopeLevel(Vec<ScopeKind>);
impl ScopeLevel {
    fn increment_stack_size(&mut self, type_decl: &NEWTypes) {
        let ScopeKind::Function(func_name, ..) = find_scope!(self, ScopeKind::Function(..))
            .expect("can only be called inside a function") else {unreachable!()};
        let func_symbol = func_name.token.get_symbol_entry();
        let stack_size = func_symbol.borrow().unwrap_func().stack_size;

        let mut size = stack_size + type_decl.size();
        size = align(size, type_decl);

        func_symbol.borrow_mut().unwrap_func_mut().stack_size = size;
    }
    fn insert_label(&mut self, name_token: &Token) -> Result<(), Error> {
        let name = name_token.unwrap_string();
        let ScopeKind::Function(func_name, ..) = find_scope!(self,ScopeKind::Function(..))
            .expect("ensured by parser that label is always inside function") else {unreachable!()};

        let func_symbol = func_name.token.get_symbol_entry();

        if func_symbol
            .borrow()
            .unwrap_func()
            .labels
            .contains_key(&name)
        {
            return Err(Error::new(
                name_token,
                ErrorKind::Redefinition("Label", name_token.unwrap_string()),
            ));
        }
        let len = func_symbol.borrow().unwrap_func().labels.len();
        func_symbol
            .borrow_mut()
            .unwrap_func_mut()
            .labels
            .insert(name, len);

        Ok(())
    }
    fn insert_goto(&mut self, name_token: Token) -> Result<(), Error> {
        let ScopeKind::Function(.., gotos) = find_scope!(self,ScopeKind::Function(..))
            .expect("ensured by parser that label is always inside function") else {unreachable!()};

        gotos.push(name_token);
        Ok(())
    }
    fn compare_gotos(&mut self) -> Result<(), Error> {
        let ScopeKind::Function(func_name, _,gotos) = find_scope!(self,ScopeKind::Function(..))
            .expect("ensured by parser that label is always inside function") else {unreachable!()};

        let func_symbol = func_name.token.get_symbol_entry();

        for g in gotos {
            let label = g.unwrap_string();
            if !func_symbol
                .borrow()
                .unwrap_func()
                .labels
                .contains_key(&label)
            {
                return Err(Error::new(
                    g,
                    ErrorKind::MissingLabel(label, func_name.unwrap_string()),
                ));
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
struct CurrentObjects(Vec<(i64, i64, NEWTypes)>);
impl CurrentObjects {
    fn new(type_decl: NEWTypes) -> Self {
        CurrentObjects(vec![(0, 0, type_decl)])
    }
    fn update(&mut self, (i, union_index, new_type): (i64, i64, NEWTypes)) {
        self.0.last_mut().unwrap().0 = i;
        self.0.last_mut().unwrap().1 = union_index;
        self.0.push((0, 0, new_type));
    }
    fn current(&self) -> &(i64, i64, NEWTypes) {
        self.0.last().unwrap()
    }
    fn current_type(&self) -> &NEWTypes {
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
}
fn find_same_union(
    new_list: &Vec<(CurrentObjects, Init)>,
    current: &CurrentObjects,
) -> Option<(i64, usize)> {
    for (objects, _) in new_list {
        let mut offset = 0;
        for (other_obj, current_obj) in objects.0.iter().zip(&current.0) {
            match (other_obj, current_obj) {
                ((_, i1, type_decl @ NEWTypes::Union(_)), (_, i2, NEWTypes::Union(_)))
                    if i1 != i2 =>
                {
                    return Some((offset, type_decl.size()))
                }
                ((i1, ..), (i2, ..)) if *i1 != *i2 => break,
                ((i, _, type_decl), ..) => offset += type_decl.offset(*i),
            }
        }
    }
    None
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
    token: &Token,
    left_type: &NEWTypes,
    right_type: &NEWTypes,
    right_expr: &ExprKind,
) -> bool {
    match (&left_type, &right_type) {
        (NEWTypes::Primitive(Types::Void), _) | (_, NEWTypes::Primitive(Types::Void)) => false,
        (NEWTypes::Pointer(_), NEWTypes::Pointer(_)) => {
            if left_type.type_compatible(right_type, right_expr) {
                token.token == TokenType::Minus
            } else {
                false
            }
        }
        (_, NEWTypes::Pointer(_)) => token.token == TokenType::Plus,
        (NEWTypes::Pointer(_), _) => {
            token.token == TokenType::Plus || token.token == TokenType::Minus
        }
        (NEWTypes::Struct(..), _)
        | (_, NEWTypes::Struct(..))
        | (NEWTypes::Union(..), _)
        | (_, NEWTypes::Union(..)) => false,
        _ => true,
    }
}
pub fn maybe_scale<'a, T>(
    left_type: &NEWTypes,
    right_type: &NEWTypes,
    left_expr: &'a mut T,
    right_expr: &'a mut T,
) -> Option<(&'a mut T, usize)> {
    match (left_type, right_type) {
        (t, NEWTypes::Pointer(inner)) if !t.is_ptr() && inner.size() > 1 => {
            Some((left_expr, inner.size()))
        }
        (NEWTypes::Pointer(inner), t) if !t.is_ptr() && inner.size() > 1 => {
            Some((right_expr, inner.size()))
        }
        _ => None,
    }
}

// 6.6 Constant Expressions
// returns true if expression is known at compile-time
fn is_constant(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::String(_) | ExprKind::Literal(_) => true,
        ExprKind::Cast { expr, .. }
        | ExprKind::ScaleUp { expr, .. }
        | ExprKind::Grouping { expr } => is_constant(expr),

        ExprKind::SizeofType { .. } | ExprKind::SizeofExpr { .. } => todo!(),
        _ => is_address_constant(expr, true),
    }
}
fn is_address_constant(expr: &Expr, is_outer: bool) -> bool {
    match &expr.kind {
        ExprKind::Unary { token, right, .. } if matches!(token.token, TokenType::Amp) => {
            matches!(right.kind, ExprKind::Ident(_) | ExprKind::String(_))
                || is_address_constant(right, false)
        }
        ExprKind::Unary { token, right, .. }
            if matches!(token.token, TokenType::Star) && !is_outer =>
        {
            is_address_constant(right, is_outer)
        }
        ExprKind::MemberAccess { .. } if !is_outer => true,
        ExprKind::Binary { left, token, right }
            if matches!(token.token, TokenType::Plus | TokenType::Minus) =>
        {
            match (&left, &right) {
                (expr, n) | (n, expr) if is_const_literal(n) => is_address_constant(expr, is_outer),
                _ => false,
            }
        }
        ExprKind::Cast { expr, .. }
        | ExprKind::ScaleUp { expr, .. }
        | ExprKind::Grouping { expr } => is_address_constant(expr, is_outer),
        _ => false,
    }
}
fn is_const_literal(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Cast { expr, .. } | ExprKind::ScaleUp { expr, .. } => is_const_literal(expr),
        ExprKind::Literal(_) => true,
        _ => false,
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
    use crate::compiler::scanner::Scanner;
    use crate::compiler::wrecc_parser::parser::Parser;
    use crate::preprocess;
    use std::path::Path;

    fn setup(input: &str) -> Parser {
        let pp_tokens = preprocess(Path::new(""), input.to_string()).unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        let tokens = scanner.scan_token().unwrap();

        Parser::new(tokens)
    }
    macro_rules! assert_type {
        ($input:expr,$expected_type:pat) => {
            let mut parser = setup($input);
            let mut expr = parser.expression().unwrap();

            let mut typechecker = TypeChecker::new();
            let actual = typechecker.expr_type(&mut expr).unwrap();

            assert!(
                matches!(actual, $expected_type),
                "actual: {:?}, expected: {}",
                actual,
                stringify!($expected_type),
            );
        };
    }

    macro_rules! assert_type_err {
        ($input:expr,$expected_err:pat) => {
            let mut parser = setup($input);
            let mut expr = parser.expression().unwrap();

            let mut typechecker = TypeChecker::new();
            let actual = typechecker.expr_type(&mut expr).unwrap_err();

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
            let mut expr = parser.expression().unwrap();

            let mut typechecker = TypeChecker::new();
            for (name, type_decl) in $symbols {
                typechecker
                    .env
                    .declare_symbol(
                        &Token::default(TokenType::new_ident(name.to_string())),
                        Symbols::Variable(SymbolInfo {
                            type_decl,
                            kind: InitType::Declaration,
                            reg: None,
                            is_global: false,
                            token: Token::default(TokenType::Semicolon),
                        }),
                    )
                    .unwrap();
            }

            let value_type = typechecker.expr_type(&mut expr).unwrap();

            // have to do manual array decay because is constant expects array to be decayed already
            if let NEWTypes::Array { .. } = value_type {
                expr.kind = ExprKind::Unary {
                    token: Token::default(TokenType::Amp),
                    right: Box::new(expr.clone()),
                };
            }

            let actual = is_constant(&expr);

            assert_eq!(actual, $expected);
        };
    }
    fn setup_init_list(input: &str) -> Result<InitKind, Error> {
        // TODO: maybe be can parser.parse() so that external declaration doesnt have to be public
        let ExternalDeclaration::Declaration(decls) =
                setup(input).external_declaration().unwrap() else {unreachable!("only passing type")};

        let Declaration { specifiers, declarators, is_typedef } = decls;
        let mut typechecker = TypeChecker::new();

        let mut decl = declarators[0].clone();
        let specifier_type = typechecker.parse_specifiers(specifiers).unwrap();
        typechecker.declarator(specifier_type, is_typedef, &mut decl)?;

        Ok(decl.1.unwrap().kind)
    }
    fn assert_init(actual: InitKind, expected: Vec<(usize, &'static str)>) {
        let InitKind::Aggr(actual) = actual else {unreachable!()};

        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert_eq!(actual.offset, expected.0 as i64);

            let expr = setup(expected.1).expression().unwrap();
            let InitKind::Scalar(actual_expr) = actual.kind else {unreachable!()};
            assert_eq!(actual_expr.to_string(), expr.to_string());
        }
    }

    #[test]
    fn binary_integer_promotion() {
        assert_type!("'1' + '2'", NEWTypes::Primitive(Types::Int));
    }

    #[test]
    fn shift_type() {
        assert_type!("1 << (long)2", NEWTypes::Primitive(Types::Int));
        assert_type!("(long)1 << (char)2", NEWTypes::Primitive(Types::Long));
        assert_type!("'1' << (char)2", NEWTypes::Primitive(Types::Int));
    }

    #[test]
    fn comp_type() {
        assert_type!("1 == (long)2", NEWTypes::Primitive(Types::Int));
        assert_type!("(char*)1 == (char*)2", NEWTypes::Primitive(Types::Int));
        assert_type!("1 <= (long)2", NEWTypes::Primitive(Types::Int));
        assert_type!("(char*)1 > (char*)2", NEWTypes::Primitive(Types::Int));
        assert_type!("(void*)1 == (long*)2", NEWTypes::Primitive(Types::Int));

        assert_type_err!("1 == (long*)2", ErrorKind::InvalidComp(..));
        assert_type_err!("(int*)1 == (long*)2", ErrorKind::InvalidComp(..));
    }

    #[test]
    fn static_constant_test() {
        assert_const_expr!(
            "&a + (int)(3 * 1)",
            true,
            vec![("a", NEWTypes::Primitive(Types::Int))]
        );

        assert_const_expr!(
            "a + (int)(3 * 1)",
            false,
            vec![(
                "a",
                NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Int)))
            )]
        );
        assert_const_expr!(
            "\"hi\" + (int)(3 * 1)",
            true,
            Vec::<(&str, NEWTypes)>::new()
        );
        assert_const_expr!(
            "&\"hi\" + (int)(3 * 1)",
            true,
            Vec::<(&str, NEWTypes)>::new()
        );

        assert_const_expr!(
            "(long*)&a",
            true,
            vec![("a", NEWTypes::Primitive(Types::Int))]
        );

        assert_const_expr!("(long*)1 + 3", true, Vec::<(&str, NEWTypes)>::new());

        assert_const_expr!(
            "&a[3]",
            true,
            vec![(
                "a",
                NEWTypes::Array {
                    amount: 4,
                    of: Box::new(NEWTypes::Primitive(Types::Int)),
                },
            )]
        );

        assert_const_expr!(
            "*&a[3]",
            false,
            vec![(
                "a",
                NEWTypes::Array {
                    amount: 4,
                    of: Box::new(NEWTypes::Primitive(Types::Int)),
                },
            )]
        );

        assert_const_expr!(
            "&a.age",
            true,
            vec![(
                "a",
                NEWTypes::Struct(StructInfo::Anonymous(
                    Token::default(TokenType::Comma),
                    vec![(
                        NEWTypes::default(),
                        Token::default(TokenType::new_ident("age".to_string())),
                    )]
                ))
            )]
        );

        assert_const_expr!(
            "a.age",
            false,
            vec![(
                "a",
                NEWTypes::Struct(StructInfo::Anonymous(
                    Token::default(TokenType::Comma),
                    vec![(
                        NEWTypes::default(),
                        Token::default(TokenType::new_ident("age".to_string())),
                    )]
                ))
            )]
        );
        assert_const_expr!(
            "*a",
            false,
            vec![(
                "a",
                NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Int)))
            )]
        );

        assert_const_expr!(
            "(int *)*a",
            false,
            vec![(
                "a",
                NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Int)))
            )]
        );

        assert_const_expr!(
            "*a",
            true,
            vec![(
                "a",
                NEWTypes::Array {
                    amount: 4,
                    of: Box::new(NEWTypes::Array {
                        amount: 4,
                        of: Box::new(NEWTypes::Primitive(Types::Int))
                    },),
                },
            )]
        );
        assert_const_expr!(
            "*&a[3]",
            true,
            vec![(
                "a",
                NEWTypes::Array {
                    amount: 4,
                    of: Box::new(NEWTypes::Array {
                        amount: 4,
                        of: Box::new(NEWTypes::Primitive(Types::Int))
                    },),
                },
            )]
        );

        assert_const_expr!(
            "&a->age",
            true,
            vec![(
                "a",
                NEWTypes::Array {
                    amount: 4,
                    of: Box::new(NEWTypes::Struct(StructInfo::Anonymous(
                        Token::default(TokenType::Comma),
                        vec![(
                            NEWTypes::default(),
                            Token::default(TokenType::new_ident("age".to_string())),
                        )]
                    ))),
                },
            )]
        );

        assert_const_expr!("a", false, vec![("a", NEWTypes::Primitive(Types::Int))]);
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
        let mut scopes = ScopeLevel(vec![
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
        let mut scopes = ScopeLevel(vec![ScopeKind::Global, ScopeKind::Loop, ScopeKind::Loop]);
        let expected = false;
        let actual = find_scope!(scopes, ScopeKind::Switch(..)).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn finds_and_mutates_scope() {
        let mut scopes = ScopeLevel(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![]),
            ScopeKind::Switch(vec![]),
            ScopeKind::Loop,
        ]);
        let expected = ScopeLevel(vec![
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

        assert_eq!(scopes, expected);
    }

    #[test]
    fn array_init_list() {
        let actual = setup_init_list("int a[3] = {1,2};").unwrap();
        let expected = vec![(0, "1"), (4, "2")];

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
        let expected = vec![(0, "1"), (4, "2")];

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
                kind: ErrorKind::InitializerOverflow(NEWTypes::Union(_)),
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
            (0, "'h'"),
            (1, "'e'"),
            (2, "'i'"),
            (3, "'\\0'"),
            (4, "'\\0'"),
        ];

        assert_init(actual, expected);
    }

    #[test]
    fn multidimensional_array() {
        let actual = setup_init_list("int a[2][3] = {{1},1,2};").unwrap();
        let expected = vec![(0, "1"), (12, "1"), (16, "2")];

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
            (0, "1"),
            (4, "(long)2"),
            (28, "21"),
            (40, "(long)3"),
            (48, "(long)4"),
            (56, "1"),
            (64, "2"),
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
            (0, "(char)2"),
            (1, "'m'"),
            (2, "'e'"),
            (3, "'\\0'"),
            (4, "2"),
            (8, "4"),
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
        let expected = vec![(2, "'1'"), (3, "'3'")];

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
        let expected = vec![(2, "(char)1"), (3, "(char)5")];

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
        let expected = vec![(3, "(char)8")];

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
        let expected = vec![(0, "3"), (4, "2")];

        assert_init(actual, expected);
    }
}
