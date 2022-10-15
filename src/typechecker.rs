use crate::environment::Environment;
use crate::environment::Function;
use crate::error::Error;
use crate::interpreter::Stmt;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;
use crate::types::Types;

#[derive(PartialEq)]
enum Scope {
    Global,
    Block,
    Function(Types), // function return type
}
pub struct TypeChecker {
    errors: Vec<Error>,
    scope: Vec<Scope>,
    env: Environment<Types>,
    global_env: Environment<Types>,
    returns_all_paths: bool,
    builtins: Vec<(&'static str, Function)>,
    found_main: bool,
}
impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            errors: vec![],
            env: Environment::new(None),
            global_env: Environment::new(None),
            scope: vec![Scope::Global],
            returns_all_paths: false,
            found_main: false,
            builtins: vec![(
                "printint",
                Function::new(
                    Types::Void,
                    vec![(
                        Types::Char,
                        Token::new(TokenType::Ident("".to_string()), -1, -1, "".to_string()),
                    )],
                    vec![],
                ),
            )],
        }
    }
    pub fn check(&mut self, statements: &Vec<Stmt>) -> Result<(), Vec<Error>> {
        // initialze builtins so typechecker doesnt throw error when it doesnt find them in the program
        for (name, f) in self.builtins.iter().by_ref() {
            self.global_env
                .current
                .funcs
                .insert(name.to_string(), f.clone());
        }
        if let Err(e) = self.check_statements(statements) {
            self.errors.push(e);
            // synchronize
        }
        if !self.errors.is_empty() {
            Err(self.errors.clone())
        } else if !self.found_main {
            Err(vec![Error::missing_entrypoint()])
        } else {
            Ok(())
        }
    }
    fn check_statements(&mut self, statements: &Vec<Stmt>) -> Result<(), Error> {
        for s in statements {
            self.visit(s)?
        }
        Ok(())
    }
    fn visit(&mut self, statement: &Stmt) -> Result<(), Error> {
        match statement {
            Stmt::DeclareVar(type_decl, var_name) => self.declare_var(type_decl, var_name),
            Stmt::InitVar(type_decl, name, expr) => self.init_var(type_decl, name, expr),
            Stmt::Function(return_type, name, params, body) => {
                self.function_definition(*return_type, name, params.clone(), body.clone())
            }
            Stmt::Return(keyword, value) => self.return_statement(keyword, value),
            Stmt::Print(token, expr) => self.print_statement(token, expr),
            Stmt::Expr(expr) => match self.expr_type(expr) {
                Ok(_) => Ok(()),
                Err(e) => Err(e),
            },
            Stmt::Block(statements) => self.block(
                statements,
                Environment::new(Some(Box::new(self.env.clone()))),
                None,
            ),
            Stmt::If(keyword, cond, then_branch, else_branch) => {
                self.if_statement(keyword, cond, then_branch, else_branch)
            }
            Stmt::While(cond, body) => self.while_statement(cond, body),
        }
    }
    fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), Error> {
        self.expr_type(cond)?;
        self.visit(body)?;
        self.returns_all_paths = false;
        Ok(())
    }
    fn declare_var(&mut self, type_decl: &Types, var_name: &Token) -> Result<(), Error> {
        let name = var_name.unwrap_string();

        if self.env.current.vars.contains_key(&name) {
            return Err(Error::new(
                var_name,
                &format!("Redefinition of variable '{}'", var_name.unwrap_string()),
            ));
        }
        if *type_decl == Types::Void {
            return Err(Error::new(
                var_name,
                &format!("Can't assign to 'void' {}", var_name.unwrap_string()),
            ));
        }
        self.env.declare_var(*type_decl, name);
        Ok(())
    }
    fn init_var(&mut self, type_decl: &Types, var_name: &Token, expr: &Expr) -> Result<(), Error> {
        let name = var_name.unwrap_string();
        let value = self.expr_type(expr)?;

        if self.env.current.vars.contains_key(&name) {
            Err(Error::new(
                var_name,
                &format!("Redefinition of variable '{}'", name),
            ))
        } else if *type_decl == Types::Void {
            Err(Error::new(
                var_name,
                &format!("Can't assign to 'void' {}", name),
            ))
        } else if value == Types::Void {
            Err(Error::new(
                var_name,
                &format!(
                    "'void' cant be assigned to variable {} of type {}",
                    name, type_decl
                ),
            ))
        } else {
            // currently only type-checks for void since int and char are interchangeable
            self.env.init_var(name, *type_decl);
            Ok(())
        }
    }
    fn if_statement(
        &mut self,
        keyword: &Token,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Stmt>,
    ) -> Result<(), Error> {
        let cond = self.expr_type(cond)?;
        if cond == Types::Void {
            return Err(Error::new(
                keyword,
                "expected Expression inside of condition, found 'void'",
            ));
        }
        self.visit(then_branch)?;
        let then_return = self.returns_all_paths;
        self.returns_all_paths = false;

        if let Some(else_branch) = else_branch {
            self.visit(else_branch)?;
            let else_return = self.returns_all_paths;

            if !then_return || !else_return {
                self.returns_all_paths = false;
            }
        }
        Ok(())
    }
    fn print_statement(&mut self, token: &Token, expr: &Expr) -> Result<(), Error> {
        let t = self.expr_type(expr)?;
        if t == Types::Void {
            Err(Error::new(token, "can't print 'void' expression"))
        } else {
            Ok(())
        }
    }
    fn function_definition(
        &mut self,
        return_type: Types,
        name: &Token,
        params: Vec<(Types, Token)>,
        body: Vec<Stmt>,
    ) -> Result<(), Error> {
        if *self.scope.last().unwrap() != Scope::Global {
            return Err(Error::new(
                name,
                "can only define functions in global scope",
            ));
        }
        if name.unwrap_string() == "main" {
            self.found_main = true;
        }

        self.global_env.current.funcs.insert(
            name.unwrap_string(),
            Function::new(return_type, params.clone(), body.clone()),
        );

        let mut env = Environment::new(Some(Box::new(self.env.clone())));

        for (type_decl, name) in params.iter() {
            env.init_var(name.unwrap_string(), *type_decl)
        }

        self.block(&body, env, Some(return_type))?;

        if return_type != Types::Void && !self.returns_all_paths {
            self.returns_all_paths = false;
            Err(Error::new(
                name,
                "non-void function doesnt return in all code paths",
            ))
        } else {
            self.returns_all_paths = false;
            Ok(())
        }
    }
    fn return_statement(&mut self, keyword: &Token, expr: &Option<Expr>) -> Result<(), Error> {
        self.returns_all_paths = true;
        if let Some(expr) = expr {
            let type_decl = self.expr_type(expr)?;
            self.check_return(keyword, type_decl)
        } else {
            self.check_return(keyword, Types::Void)
        }
    }

    pub fn expr_type(&mut self, ast: &Expr) -> Result<Types, Error> {
        match ast {
            Expr::Binary { left, token, right } => self.evaluate_binary(left, token, right),
            Expr::Unary { token: _, right } => self.evaluate_unary(right),
            Expr::Grouping { expr } => self.evaluate_grouping(expr),
            Expr::Number(_) => Ok(Types::Int),
            Expr::CharLit(_) => Ok(Types::Char),
            Expr::Logical { left, token, right } => self.evaluate_logical(left, token, right),
            Expr::Ident(v) => self.env.get_var(v),
            Expr::Assign { name, expr } => {
                let value = self.expr_type(expr)?;
                self.env.assign_var(name, value)
            }
            Expr::Call {
                left_paren,
                callee,
                args,
            } => self.evaluate_call(left_paren, callee, args),
        }
    }

    fn evaluate_call(
        &mut self,
        left_paren: &Token,
        callee: &Expr,
        args: &Vec<Expr>,
    ) -> Result<Types, Error> {
        let func_name = match callee {
            Expr::Ident(func_name) => func_name,
            _ => return Err(Error::new(left_paren, "function-name has to be identifier")),
        };

        let arg_types = args
            .iter()
            .map(|expr| self.expr_type(expr))
            .collect::<Result<Vec<Types>, Error>>()?;

        // TODO: use get_func instead
        match self
            .global_env
            .current
            .funcs
            .get(&func_name.unwrap_string())
        {
            Some(function) => {
                if function.arity() == args.len() {
                    Self::args_and_params_match(left_paren, &function.params, arg_types)?;
                    Ok(function.return_type)
                } else {
                    Err(Error::new(
                        left_paren,
                        &format!(
                            "at '{}': expected {} argument(s) found {}",
                            func_name.unwrap_string(),
                            function.arity(),
                            args.len()
                        ),
                    ))
                }
            }
            None => Err(Error::new(
                left_paren,
                &format!("no function {} exists", func_name.unwrap_string()),
            )),
        }
    }
    fn args_and_params_match(
        left_paren: &Token,
        params: &Vec<(Types, Token)>,
        args: Vec<Types>,
    ) -> Result<(), Error> {
        // TODO: actually compare args not only testing for void
        for (i, arg_type) in args.iter().enumerate() {
            if *arg_type == Types::Void {
                return Err(Error::new(
                    left_paren,
                    &format!(
                        "expected argument to be of type {} found {}",
                        params[i].0, arg_type
                    ),
                ));
            }
        }
        Ok(())
    }
    fn block(
        &mut self,
        body: &Vec<Stmt>,
        env: Environment<Types>,
        return_type: Option<Types>,
    ) -> Result<(), Error> {
        self.env = env;
        if let Some(return_type) = return_type {
            self.scope.push(Scope::Function(return_type));
        } else {
            self.scope.push(Scope::Block);
        }
        let result = self.check_statements(body);

        self.env = *self.env.enclosing.as_ref().unwrap().clone();
        self.scope.pop();

        result
    }
    fn evaluate_logical(
        &mut self,
        left: &Expr,
        token: &Token,
        right: &Expr,
    ) -> Result<Types, Error> {
        self.evaluate_binary(left, token, right)
    }
    fn evaluate_binary(
        &mut self,
        left: &Expr,
        token: &Token,
        right: &Expr,
    ) -> Result<Types, Error> {
        let mut left = self.expr_type(left)?;
        let mut right = self.expr_type(right)?;

        if left == Types::Void || right == Types::Void {
            return Err(Error::new(
                token,
                &format!(
                    "invalid binary expression: {} {} {}",
                    left, token.token, right
                ),
            ));
        }

        left = self.maybe_int_promote(left);
        right = self.maybe_int_promote(right);

        Ok(if left > right { left } else { right }) // implicit type conversion
    }
    fn maybe_int_promote(&self, type_decl: Types) -> Types {
        if type_decl < Types::Int {
            Types::Int
        } else {
            type_decl
        }
    }
    fn evaluate_unary(&mut self, right: &Expr) -> Result<Types, Error> {
        self.expr_type(right)
    }
    fn evaluate_grouping(&mut self, expr: &Expr) -> Result<Types, Error> {
        self.expr_type(expr)
    }
    fn check_return(&mut self, keyword: &Token, body_return: Types) -> Result<(), Error> {
        match self.find_function() {
            Some(Scope::Function(function_type)) => {
                if *function_type == Types::Void && body_return != Types::Void {
                    return Err(Error::new(
                        keyword,
                        &format!(
                            "function return expects type:'void', found: {}",
                            body_return
                        ),
                    ));
                } else if *function_type != Types::Void && body_return == Types::Void {
                    return Err(Error::new(
                        keyword,
                        &format!(
                            "function return expects type:{}, found: 'void'",
                            function_type
                        ),
                    ));
                }
            }
            _ => {
                return Err(Error::new(
                    keyword,
                    "can only define return statements inside a function",
                ));
            }
        };
        Ok(())
    }
    fn find_function(&self) -> Option<&Scope> {
        for ref scope in self.scope.iter().rev() {
            if matches!(scope, Scope::Function(_)) {
                return Some(scope);
            }
        }
        None
    }
}
