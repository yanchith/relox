use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::rc::Rc;

use crate::ast;
use crate::callable::{FunctionCallable, NativeCallableClock};
use crate::env::{AssignError, Env};
use crate::reporter::Reporter;
use crate::value::{CallableValue, ClassValue, InstanceValue, Value};

// FIXME(yanchith): add Token/Span info
// FIXME(yanchith): implement std::error:Error
#[derive(Debug)]
pub enum InterpretError {
    Return(Value),
    TypeError,
    ValueNotCallable(Value),
    WrongNumberOfArgsToCallable(usize, usize), // FIXME(yanchith): add callable ident
    UndeclaredVariableUse,                     // FIXME(yanchith): add variable name
    UndeclaredVariableAssign(String),
    AccessOnNoninstanceValue, // FIXME(yanchith): add more info
    UndefinedPropertyUse(String, String),
    SuperclassNotAClass(String),
}

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InterpretError::Return(value) => write!(f, "Return statement with value {}", value),
            InterpretError::TypeError => write!(f, "Type Error"),
            InterpretError::ValueNotCallable(value) => {
                write!(f, "Type Error: value not callable {}", value)
            }
            InterpretError::WrongNumberOfArgsToCallable(provided, required) => write!(
                f,
                "Wrong number of args passed to callable (provided {}, required {})",
                provided, required,
            ),
            InterpretError::UndeclaredVariableUse => write!(f, "Use of undeclared variable"),
            InterpretError::UndeclaredVariableAssign(ident) => {
                write!(f, "Assign to undeclared variable {}", ident)
            }
            InterpretError::AccessOnNoninstanceValue => {
                write!(f, "Access expression applied on noninstance value")
            }
            InterpretError::UndefinedPropertyUse(class, field) => {
                write!(f, "Class {} does not have a field {}", class, field)
            }
            InterpretError::SuperclassNotAClass(ident) => write!(
                f,
                "Classes can only inherit from other classes. {} is not a class",
                ident,
            ),
        }
    }
}

pub type InterpretResult<T> = Result<T, InterpretError>;

#[derive(Debug)]
pub struct Interpreter {
    env: Rc<RefCell<Env>>,
    globals: Rc<RefCell<Env>>,
    locals: HashMap<u64, u64>,
}

impl Interpreter {
    pub fn new() -> Self {
        let mut globals = Env::new();
        globals.define(
            "clock".to_string(),
            Value::Callable(CallableValue::new(Box::new(NativeCallableClock))),
        );

        let globals_ptr = Rc::new(RefCell::new(globals));

        Self {
            env: Rc::clone(&globals_ptr),
            globals: globals_ptr,
            locals: HashMap::new(),
        }
    }

    pub fn resolve(&mut self, ast_id: u64, distance: u64) {
        self.locals.insert(ast_id, distance);
    }

    pub fn interpret(&mut self, reporter: &mut Reporter, prog: &ast::Prog) {
        match prog {
            ast::Prog::Stmts(stmts) => {
                for stmt in stmts {
                    match self.eval_stmt(stmt) {
                        Err(err) => {
                            reporter.report_runtime_error(err.to_string());
                            break;
                        }
                        _ => (),
                    }
                }
            }
            ast::Prog::Expr(expr) => match self.eval_expr(expr) {
                Ok(value) => {
                    println!("{}", value);
                }
                Err(err) => {
                    reporter.report_runtime_error(err.to_string());
                }
            },
        }

        if reporter.has_runtime_error() {
            reporter.print_all_errors();
        }
    }

    pub fn interpret_stmts(&mut self, stmts: &[ast::Stmt]) -> InterpretResult<()> {
        for stmt in stmts {
            self.eval_stmt(stmt)?;
        }

        Ok(())
    }

    pub fn replace_env(&mut self, new_env: Rc<RefCell<Env>>) -> Rc<RefCell<Env>> {
        mem::replace(&mut self.env, new_env)
    }

    pub fn set_env(&mut self, new_env: Rc<RefCell<Env>>) {
        self.env = new_env;
    }

    fn eval_stmt(&mut self, stmt: &ast::Stmt) -> InterpretResult<()> {
        match stmt {
            ast::Stmt::VarDecl(var_decl) => self.eval_var_decl_stmt(var_decl),
            ast::Stmt::FunDecl(fun_decl) => self.eval_fun_decl_stmt(fun_decl),
            ast::Stmt::ClassDecl(class_decl) => self.eval_class_decl_stmt(class_decl),
            ast::Stmt::Expr(expr) => {
                self.eval_expr(expr.expr())?;
                Ok(())
            }
            ast::Stmt::If(if_) => self.eval_if_stmt(if_),
            ast::Stmt::While(while_) => self.eval_while_stmt(while_),
            ast::Stmt::Print(print) => self.eval_print_stmt(print),
            ast::Stmt::Return(return_) => self.eval_return_stmt(return_),
            ast::Stmt::Block(block) => self.eval_block_stmt(block),
        }
    }

    fn eval_var_decl_stmt(&mut self, var_decl: &ast::VarDeclStmt) -> InterpretResult<()> {
        let value = match var_decl.initializer() {
            Some(expr) => self.eval_expr(expr)?,
            None => Value::Nil,
        };

        self.env
            .borrow_mut()
            .define(var_decl.ident().to_string(), value);

        Ok(())
    }

    fn eval_fun_decl_stmt(&mut self, fun_decl: &ast::FunDeclStmt) -> InterpretResult<()> {
        let function = FunctionCallable::new(fun_decl.clone(), Rc::clone(&self.env), false);
        let value = Value::Callable(CallableValue::new(Box::new(function)));

        self.env
            .borrow_mut()
            .define(fun_decl.ident().to_string(), value);

        Ok(())
    }

    fn eval_class_decl_stmt(&mut self, class_decl: &ast::ClassDeclStmt) -> InterpretResult<()> {
        let superclass = if let Some(superclass_expr) = class_decl.superclass() {
            let superclass = self.eval_var_expr(superclass_expr)?;
            match superclass {
                Value::Class(class) => Some(class),
                _ => {
                    let ident = superclass_expr.ident().to_string();
                    return Err(InterpretError::SuperclassNotAClass(ident));
                }
            }
        } else {
            None
        };

        self.env
            .borrow_mut()
            .define(class_decl.ident().to_string(), Value::Nil);

        // Similar to what happens with `this`, but the environment
        // for `super` can be created just once, when we declare the
        // class.
        let method_environment = if let Some(ref superclass) = superclass {
            let mut env = Env::with_parent(Rc::clone(&self.env));
            env.define("super".to_string(), Value::Class(Rc::clone(superclass)));
            Rc::new(RefCell::new(env))
        } else {
            // FIXME(yanchith): this clone is redundant
            Rc::clone(&self.env)
        };

        let mut methods = HashMap::with_capacity(class_decl.methods().len());
        for method in class_decl.methods() {
            let function = FunctionCallable::new(
                method.clone(),
                Rc::clone(&method_environment),
                method.ident() == "init",
            );
            methods.insert(method.ident().to_string(), function);
        }

        let class = ClassValue::new(class_decl.ident().to_string(), superclass, methods);
        let value = Value::Class(Rc::new(class));

        self.env
            .borrow_mut()
            .assign_here(class_decl.ident(), value)
            .expect("Class must have been declared prior to assig");

        Ok(())
    }

    fn eval_if_stmt(&mut self, if_: &ast::IfStmt) -> InterpretResult<()> {
        let cond = self.eval_expr(if_.cond())?;
        if cond.is_truthy() {
            self.eval_stmt(if_.then())?;
        } else if let Some(else_) = if_.else_() {
            self.eval_stmt(else_)?;
        }

        Ok(())
    }

    fn eval_while_stmt(&mut self, while_: &ast::WhileStmt) -> InterpretResult<()> {
        while self.eval_expr(while_.cond())?.is_truthy() {
            self.eval_stmt(while_.loop_())?;
        }

        Ok(())
    }

    fn eval_print_stmt(&mut self, print: &ast::PrintStmt) -> InterpretResult<()> {
        let value = self.eval_expr(print.expr())?;
        println!("{}", value);

        Ok(())
    }

    fn eval_return_stmt(&mut self, return_: &ast::ReturnStmt) -> InterpretResult<()> {
        let value = match return_.expr() {
            Some(expr) => self.eval_expr(expr)?,
            None => Value::Nil,
        };
        Err(InterpretError::Return(value))
    }

    fn eval_block_stmt(&mut self, block: &ast::BlockStmt) -> InterpretResult<()> {
        let new_env = Env::with_parent(Rc::clone(&self.env));
        let old_env = mem::replace(&mut self.env, Rc::new(RefCell::new(new_env)));

        let res = self.interpret_stmts(block.stmts());

        self.env = old_env;

        res
    }

    fn eval_expr(&mut self, expr: &ast::Expr) -> InterpretResult<Value> {
        match expr {
            ast::Expr::Lit(lit) => self.eval_lit_expr(lit),
            ast::Expr::Group(group) => self.eval_group_expr(group),
            ast::Expr::Unary(unary) => self.eval_unary_expr(unary),
            ast::Expr::Binary(binary) => self.eval_binary_expr(binary),
            ast::Expr::Logic(logic) => self.eval_logic_expr(logic),
            ast::Expr::Var(var) => self.eval_var_expr(var),
            ast::Expr::Assign(assign) => self.eval_assign_expr(assign),
            ast::Expr::Call(call) => self.eval_call_expr(call),
            ast::Expr::Get(get) => self.eval_get_expr(get),
            ast::Expr::Set(set) => self.eval_set_expr(set),
            ast::Expr::This(this) => self.eval_this_expr(this),
            ast::Expr::Super(super_) => self.eval_super_expr(super_),
        }
    }

    fn eval_lit_expr(&self, lit: &ast::LitExpr) -> InterpretResult<Value> {
        let value = match lit {
            ast::LitExpr::Number(number) => Value::Number(*number),
            // We clone the string from the AST, as we may be
            // instantiating it multiple times and we don't want the
            // instances to share storage (even though we currently
            // don't support mutation on strings).
            // FIXME(yanchith): optimize this... if we decide never to mutate
            // strings, we can put the string in the token/ast in an
            // Rc as well, otherwise we can maybe clone on write (Cow)
            // instead?
            ast::LitExpr::String(string) => Value::String(Rc::new(string.clone())),
            ast::LitExpr::Boolean(boolean) => Value::Boolean(*boolean),
            ast::LitExpr::Nil => Value::Nil,
        };

        Ok(value)
    }

    fn eval_group_expr(&mut self, group: &ast::GroupExpr) -> InterpretResult<Value> {
        self.eval_expr(group.expr())
    }

    fn eval_unary_expr(&mut self, unary: &ast::UnaryExpr) -> InterpretResult<Value> {
        let value = self.eval_expr(unary.expr())?;
        match unary.op() {
            ast::UnaryOp::Minus => match &value {
                Value::Number(number) => Ok(Value::Number(-number)),
                _ => Err(InterpretError::TypeError),
            },
            ast::UnaryOp::Not => Ok(Value::Boolean(!value.is_truthy())),
        }
    }

    fn eval_binary_expr(&mut self, binary: &ast::BinaryExpr) -> InterpretResult<Value> {
        let left_value = self.eval_expr(binary.left())?;
        let right_value = self.eval_expr(binary.right())?;

        match binary.op() {
            ast::BinaryOp::Plus => match (left_value, right_value) {
                (Value::String(left), Value::String(right)) => {
                    let mut result: String = String::with_capacity(left.len() + right.len());
                    result.push_str(&left);
                    result.push_str(&right);
                    Ok(Value::String(Rc::new(result)))
                }
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left + right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::Minus => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left - right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::Multiply => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left * right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::Divide => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left / right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::Greater => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left > right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::GreaterEqual => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left >= right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::Less => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left < right)),
                _ => Err(InterpretError::TypeError),
            },
            ast::BinaryOp::LessEqual => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left <= right)),
                _ => Err(InterpretError::TypeError),
            },
            // Note: officially in Lox, NaN == NaN, but our
            // implementation uses Rust and IEEE 754 semantics, where
            // NaN != NaN
            ast::BinaryOp::Equal => Ok(Value::Boolean(left_value == right_value)),
            ast::BinaryOp::NotEqual => Ok(Value::Boolean(left_value != right_value)),
        }
    }

    fn eval_logic_expr(&mut self, logic: &ast::LogicExpr) -> InterpretResult<Value> {
        let left_value = self.eval_expr(logic.left())?;

        match logic.op() {
            ast::LogicOp::And => {
                if left_value.is_truthy() {
                    Ok(self.eval_expr(logic.right())?)
                } else {
                    Ok(left_value)
                }
            }
            ast::LogicOp::Or => {
                if left_value.is_truthy() {
                    Ok(left_value)
                } else {
                    Ok(self.eval_expr(logic.right())?)
                }
            }
        }
    }

    fn eval_var_expr(&self, var: &ast::VarExpr) -> InterpretResult<Value> {
        if let Some(distance) = self.locals.get(&var.ast_id()) {
            Ok(self.env.borrow().get_at_distance(var.ident(), *distance))
        } else {
            self.globals
                .borrow()
                .get_here(var.ident())
                .ok_or(InterpretError::UndeclaredVariableUse)
        }
    }

    fn eval_assign_expr(&mut self, assign: &ast::AssignExpr) -> InterpretResult<Value> {
        let lvalue = assign.ident();
        let rvalue = self.eval_expr(assign.expr())?;

        if let Some(distance) = self.locals.get(&assign.ast_id()) {
            self.env
                .borrow_mut()
                .assign_at_distance(lvalue, *distance, rvalue.clone());
            Ok(rvalue)
        } else {
            match self
                .globals
                .borrow_mut()
                .assign_here(lvalue, rvalue.clone())
            {
                Ok(()) => Ok(rvalue),
                Err(AssignError::ValueNotDeclared) => {
                    let ident = lvalue.to_string();
                    Err(InterpretError::UndeclaredVariableAssign(ident))
                }
            }
        }
    }

    fn eval_call_expr(&mut self, call: &ast::CallExpr) -> InterpretResult<Value> {
        let callee = self.eval_expr(call.callee())?;

        match callee {
            Value::Callable(callable) => {
                let provided_args_len = call.args().len();
                let required_args_len = callable.arity();
                if provided_args_len != required_args_len {
                    Err(InterpretError::WrongNumberOfArgsToCallable(
                        provided_args_len,
                        required_args_len,
                    ))
                } else {
                    let mut args = Vec::with_capacity(call.args().len());

                    for arg_expr in call.args() {
                        let arg = self.eval_expr(arg_expr)?;
                        args.push(arg);
                    }

                    callable.call(self, &args)
                }
            }
            Value::Class(class) => {
                let provided_args_len = call.args().len();
                let required_args_len = class.init_arity();
                if provided_args_len != required_args_len {
                    Err(InterpretError::WrongNumberOfArgsToCallable(
                        provided_args_len,
                        required_args_len,
                    ))
                } else {
                    let mut args = Vec::with_capacity(call.args().len() + 1);

                    for arg_expr in call.args() {
                        let arg = self.eval_expr(arg_expr)?;
                        args.push(arg);
                    }

                    ClassValue::init_call(Rc::clone(&class), self, &args)
                }
            }
            _ => Err(InterpretError::ValueNotCallable(callee)),
        }
    }

    fn eval_get_expr(&mut self, get: &ast::GetExpr) -> InterpretResult<Value> {
        let object = self.eval_expr(get.object())?;

        match object {
            Value::Instance(instance) => InstanceValue::get(instance.clone(), get.field())
                .ok_or_else(|| {
                    InterpretError::UndefinedPropertyUse(
                        instance.borrow().class().ident().to_string(),
                        get.field().to_string(),
                    )
                }),
            _ => Err(InterpretError::AccessOnNoninstanceValue),
        }
    }

    fn eval_set_expr(&mut self, set: &ast::SetExpr) -> InterpretResult<Value> {
        let object = self.eval_expr(set.object())?;

        match object {
            Value::Instance(instance) => {
                // FIXME(yanchith): what do other languages do? This
                // is underspecified - we don't try to evaluate the
                // value before we have a place to shove it to, but
                // users might be expecting us to.
                let value = self.eval_expr(set.value())?;
                let mut instance_mut = instance.borrow_mut();
                instance_mut.set(set.field().to_string(), value.clone());

                Ok(value)
            }
            _ => Err(InterpretError::AccessOnNoninstanceValue),
        }
    }

    fn eval_this_expr(&mut self, this: &ast::ThisExpr) -> InterpretResult<Value> {
        let distance = self
            .locals
            .get(&this.ast_id())
            .expect("'this' must always be resolved");
        Ok(self.env.borrow().get_at_distance("this", *distance))
    }

    fn eval_super_expr(&mut self, super_: &ast::SuperExpr) -> InterpretResult<Value> {
        let distance = *self
            .locals
            .get(&super_.ast_id())
            .expect("'super' must always be resolved");

        let env = self.env.borrow();
        let superclass = env.get_at_distance("super", distance);

        // This counts on the scope containing 'this' (the instance)
        // to be one closer than the scope containing 'super'
        let this = if let Value::Instance(instance) = env.get_at_distance("this", distance - 1) {
            instance
        } else {
            panic!("Assertion failed: 'this' must an instance");
        };

        match superclass {
            Value::Class(class) => match class.find_method(super_.method()) {
                Some(method) => {
                    let bound_method = method.bind(this);
                    Ok(Value::Callable(CallableValue::new(Box::new(bound_method))))
                }
                None => Err(InterpretError::UndefinedPropertyUse(
                    class.ident().to_string(),
                    super_.method().to_string(),
                )),
            },
            _ => panic!("Assertion failed: Only classes can be superclasses"),
        }
    }
}
