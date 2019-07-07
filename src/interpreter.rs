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

    pub fn interpret(&mut self, reporter: &mut Reporter, program: &ast::Program) {
        for stmt in program.stmts() {
            match self.eval_stmt(stmt) {
                Ok(Value::Nil) => (),
                Ok(value) => println!("{}", value),
                Err(err) => {
                    reporter.report_runtime_error(err.to_string());
                    break;
                }
            }
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

    // FIXME(yanchith): don't return a value from here -> even
    // expression statements should not return anything. Instead allow
    // interpretting expressions in repl explicitely. Maybe `Program`
    // should be an enum: `Expr | Stmts` and `interpret` should be
    // able to handle expression programs?
    fn eval_stmt(&mut self, stmt: &ast::Stmt) -> InterpretResult<Value> {
        match stmt {
            ast::Stmt::VarDecl(var_decl) => {
                let value = match var_decl.initializer() {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Nil,
                };

                self.env
                    .borrow_mut()
                    .define(var_decl.ident().to_string(), value);

                Ok(Value::Nil)
            }
            ast::Stmt::FunDecl(fun_decl) => {
                let function = FunctionCallable::new(fun_decl.clone(), Rc::clone(&self.env), false);
                let value = Value::Callable(CallableValue::new(Box::new(function)));

                self.env
                    .borrow_mut()
                    .define(fun_decl.ident().to_string(), value);

                Ok(Value::Nil)
            }
            ast::Stmt::ClassDecl(class_decl) => {
                self.env
                    .borrow_mut()
                    .define(class_decl.ident().to_string(), Value::Nil);

                let mut methods = HashMap::with_capacity(class_decl.methods().len());
                for method in class_decl.methods() {
                    let function = FunctionCallable::new(
                        method.clone(),
                        Rc::clone(&self.env),
                        method.ident() == "init",
                    );
                    methods.insert(method.ident().to_string(), function);
                }

                let class = ClassValue::new(class_decl.ident().to_string(), methods);
                let value = Value::Class(Rc::new(class));

                self.env
                    .borrow_mut()
                    .assign_here(class_decl.ident(), value)
                    .expect("Class must have been declared prior to assig");

                Ok(Value::Nil)
            }
            ast::Stmt::Expr(expr) => self.eval_expr(expr.expr()),
            ast::Stmt::If(if_) => {
                let cond = self.eval_expr(if_.cond())?;
                if cond.is_truthy() {
                    self.eval_stmt(if_.then())?;
                } else if let Some(else_) = if_.else_() {
                    self.eval_stmt(else_)?;
                }

                Ok(Value::Nil)
            }
            ast::Stmt::While(while_) => {
                while self.eval_expr(while_.cond())?.is_truthy() {
                    self.eval_stmt(while_.loop_())?;
                }

                Ok(Value::Nil)
            }
            ast::Stmt::Print(print) => {
                let value = self.eval_expr(print.expr())?;
                println!("{}", value);

                Ok(Value::Nil)
            }
            ast::Stmt::Return(return_) => {
                let value = match return_.expr() {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Nil,
                };
                Err(InterpretError::Return(value))
            }
            ast::Stmt::Block(block) => {
                let new_env = Env::with_parent(Rc::clone(&self.env));
                let old_env = mem::replace(&mut self.env, Rc::new(RefCell::new(new_env)));

                let res = self.interpret_stmts(block.stmts());

                self.env = old_env;

                res.map(|()| Value::Nil)
            }
        }
    }

    fn eval_expr(&mut self, expr: &ast::Expr) -> InterpretResult<Value> {
        match expr {
            ast::Expr::Lit(lit) => self.eval_lit(lit),
            ast::Expr::Group(group) => self.eval_group(group),
            ast::Expr::Unary(unary) => self.eval_unary(unary),
            ast::Expr::Binary(binary) => self.eval_binary(binary),
            ast::Expr::Logic(logic) => self.eval_logic(logic),
            ast::Expr::Var(var) => self.eval_var(var),
            ast::Expr::Assign(assign) => self.eval_assign(assign),
            ast::Expr::Call(call) => self.eval_call(call),
            ast::Expr::Get(get) => self.eval_get(get),
            ast::Expr::Set(set) => self.eval_set(set),
            ast::Expr::This(this) => self.eval_this(this),
        }
    }

    fn eval_lit(&self, lit: &ast::LitExpr) -> InterpretResult<Value> {
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

    fn eval_group(&mut self, group: &ast::GroupExpr) -> InterpretResult<Value> {
        self.eval_expr(group.expr())
    }

    fn eval_unary(&mut self, unary: &ast::UnaryExpr) -> InterpretResult<Value> {
        let value = self.eval_expr(unary.expr())?;
        match unary.op() {
            ast::UnaryOp::Minus => match &value {
                Value::Number(number) => Ok(Value::Number(-number)),
                _ => Err(InterpretError::TypeError),
            },
            ast::UnaryOp::Not => Ok(Value::Boolean(!value.is_truthy())),
        }
    }

    fn eval_binary(&mut self, binary: &ast::BinaryExpr) -> InterpretResult<Value> {
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

    fn eval_logic(&mut self, logic: &ast::LogicExpr) -> InterpretResult<Value> {
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

    fn eval_var(&self, var: &ast::VarExpr) -> InterpretResult<Value> {
        if let Some(distance) = self.locals.get(&var.ast_id()) {
            Ok(self.env.borrow().get_at_distance(var.ident(), *distance))
        } else {
            self.globals
                .borrow()
                .get_here(var.ident())
                .ok_or(InterpretError::UndeclaredVariableUse)
        }
    }

    fn eval_assign(&mut self, assign: &ast::AssignExpr) -> InterpretResult<Value> {
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

    fn eval_call(&mut self, call: &ast::CallExpr) -> InterpretResult<Value> {
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

    fn eval_get(&mut self, get: &ast::GetExpr) -> InterpretResult<Value> {
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

    fn eval_set(&mut self, set: &ast::SetExpr) -> InterpretResult<Value> {
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

    fn eval_this(&mut self, this: &ast::ThisExpr) -> InterpretResult<Value> {
        let distance = self
            .locals
            .get(&this.ast_id())
            .expect("'this' must always be resolved");
        Ok(self.env.borrow().get_at_distance("this", *distance))
    }
}
