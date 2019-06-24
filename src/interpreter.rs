use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use crate::environment::{AssignError, Environment};
use crate::parser::{
    AssignmentExpr, BinaryExpr, BinaryOp, CallExpr, Expr, GroupExpr, LitExpr, LogicExpr, LogicOp,
    Program, Stmt, UnaryExpr, UnaryOp, VarExpr,
};
use crate::reporter::Reporter;

/// A Lox Value.
///
/// Since we don't really have a garbage collector, heap allocated
/// values are behind an `Rc` pointer as a poor man's GC. As far as
/// lox spec goes, only functions (via closures) and classes (via
/// fields) can cause a reference cycle. Cloning a value is always
/// cheap, it is either a small value type, or a pointer.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A 64-bit floating point number.
    Number(f64),
    /// An 8-bit boolean.
    Boolean(bool),
    /// The `Nil` singleton value, only equal to itself.
    Nil,
    /// A heap allocated string, stored behind an `Rc` pointer, the
    /// string is not mutable, so no `RefCell` is used to contain it.
    /// Strings are compared by value, not identity.
    String(Rc<String>),
    /// A value callable with the function call
    /// syntax. `CallableValue` internally has an `Rc` pointer to the
    /// actual function implementation.
    Callable(CallableValue),
}

#[derive(Debug, Clone)]
pub struct CallableValue {
    callable: Rc<dyn Callable>,
}

impl CallableValue {
    pub fn new(callable: Box<dyn Callable>) -> Self {
        Self {
            callable: Rc::from(callable),
        }
    }

    pub fn arity(&self) -> usize {
        self.callable.arity()
    }

    pub fn call(&self, arguments: &[Value]) -> Value {
        self.callable.call(arguments)
    }
}

impl PartialEq for CallableValue {
    /// Two callable values are equal if their function pointers are equal
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.callable, &other.callable)
    }
}

impl fmt::Display for CallableValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<callable {:p}>", &self.callable)
    }
}

pub trait Callable: fmt::Debug {
    fn arity(&self) -> usize;
    fn call(&self, arguments: &[Value]) -> Value;
}

#[derive(Debug)]
struct NativeCallableClock;

impl Callable for NativeCallableClock {
    fn arity(&self) -> usize {
        0
    }

    fn call(&self, _: &[Value]) -> Value {
        let now = SystemTime::now();
        let since_the_epoch = now
            .duration_since(UNIX_EPOCH)
            .unwrap_or(Duration::from_secs(0));
        let millis = since_the_epoch.as_millis();

        Value::Number(millis as f64)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Number(number) => write!(f, "{}", number),
            Value::String(string) => write!(f, "\"{}\"", string),
            Value::Boolean(boolean) => write!(f, "{}", boolean),
            Value::Nil => write!(f, "nil"),
            Value::Callable(callable) => write!(f, "{}", callable),
        }
    }
}

// TODO: add Token/Span info
// TODO: implement std::error:Error
// TODO: implement std::fmt::Display
#[derive(Debug)]
pub enum InterpretError {
    TypeError,
    ValueNotCallable(Value),
    WrongNumberOfArgumentsToCallable(usize, usize), // TODO: add callable ident
    UndeclaredVariableUse, // TODO: add variable name
    UndeclaredVariableAssignment(String),
}

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InterpretError::TypeError => write!(f, "Type Error"),
            InterpretError::ValueNotCallable(value) => {
                write!(f, "Type Error: value not callable {}", value)
            }
            InterpretError::WrongNumberOfArgumentsToCallable(provided, required) => write!(
                f,
                "Wrong number of arguments passed to callable (provided {}, required {})",
                provided, required,
            ),
            InterpretError::UndeclaredVariableUse => write!(f, "Use of undeclared variable"),
            InterpretError::UndeclaredVariableAssignment(ident) => {
                write!(f, "Assignment to undeclared variable {}", ident)
            }
        }
    }
}

pub type InterpretResult<T> = Result<T, InterpretError>;

pub struct Interpreter {
    // Even thogh this is an `Option`, one should never observe `None`
    // here outside of `push_env()` and `pop_env()`
    environment: Option<Environment>,
}

impl Interpreter {
    pub fn new() -> Self {
        let mut environment = Environment::new();
        environment.define(
            "clock".to_string(),
            Value::Callable(CallableValue::new(Box::new(NativeCallableClock))),
        );

        Self {
            environment: Some(environment),
        }
    }

    pub fn interpret(&mut self, reporter: &mut Reporter, program: &Program) {
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

    fn eval_stmt(&mut self, stmt: &Stmt) -> InterpretResult<Value> {
        match stmt {
            Stmt::VarDecl(var_decl_stmt) => {
                let value = match var_decl_stmt.initializer() {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Nil,
                };

                // TODO: intern idents to prevent cloning
                self.environment
                    .as_mut()
                    .expect("Environment must be present at all times")
                    .define(var_decl_stmt.ident().to_string(), value);

                Ok(Value::Nil)
            }
            Stmt::Expr(expr_stmt) => self.eval_expr(expr_stmt.expr()),
            Stmt::If(if_stmt) => {
                let cond = self.eval_expr(if_stmt.cond())?;
                if is_truthy(&cond) {
                    self.eval_stmt(if_stmt.then())?;
                } else if let Some(else_) = if_stmt.else_() {
                    self.eval_stmt(else_)?;
                }

                Ok(Value::Nil)
            }
            Stmt::While(while_stmt) => {
                while is_truthy(&self.eval_expr(while_stmt.cond())?) {
                    self.eval_stmt(while_stmt.loop_())?;
                }

                Ok(Value::Nil)
            }
            Stmt::Print(print_stmt) => {
                let value = self.eval_expr(print_stmt.expr())?;
                println!("{}", value);

                Ok(Value::Nil)
            }
            Stmt::Block(block_stmt) => {
                let mut error = None;

                self.push_env();

                for stmt in block_stmt.stmts() {
                    // Even if this errors, we can not unwind without
                    // cleaning up the environment! Therefore we store
                    // the error, perform the cleanup, and only
                    // afterwards return the error.
                    if let Err(err) = self.eval_stmt(stmt) {
                        error = Some(err);
                        break;
                    }
                }

                self.pop_env();

                if let Some(err) = error {
                    Err(err)
                } else {
                    Ok(Value::Nil)
                }
            }
        }
    }

    fn push_env(&mut self) {
        assert!(
            self.environment.is_some(),
            "Environment must be present at all times",
        );

        let outer_environment = self
            .environment
            .take()
            .expect("Environment must be present at all times");
        let inner_environment = Environment::with_parent(outer_environment);
        self.environment.replace(inner_environment);

        assert!(
            self.environment.is_some(),
            "Environment must be present at all times",
        );
    }

    fn pop_env(&mut self) {
        assert!(
            self.environment.is_some(),
            "Environment must be present at all times",
        );

        let inner_environment = self
            .environment
            .take()
            .expect("Environment must be present at all times");
        let outer_environment = inner_environment
            .into_parent()
            .expect("Must be able to pop a parent environment from a local one");
        self.environment.replace(outer_environment);

        assert!(
            self.environment.is_some(),
            "Environment must be present at all times",
        );
    }

    fn eval_expr(&mut self, expr: &Expr) -> InterpretResult<Value> {
        match expr {
            Expr::Lit(lit) => self.eval_lit(lit),
            Expr::Group(group) => self.eval_group(group),
            Expr::Unary(unary) => self.eval_unary(unary),
            Expr::Binary(binary) => self.eval_binary(binary),
            Expr::Logic(logic) => self.eval_logic(logic),
            Expr::Var(var) => self.eval_var(var),
            Expr::Assignment(assignment) => self.eval_assignment(assignment),
            Expr::Call(call) => self.eval_call(call),
        }
    }

    fn eval_lit(&self, lit: &LitExpr) -> InterpretResult<Value> {
        let value = match lit {
            LitExpr::Number(number) => Value::Number(*number),
            // We clone the string from the AST, as we may be
            // instantiating it multiple times and we don't want the
            // instances to share storage (even though we currently
            // don't support mutation on strings).
            // TODO: optimize this... if we decide never to mutate
            // strings, we can put the string in the token/ast in an
            // Rc as well, otherwise we can maybe clone on write (Cow)
            // instead?
            LitExpr::String(string) => Value::String(Rc::new(string.clone())),
            LitExpr::Boolean(boolean) => Value::Boolean(*boolean),
            LitExpr::Nil => Value::Nil,
        };

        Ok(value)
    }

    fn eval_group(&mut self, group: &GroupExpr) -> InterpretResult<Value> {
        self.eval_expr(group.expr())
    }

    fn eval_unary(&mut self, unary: &UnaryExpr) -> InterpretResult<Value> {
        let value = self.eval_expr(unary.expr())?;
        match unary.op() {
            UnaryOp::Minus => match &value {
                Value::Number(number) => Ok(Value::Number(-number)),
                _ => Err(InterpretError::TypeError),
            },
            UnaryOp::Not => Ok(Value::Boolean(!is_truthy(&value))),
        }
    }

    fn eval_binary(&mut self, binary: &BinaryExpr) -> InterpretResult<Value> {
        let left_value = self.eval_expr(binary.left())?;
        let right_value = self.eval_expr(binary.right())?;

        match binary.op() {
            BinaryOp::Plus => match (left_value, right_value) {
                (Value::String(left), Value::String(right)) => {
                    let mut result: String = String::with_capacity(left.len() + right.len());
                    result.push_str(&left);
                    result.push_str(&right);
                    Ok(Value::String(Rc::new(result)))
                }
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left + right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::Minus => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left - right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::Multiply => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left * right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::Divide => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left / right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::Greater => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left > right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::GreaterEqual => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left >= right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::Less => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left < right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOp::LessEqual => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left <= right)),
                _ => Err(InterpretError::TypeError),
            },
            // Note: officially in Lox, NaN == NaN, but our
            // implementation uses Rust and IEEE 754 semantics, where
            // NaN != NaN
            BinaryOp::Equal => Ok(Value::Boolean(left_value == right_value)),
            BinaryOp::NotEqual => Ok(Value::Boolean(left_value != right_value)),
        }
    }

    fn eval_logic(&mut self, logic: &LogicExpr) -> InterpretResult<Value> {
        let left_value = self.eval_expr(logic.left())?;

        match logic.op() {
            LogicOp::And => {
                if is_truthy(&left_value) {
                    Ok(self.eval_expr(logic.right())?)
                } else {
                    Ok(left_value)
                }
            }
            LogicOp::Or => {
                if is_truthy(&left_value) {
                    Ok(left_value)
                } else {
                    Ok(self.eval_expr(logic.right())?)
                }
            }
        }
    }

    fn eval_var(&self, var: &VarExpr) -> InterpretResult<Value> {
        self.environment
            .as_ref()
            .expect("Environment must be present at all times")
            .get(var.ident())
            .cloned()
            .ok_or(InterpretError::UndeclaredVariableUse)
    }

    fn eval_assignment(&mut self, assignment: &AssignmentExpr) -> InterpretResult<Value> {
        let lvalue = assignment.target();
        let rvalue = self.eval_expr(assignment.expr())?;

        let environment = self
            .environment
            .as_mut()
            .expect("Environment must be present at all times");

        match environment.assign(lvalue.ident(), rvalue.clone()) {
            Ok(()) => Ok(rvalue),
            Err(AssignError::ValueNotDeclared) => {
                let ident = lvalue.ident().to_string();
                Err(InterpretError::UndeclaredVariableAssignment(ident))
            }
        }
    }

    fn eval_call(&mut self, call: &CallExpr) -> InterpretResult<Value> {
        let callee = self.eval_expr(call.callee())?;

        if let Value::Callable(callable_value) = callee {
            let provided_args_len = call.arguments().len();
            let required_args_len = callable_value.arity();
            if provided_args_len != required_args_len {
                Err(InterpretError::WrongNumberOfArgumentsToCallable(
                    provided_args_len,
                    required_args_len,
                ))
            } else {
                let mut arguments = Vec::with_capacity(call.arguments().len());

                for argument_expr in call.arguments() {
                    let arg = self.eval_expr(argument_expr)?;
                    arguments.push(arg);
                }

                Ok(callable_value.call(&arguments))
            }
        } else {
            Err(InterpretError::ValueNotCallable(callee))
        }
    }
}

/// Everything is truthy, except `false` and `nil`
fn is_truthy(value: &Value) -> bool {
    match value {
        Value::Boolean(boolean) => *boolean,
        Value::Nil => false,
        _ => true,
    }
}
