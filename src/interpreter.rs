use std::fmt;
use std::rc::Rc;

use crate::environment::{AssignError, Environment};
use crate::parser::{
    AssignmentExpr, BinaryExpr, BinaryOperator, Expr, GroupExpr, LitExpr, LogicExpr, LogicOperator,
    Program, Stmt, UnaryExpr, UnaryOperator, VarExpr,
};
use crate::reporter::Reporter;

/// A Lox Value.
///
/// Since we don't really have a garbage collector, heap allocated
/// values are behind an `Rc` pointer as a poor man's GC. This also
/// means that cloning a value is always cheap.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A 64-bit floating point number.
    Number(f64),
    /// A heap allocated string, stored behind an `Rc` pointer, the
    /// string is not mutable, so no `RefCell` is used to contain it.
    String(Rc<String>),
    /// An 8-bit boolean.
    Boolean(bool),
    /// The `Nil` singleton value, only equal to itself.
    Nil,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Number(number) => write!(f, "{}", number),
            Value::String(string) => write!(f, "\"{}\"", string),
            Value::Boolean(boolean) => write!(f, "{}", boolean),
            Value::Nil => write!(f, "nil"),
        }
    }
}

// TODO: add Token/Span info
// TODO: implement std::error:Error
// TODO: implement std::fmt::Display
#[derive(Debug)]
pub enum InterpretError {
    TypeError,
    UndeclaredVariableUse, // TODO: add variable name
    UndeclaredVariableAssignment(String),
}

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InterpretError::TypeError => write!(f, "Type Error"),
            InterpretError::UndeclaredVariableUse => write!(f, "Use of undeclared variable"),
            InterpretError::UndeclaredVariableAssignment(ident) => {
                write!(f, "Assignment to undeclared variable {}", ident,)
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
        Self {
            environment: Some(Environment::new()),
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
            Stmt::Expr(expr_stmt) => self.eval_expr(expr_stmt.expr()),
            Stmt::If(if_stmt) => {
                let cond = self.eval_expr(if_stmt.cond_expr())?;
                if is_truthy(&cond) {
                    self.eval_stmt(if_stmt.then_stmt())?;
                } else if let Some(else_stmt) = if_stmt.else_stmt() {
                    self.eval_stmt(else_stmt)?;
                }

                Ok(Value::Nil)
            }
            Stmt::Print(print_stmt) => {
                let value = self.eval_expr(print_stmt.expr())?;
                println!("{}", value);

                Ok(Value::Nil)
            }
            Stmt::VarDecl(var_decl) => {
                let value = match var_decl.initializer_expr() {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Nil,
                };

                // TODO: intern idents to prevent cloning
                self.environment
                    .as_mut()
                    .expect("Environment must be present at all times")
                    .define(var_decl.ident().to_string(), value);

                Ok(Value::Nil)
            }
            Stmt::Block(block) => {
                let mut error = None;

                self.push_env();

                for stmt in block.stmts() {
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
        match unary.operator() {
            UnaryOperator::Minus => match &value {
                Value::Number(number) => Ok(Value::Number(-number)),
                _ => Err(InterpretError::TypeError),
            },
            UnaryOperator::Not => Ok(Value::Boolean(!is_truthy(&value))),
        }
    }

    fn eval_binary(&mut self, binary: &BinaryExpr) -> InterpretResult<Value> {
        let left_value = self.eval_expr(binary.left_expr())?;
        let right_value = self.eval_expr(binary.right_expr())?;

        match binary.operator() {
            BinaryOperator::Plus => match (left_value, right_value) {
                (Value::String(left), Value::String(right)) => {
                    let mut result: String = String::with_capacity(left.len() + right.len());
                    result.push_str(&left);
                    result.push_str(&right);
                    Ok(Value::String(Rc::new(result)))
                }
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left + right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::Minus => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left - right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::Multiply => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left * right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::Divide => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left / right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::Greater => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left > right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::GreaterEqual => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left >= right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::Less => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left < right)),
                _ => Err(InterpretError::TypeError),
            },
            BinaryOperator::LessEqual => match (left_value, right_value) {
                (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left <= right)),
                _ => Err(InterpretError::TypeError),
            },
            // Note: officially in Lox, NaN == NaN, but our
            // implementation uses Rust and IEEE 754 semantics, where
            // NaN != NaN
            BinaryOperator::Equal => Ok(Value::Boolean(left_value == right_value)),
            BinaryOperator::NotEqual => Ok(Value::Boolean(left_value != right_value)),
        }
    }

    fn eval_logic(&mut self, logic: &LogicExpr) -> InterpretResult<Value> {
        let left_value = self.eval_expr(logic.left_expr())?;

        match logic.operator() {
            LogicOperator::And => {
                if is_truthy(&left_value) {
                    Ok(self.eval_expr(logic.right_expr())?)
                } else {
                    Ok(left_value)
                }
            }
            LogicOperator::Or => {
                if is_truthy(&left_value) {
                    Ok(left_value)
                } else {
                    Ok(self.eval_expr(logic.right_expr())?)
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
}

/// Everything is truthy, except `false` and `nil`
fn is_truthy(value: &Value) -> bool {
    match value {
        Value::Boolean(boolean) => *boolean,
        Value::Nil => false,
        _ => true,
    }
}
