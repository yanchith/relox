use std::fmt;
use std::rc::Rc;

use crate::environment::{AssignError, Environment};
use crate::parser::{
    AssignmentExpr, BinaryExpr, BinaryOperator, Expr, GroupExpr, LitExpr, Program, Stmt, UnaryExpr,
    UnaryOperator, VarExpr,
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

// TODO: add Token/Span/ident info
// TODO: implement std::error:Error
// TODO: implement std::fmt::Display
#[derive(Debug)]
pub enum InterpretError {
    TypeError,
    UndeclaredVariableUse,
    UndeclaredVariableAssignment(String),
}

pub type InterpretResult<T> = Result<T, InterpretError>;

pub struct Interpreter {
    environment: Environment,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }

    pub fn interpret(&mut self, reporter: &mut Reporter, program: &Program) -> Option<Value> {
        let mut last_value = None;

        for stmt in program.stmts() {
            last_value = self.interpret_stmt(reporter, stmt);
        }

        last_value
    }

    fn interpret_stmt(&mut self, reporter: &mut Reporter, stmt: &Stmt) -> Option<Value> {
        match stmt {
            Stmt::Expr(expr_stmt) => self.interpret_expr(reporter, expr_stmt.expr()),
            Stmt::Print(print_stmt) => {
                let value = self.interpret_expr(reporter, print_stmt.expr())?;
                println!("{}", value);
                Some(value)
            }
            Stmt::VarDecl(var_decl) => {
                let value = match var_decl.initializer_expr() {
                    Some(expr) => self.interpret_expr(reporter, expr)?,
                    None => Value::Nil,
                };

                // TODO: intern idents to prevent cloning
                self.environment
                    .define(var_decl.ident().to_string(), value.clone());

                Some(value)
            }
        }
    }

    fn interpret_expr(&mut self, reporter: &mut Reporter, expr: &Expr) -> Option<Value> {
        match self.evaluate_expr(expr) {
            Ok(value) => Some(value),
            Err(InterpretError::TypeError) => {
                reporter.report_runtime_error("Type Error".to_string());
                None
            }
            Err(InterpretError::UndeclaredVariableUse) => {
                reporter.report_runtime_error("Use of undeclared variable".to_string());
                None
            }
            Err(InterpretError::UndeclaredVariableAssignment(ident)) => {
                reporter
                    .report_runtime_error(format!("Assignment to undeclared variable {}", ident));
                None
            }
        }
    }

    fn evaluate_expr(&mut self, expr: &Expr) -> InterpretResult<Value> {
        match expr {
            Expr::Lit(lit) => self.evaluate_lit(lit),
            Expr::Group(group) => self.evaluate_group(group),
            Expr::Unary(unary) => self.evaluate_unary(unary),
            Expr::Binary(binary) => self.evaluate_binary(binary),
            Expr::Var(var) => self.evaluate_var(var),
            Expr::Assignment(assignment) => self.evaluate_assignment(assignment),
        }
    }

    fn evaluate_lit(&self, lit: &LitExpr) -> InterpretResult<Value> {
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

    fn evaluate_group(&mut self, group: &GroupExpr) -> InterpretResult<Value> {
        self.evaluate_expr(group.expr())
    }

    fn evaluate_unary(&mut self, unary: &UnaryExpr) -> InterpretResult<Value> {
        let value = self.evaluate_expr(unary.expr())?;
        match unary.operator() {
            UnaryOperator::Minus => match &value {
                Value::Number(number) => Ok(Value::Number(-number)),
                _ => Err(InterpretError::TypeError),
            },
            UnaryOperator::Not => Ok(Value::Boolean(!is_truthy(&value))),
        }
    }

    fn evaluate_binary(&mut self, binary: &BinaryExpr) -> InterpretResult<Value> {
        let left_value = self.evaluate_expr(binary.left_expr())?;
        let right_value = self.evaluate_expr(binary.right_expr())?;

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

    fn evaluate_var(&self, var: &VarExpr) -> InterpretResult<Value> {
        self.environment
            .get(var.ident())
            .cloned()
            .ok_or(InterpretError::UndeclaredVariableUse)
    }

    fn evaluate_assignment(&mut self, assignment: &AssignmentExpr) -> InterpretResult<Value> {
        let lvalue = assignment.target();
        let rvalue = self.evaluate_expr(assignment.expr())?;

        match self.environment.assign(lvalue.ident(), rvalue.clone()) {
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
