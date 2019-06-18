use std::fmt;

use crate::environment::Environment;
use crate::parser::{
    BinaryExpr, BinaryOperator, Expr, GroupExpr, LitExpr, Program, Stmt, UnaryExpr, UnaryOperator,
    VarExpr,
};
use crate::reporter::Reporter;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    String(String),
    Boolean(bool),
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

// TODO: add Token or Span info to this error
pub enum InterpretError {
    TypeError,
    UndeclaredVariableUse,
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

                // TODO: don't clone if possible....
                self.environment
                    .define(var_decl.ident().to_string(), value.clone());

                Some(value)
            }
        }
    }

    fn interpret_expr(&self, reporter: &mut Reporter, expr: &Expr) -> Option<Value> {
        match self.evaluate_expr(expr) {
            Ok(value) => Some(value),
            Err(InterpretError::TypeError) => {
                reporter.report_runtime_error("Type Error");
                None
            }
            Err(InterpretError::UndeclaredVariableUse) => {
                reporter.report_runtime_error("Use of undeclared variable");
                None
            }
        }
    }

    fn evaluate_expr(&self, expr: &Expr) -> InterpretResult<Value> {
        match expr {
            Expr::Lit(lit) => self.evaluate_lit(lit),
            Expr::Group(group) => self.evaluate_group(group),
            Expr::Unary(unary) => self.evaluate_unary(unary),
            Expr::Binary(binary) => self.evaluate_binary(binary),
            Expr::Var(var) => self.evaluate_var(var),
        }
    }

    fn evaluate_lit(&self, lit: &LitExpr) -> InterpretResult<Value> {
        let value = match lit {
            LitExpr::Number(number) => Value::Number(*number),
            // TODO: should this clone?
            LitExpr::String(string) => Value::String(string.clone()),
            LitExpr::Boolean(boolean) => Value::Boolean(*boolean),
            LitExpr::Nil => Value::Nil,
        };

        Ok(value)
    }

    fn evaluate_group(&self, group: &GroupExpr) -> InterpretResult<Value> {
        self.evaluate_expr(group.expr())
    }

    fn evaluate_unary(&self, unary: &UnaryExpr) -> InterpretResult<Value> {
        let value = self.evaluate_expr(unary.expr())?;
        match unary.operator() {
            UnaryOperator::Minus => match &value {
                Value::Number(number) => Ok(Value::Number(-number)),
                _ => Err(InterpretError::TypeError),
            },
            UnaryOperator::Not => Ok(Value::Boolean(!is_truthy(&value))),
        }
    }

    fn evaluate_binary(&self, binary: &BinaryExpr) -> InterpretResult<Value> {
        let left_value = self.evaluate_expr(binary.left_expr())?;
        let right_value = self.evaluate_expr(binary.right_expr())?;

        match binary.operator() {
            BinaryOperator::Plus => match (left_value, right_value) {
                (Value::String(left), Value::String(right)) => Ok(Value::String(left + &right)),
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
        // TODO: we are cloning strings left and right...
        self.environment
            .get(var.ident())
            .cloned()
            .ok_or(InterpretError::UndeclaredVariableUse)
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
