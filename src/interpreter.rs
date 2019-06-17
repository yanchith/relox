use std::fmt;

use crate::parser::{
    BinaryExpression, BinaryOperator, Expression, GroupingExpression, LiteralExpression, Program,
    Statement, UnaryExpression, UnaryOperator,
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

// TODO: rename to InterpretResult, InterpretError, etc..

pub struct InterpreterError {
    pub kind: InterpreterErrorKind,
    // TODO: add token/span here
    // token: Token,
}

impl InterpreterError {
    pub fn type_error() -> Self {
        InterpreterError {
            kind: InterpreterErrorKind::TypeError,
        }
    }
}

pub enum InterpreterErrorKind {
    TypeError,
}

pub type InterpreterResult<T> = Result<T, InterpreterError>;

pub struct Interpreter;

impl Interpreter {
    pub fn new() -> Self {
        Self
    }

    pub fn interpret(&self, reporter: &mut Reporter, program: &Program) -> Option<Value> {
        let mut last_value = None;

        for stmt in program.statements() {
            last_value = self.interpret_statement(reporter, stmt);
        }

        last_value
    }

    fn interpret_statement(&self, reporter: &mut Reporter, stmt: &Statement) -> Option<Value> {
        match stmt {
            Statement::Expression(expr_stmt) => {
                self.interpret_expression(reporter, expr_stmt.expression())
            }
            Statement::Print(print_stmt) => {
                match self.interpret_expression(reporter, print_stmt.expression()) {
                    Some(value) => {
                        println!("{}", value);
                        Some(value)
                    }
                    None => None,
                }
            }
        }
    }

    fn interpret_expression(
        &self,
        reporter: &mut Reporter,
        expression: &Expression,
    ) -> Option<Value> {
        match evaluate_expression(expression) {
            Ok(value) => Some(value),
            Err(err) => {
                match err.kind {
                    InterpreterErrorKind::TypeError => {
                        reporter.report_runtime_error("Type Error");
                    }
                }
                None
            }
        }
    }
}

fn evaluate_expression(expression: &Expression) -> InterpreterResult<Value> {
    match expression {
        Expression::Literal(literal) => Ok(evaluate_literal(literal)),
        Expression::Grouping(grouping) => evaluate_grouping(grouping),
        Expression::Unary(unary) => evaluate_unary(unary),
        Expression::Binary(binary) => evaluate_binary(binary),
    }
}

fn evaluate_literal(literal: &LiteralExpression) -> Value {
    match literal {
        LiteralExpression::Number(number) => Value::Number(*number),
        // TODO: should this clone?
        LiteralExpression::String(string) => Value::String(string.clone()),
        LiteralExpression::Boolean(boolean) => Value::Boolean(*boolean),
        LiteralExpression::Nil => Value::Nil,
    }
}

fn evaluate_grouping(grouping: &GroupingExpression) -> InterpreterResult<Value> {
    evaluate_expression(grouping.expression())
}

fn evaluate_unary(unary: &UnaryExpression) -> InterpreterResult<Value> {
    let value = evaluate_expression(unary.expression())?;
    match unary.operator() {
        UnaryOperator::Minus => match &value {
            Value::Number(number) => Ok(Value::Number(-number)),
            _ => Err(InterpreterError::type_error()),
        },
        UnaryOperator::Not => Ok(Value::Boolean(!is_truthy(&value))),
    }
}

fn evaluate_binary(binary: &BinaryExpression) -> InterpreterResult<Value> {
    let left_value = evaluate_expression(binary.left_expression())?;
    let right_value = evaluate_expression(binary.right_expression())?;

    match binary.operator() {
        BinaryOperator::Plus => match (left_value, right_value) {
            (Value::String(left), Value::String(right)) => Ok(Value::String(left + &right)),
            (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left + right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::Minus => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left - right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::Multiply => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left * right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::Divide => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Number(left / right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::Greater => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left > right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::GreaterEqual => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left >= right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::Less => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left < right)),
            _ => Err(InterpreterError::type_error()),
        },
        BinaryOperator::LessEqual => match (left_value, right_value) {
            (Value::Number(left), Value::Number(right)) => Ok(Value::Boolean(left <= right)),
            _ => Err(InterpreterError::type_error()),
        },
        // Note: in Lox, NaN == NaN, but our implementation uses Rust
        // and IEEE 754 semantics, where NaN != NaN
        BinaryOperator::Equal => Ok(Value::Boolean(left_value == right_value)),
        BinaryOperator::NotEqual => Ok(Value::Boolean(left_value != right_value)),
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
