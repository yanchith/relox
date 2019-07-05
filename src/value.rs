use std::fmt;
use std::rc::Rc;

use crate::callable::Callable;
use crate::interpreter::{InterpretResult, Interpreter};

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

impl Value {
    /// Everything is truthy, except `false` and `nil`
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Boolean(boolean) => *boolean,
            Value::Nil => false,
            _ => true,
        }
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

    pub fn call(&self, interpreter: &mut Interpreter, args: &[Value]) -> InterpretResult<Value> {
        self.callable.call(interpreter, args)
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
