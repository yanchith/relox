use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use crate::callable::{Callable, FunctionCallable};
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
    /// A class. Stored behind `Rc` so that it can be passed around by
    /// value of its reference and that the instances can have a
    /// pointer to it too.
    Class(Rc<ClassValue>),
    /// A class instance. Stored behind `Rc<RefCell>` so it can be
    /// passed around by value of its reference and fields can be
    /// mutated.
    Instance(Rc<RefCell<InstanceValue>>),
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
            Value::Class(class) => write!(f, "{}", class),
            Value::Instance(instance) => write!(f, "{}", instance.borrow()),
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

#[derive(Debug, Clone, PartialEq)]
pub struct ClassValue {
    ident: String, // FIXME(yanchith): intern idents
    superclass: Option<Rc<ClassValue>>,
    methods: HashMap<String, FunctionCallable>,
}

impl ClassValue {
    pub fn new(
        ident: String,
        superclass: Option<Rc<ClassValue>>,
        methods: HashMap<String, FunctionCallable>,
    ) -> Self {
        Self {
            ident,
            superclass,
            methods,
        }
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    pub fn init_arity(&self) -> usize {
        if let Some(init_method) = self.find_method("init") {
            init_method.arity()
        } else {
            0
        }
    }

    pub fn init_call(
        this: Rc<ClassValue>,
        interpreter: &mut Interpreter,
        args: &[Value],
    ) -> InterpretResult<Value> {
        let instance = Rc::new(RefCell::new(InstanceValue::new(this.clone())));

        if let Some(init_method) = this.find_method("init") {
            let initializer = init_method.bind(instance.clone());
            initializer.call(interpreter, args)?;
        }

        Ok(Value::Instance(instance))
    }

    pub fn find_method(&self, name: &str) -> Option<&FunctionCallable> {
        self.methods.get(name).or_else(|| {
            self.superclass
                .as_ref()
                .map(|s| s.find_method(name))
                .unwrap_or(None)
        })
    }
}

impl fmt::Display for ClassValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<class {}>", &self.ident)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InstanceValue {
    class: Rc<ClassValue>,
    members: HashMap<String, Value>,
}

impl InstanceValue {
    pub fn new(class: Rc<ClassValue>) -> Self {
        Self {
            class,
            members: HashMap::new(),
        }
    }

    pub fn class(&self) -> &ClassValue {
        &self.class
    }

    pub fn get(this: Rc<RefCell<Self>>, field: &str) -> Option<Value> {
        let this_ref = this.borrow();
        this_ref.members.get(field).cloned().or_else(|| {
            this_ref.class.find_method(field).cloned().map(|method| {
                // FIXME(yanchith) :borrowck: can this Rc::clone be avoided?
                let bound_method = method.bind(Rc::clone(&this));
                Value::Callable(CallableValue::new(Box::new(bound_method)))
            })
        })
    }

    pub fn set(&mut self, field: String, value: Value) {
        self.members.insert(field, value);
    }
}

impl fmt::Display for InstanceValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<instance {}>", self.class.ident())
    }
}
