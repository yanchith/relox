use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::interpreter::Value;

// TODO: std::fmt and error::Error
pub enum AssignError {
    ValueNotDeclared,
}

#[derive(Debug)]
pub struct Env {
    parent: Option<Rc<RefCell<Env>>>,
    // TODO: intern idents!
    values: HashMap<String, Value>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            parent: None,
            values: HashMap::new(),
        }
    }

    pub fn with_parent(parent: Rc<RefCell<Self>>) -> Self {
        Self {
            parent: Some(parent),
            values: HashMap::new(),
        }
    }

    pub fn define(&mut self, ident: String, value: Value) {
        self.values.insert(ident, value);
    }

    pub fn assign(&mut self, ident: &str, new_value: Value) -> Result<(), AssignError> {
        if let Some(value) = self.values.get_mut(ident) {
            *value = new_value;
            Ok(())
        } else if let Some(parent) = &self.parent {
            let mut parent = parent.borrow_mut();
            parent.assign(ident, new_value)
        } else {
            Err(AssignError::ValueNotDeclared)
        }
    }

    pub fn get(&self, ident: &str) -> Option<Value> {
        self.values.get(ident).cloned().or_else(|| {
            if let Some(parent) = &self.parent {
                parent.borrow().get(ident)
            } else {
                None
            }
        })
    }
}
