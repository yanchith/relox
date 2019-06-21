use std::collections::HashMap;

use crate::interpreter::Value;

// TODO: std::fmt and error::Error
pub enum AssignError {
    ValueNotDeclared,
}

pub struct Environment {
    // TODO: intern idents!
    values: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
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
        } else {
            Err(AssignError::ValueNotDeclared)
        }
    }

    pub fn get(&self, ident: &str) -> Option<&Value> {
        self.values.get(ident)
    }
}
