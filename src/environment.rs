use std::collections::HashMap;

use crate::interpreter::Value;

// TODO: std::fmt and error::Error
pub enum AssignError {
    ValueNotDeclared,
}

pub struct Environment {
    parent: Option<Box<Environment>>,
    // TODO: intern idents!
    values: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            parent: None,
            values: HashMap::new(),
        }
    }

    pub fn with_parent(parent: Self) -> Self {
        Self {
            parent: Some(Box::new(parent)),
            values: HashMap::new(),
        }
    }

    pub fn into_parent(self) -> Option<Self> {
        if let Some(parent) = self.parent {
            Some(*parent)
        } else {
            None
        }
    }

    pub fn define(&mut self, ident: String, value: Value) {
        self.values.insert(ident, value);
    }

    pub fn assign(&mut self, ident: &str, new_value: Value) -> Result<(), AssignError> {
        if let Some(value) = self.values.get_mut(ident) {
            *value = new_value;
            Ok(())
        } else if let Some(parent) = &mut self.parent {
            parent.assign(ident, new_value)
        } else {
            Err(AssignError::ValueNotDeclared)
        }
    }

    pub fn get(&self, ident: &str) -> Option<&Value> {
        self.values.get(ident).or_else(|| {
            if let Some(parent) = &self.parent {
                parent.get(ident)
            } else {
                None
            }
        })
    }
}
