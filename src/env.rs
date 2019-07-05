use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::interpreter::Value;

// FIXME(yanchith): std::fmt and error::Error
pub enum AssignError {
    ValueNotDeclared,
}

#[derive(Debug)]
pub struct Env {
    parent: Option<Rc<RefCell<Env>>>,
    // FIXME(yanchith): intern idents!
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
        if let Some(value_ptr) = self.values.get_mut(ident) {
            *value_ptr = new_value;
            Ok(())
        } else if let Some(parent) = &self.parent {
            let mut parent = parent.borrow_mut();
            parent.assign(ident, new_value)
        } else {
            Err(AssignError::ValueNotDeclared)
        }
    }

    pub fn assign_at_distance(&mut self, ident: &str, distance: u64, new_value: Value) {
        if distance == 0 {
            let value_ptr = self
                .values
                .get_mut(ident)
                .expect("`assign_at_distance()` must always find the value slot");
            *value_ptr = new_value;
        } else {
            self.parent
                .as_mut()
                .expect("`assign_at_distance()` must always find a parent env")
                .borrow_mut()
                .assign_at_distance(ident, distance - 1, new_value)
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

    pub fn get_at_distance(&self, ident: &str, distance: u64) -> Value {
        if distance == 0 {
            self.values
                .get(ident)
                .cloned()
                .expect("`get_at_distance()` must always find the value slot")
        } else {
            self.parent
                .as_ref()
                .expect("`get_at_distance()` must always find a parent env")
                .borrow()
                .get_at_distance(ident, distance - 1)
        }
    }
}
