use std::collections::HashMap;

use crate::interpreter::Value;

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

    pub fn get(&self, ident: &str) -> Option<&Value> {
        self.values.get(ident)
    }
}
