use std::collections::HashMap;

use crate::interpreter::Value;

pub struct Environment {
    // TODO: intern identifiers!
    values: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Self {
        Self { values: HashMap::new() }
    }

    pub fn define(&mut self, identifier: String, value: Value) {
        self.values.insert(identifier, value);
    }

    pub fn get(&self, identifier: &str) -> Option<&Value> {
        self.values.get(identifier)
    }
}
