pub struct Reporter {
    compile_errors: Vec<String>,
    runtime_error: Option<String>,
}

// FIXME(yanchith): span reporting

impl Reporter {
    pub fn new() -> Self {
        Self {
            compile_errors: Vec::new(),
            runtime_error: None,
        }
    }

    pub fn has_compile_error(&self) -> bool {
        !self.compile_errors.is_empty()
    }

    pub fn has_runtime_error(&self) -> bool {
        self.runtime_error.is_some()
    }

    // FIXME(yanchith): just be able to get the reports, don't print them in here
    pub fn print_all_errors(&mut self) {
        for message in &self.compile_errors {
            eprintln!("Compile Error: {}", message);
        }
        self.compile_errors.clear();

        if let Some(message) = self.runtime_error.take() {
            eprintln!("Runtime Error: {}", message);
        }
    }

    pub fn report_compile_error(&mut self, message: String) {
        self.compile_errors.push(message);
    }

    pub fn report_runtime_error(&mut self, message: String) {
        self.runtime_error = Some(message);
    }

    pub fn clear_compile_errors(&mut self) {
        self.compile_errors.clear();
    }
}
