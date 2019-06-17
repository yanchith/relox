pub struct Reporter {
    compile_errors: Vec<ErrorReport>,
    runtime_error: Option<ErrorReport>,
}

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

    // TODO: just be able to get the reports, don't print them in here
    pub fn print_all_errors(&mut self) {
        for report in &self.compile_errors {
            match report {
                ErrorReport::Message(message) => eprintln!("Error: {}", message),
                ErrorReport::MessageLine(message, line) => {
                    eprintln!("Error on line {}: {}", line, message);
                }
                ErrorReport::MessageLinePlace(message, line, place) => {
                    eprintln!("Error on line {} around {}: {}", line, place, message);
                }
            }
        }
        self.compile_errors.clear();

        if let Some(report) = self.runtime_error.take() {
            match report {
                ErrorReport::Message(message) => eprintln!("Error: {}", message),
                ErrorReport::MessageLine(message, line) => {
                    eprintln!("Error on line {}: {}", line, message);
                }
                ErrorReport::MessageLinePlace(message, line, place) => {
                    eprintln!("Error on line {} around {}: {}", line, place, message);
                }
            }
        }
    }

    pub fn report_compile_error(&mut self, message: &str) {
        self.compile_errors
            .push(ErrorReport::Message(message.to_string()));
    }

    pub fn report_compile_error_on_line(&mut self, message: &str, line: u32) {
        self.compile_errors
            .push(ErrorReport::MessageLine(message.to_string(), line));
    }

    pub fn report_compile_error_on_line_with_place(
        &mut self,
        message: &str,
        line: u32,
        place: &str,
    ) {
        self.compile_errors.push(ErrorReport::MessageLinePlace(
            message.to_string(),
            line,
            place.to_string(),
        ));
    }

    pub fn report_runtime_error(&mut self, message: &str) {
        self.runtime_error = Some(ErrorReport::Message(message.to_string()));
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ErrorReport {
    Message(String),
    MessageLine(String, u32),
    MessageLinePlace(String, u32, String),
}
