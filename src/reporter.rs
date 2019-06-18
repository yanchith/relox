use crate::lexer::Span;

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
                ErrorReport::MessageSpan(message, span) => {
                    eprintln!("Error on line {}: {}", span.line_range.start, message);
                }
            }
        }
        self.compile_errors.clear();

        if let Some(report) = self.runtime_error.take() {
            match report {
                ErrorReport::Message(message) => eprintln!("Error: {}", message),
                ErrorReport::MessageSpan(message, span) => {
                    eprintln!("Error on line {}: {}", span.line_range.start, message);
                }
            }
        }
    }

    pub fn report_compile_error(&mut self, message: &str) {
        self.compile_errors
            .push(ErrorReport::Message(message.to_string()));
    }

    pub fn report_compile_error_on_span(&mut self, message: &str, span: &Span) {
        self.compile_errors
            .push(ErrorReport::MessageSpan(message.to_string(), span.clone()));
    }

    pub fn report_runtime_error(&mut self, message: &str) {
        self.runtime_error = Some(ErrorReport::Message(message.to_string()));
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ErrorReport {
    Message(String),
    MessageSpan(String, Span),
}
