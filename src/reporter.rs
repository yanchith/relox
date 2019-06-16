pub struct Reporter {
    error_reports: Vec<ErrorReport>,
}

impl Reporter {
    pub fn new() -> Self {
        Self {
            error_reports: Vec::new(),
        }
    }

    pub fn has_error_reports(&self) -> bool {
        !self.error_reports.is_empty()
    }

    // TODO: just be able to get the reports, don't print them in here
    pub fn print_error_reports(&self) {
        for report in &self.error_reports {
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

    pub fn report(&mut self, message: &str) {
        self.error_reports
            .push(ErrorReport::Message(message.to_string()));
    }

    pub fn report_on_line(&mut self, message: &str, line: u32) {
        self.error_reports
            .push(ErrorReport::MessageLine(message.to_string(), line));
    }

    pub fn report_on_line_with_place(&mut self, message: &str, line: u32, place: &str) {
        self.error_reports.push(ErrorReport::MessageLinePlace(
            message.to_string(),
            line,
            place.to_string(),
        ));
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ErrorReport {
    Message(String),
    MessageLine(String, u32),
    MessageLinePlace(String, u32, String),
}
