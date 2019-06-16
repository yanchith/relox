use std::io::{self, Write};

use crate::reporter::Reporter;

mod lexer;
mod parser;
mod reporter;

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let arguments_len = arguments.len();
    if arguments_len > 1 {
        eprintln!("Usage: relox [script]");
        std::process::exit(64);
    } else if arguments_len == 1 {
        run_file(arguments[0].clone());
    } else {
        run_prompt();
    }
}

fn run_file(file_path: String) {
    let mut reporter = Reporter::new();
    let buffer = std::fs::read_to_string(&file_path).expect("Failed to read file");
    run(&mut reporter, &buffer);
}

fn run_prompt() {
    let mut reporter = Reporter::new();
    let mut buffer = String::new();
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        if reporter.has_error_reports() {
            reporter.print_error_reports();
            break;
        }

        print!("> ");
        stdout.flush().unwrap();

        stdin
            .read_line(&mut buffer)
            .expect("Failed to read from console");

        run(&mut reporter, &buffer);
        buffer.clear();
    }
}

fn run(reporter: &mut Reporter, script: &str) {
    let tokens = lexer::scan(reporter, script);
    print!("Tokens: ");
    for token in &tokens {
        print!("{} ", token);
    }
    println!();
    if let Some(ast) = parser::parse(reporter, &tokens) {
        println!("Ast: {}", ast);
    }
}

