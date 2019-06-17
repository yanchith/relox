use std::io::{self, Write};

use crate::reporter::Reporter;

mod interpreter;
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

    let exit_status = if reporter.has_compile_error() {
        Some(65)
    } else if reporter.has_runtime_error() {
        Some(70)
    } else {
        None
    };

    if let Some(status) = exit_status {
        reporter.print_all_errors();
        std::process::exit(status)
    }
}

fn run_prompt() {
    let mut reporter = Reporter::new();
    let mut buffer = String::new();
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        if reporter.has_compile_error() || reporter.has_runtime_error() {
            reporter.print_all_errors();
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
        if let Some(value) = interpreter::interpret(reporter, &ast) {
            println!("Value: {}", value);
        }
    }
}
