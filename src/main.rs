use std::io::{self, Write};

use crate::interpreter::Interpreter;
use crate::reporter::Reporter;

mod ast;
mod callable;
mod env;
mod interpreter;
mod lexer;
mod parser;
mod reporter;
mod resolver;
mod token;
mod value;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args_len = args.len();
    if args_len > 1 {
        eprintln!("Usage: relox [script]");
        std::process::exit(64);
    } else if args_len == 1 {
        run_file(args[0].clone());
    } else {
        run_prompt();
    }
}

fn run_file(file_path: String) {
    let mut interpreter = Interpreter::new();
    let mut reporter = Reporter::new();
    let buffer = std::fs::read_to_string(&file_path).expect("Failed to read file");
    run(&mut interpreter, &mut reporter, &buffer);

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
    let mut interpreter = Interpreter::new();
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

        run(&mut interpreter, &mut reporter, &buffer);
        buffer.clear();
    }
}

fn run(interpreter: &mut Interpreter, reporter: &mut Reporter, script: &str) {
    let tokens = lexer::lex(reporter, script);
    if reporter.has_compile_error() {
        return;
    }

    if let Some(program) = parser::parse(reporter, &tokens) {
        if reporter.has_compile_error() {
            return;
        }
        println!("{}", program);

        resolver::resolve(reporter, interpreter, program.stmts());
        if reporter.has_compile_error() {
            return;
        }

        interpreter.interpret(reporter, &program);
    }
}
