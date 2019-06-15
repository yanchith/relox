use std::io::{self, Write};

mod lexer;

// TODO: get rid of the static mut
static mut HAD_ERROR: bool = false;

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
    let buffer = std::fs::read_to_string(&file_path).expect("Failed to read file");
    run(&buffer);
}

fn run_prompt() {
    let mut buffer = String::new();
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        let had_error = unsafe { HAD_ERROR };
        if had_error {
            break;
        }

        print!("> ");
        stdout.flush().unwrap();

        stdin
            .read_line(&mut buffer)
            .expect("Failed to read from console");

        run(&buffer);
        buffer.clear();
    }
}

fn run(script: &str) {
    let tokens = lexer::scan_tokens(script, Box::new(report));
    print!("Tokens: ");
    for token in &tokens {
        print!("{} ", token);
    }
    println!()
}

fn error(line: usize, message: &str) {
    report(line, "", message);
}

fn report(line: usize, place: &str, message: &str) {
    eprintln!("ERROR on line {} around {}: {}", line, place, message);
    unsafe {
        HAD_ERROR = true;
    }
}
