//! Translates a Python-like `hl` source file to the annotated RISC-V dialect:
//!
//! ```sh
//! cargo run --example translate -- tests/uart_hello/input.hl tests/uart_hello/dialect.s
//! ```
//!
//! With one argument the dialect is written to stdout.

fn main() {
    let mut args = std::env::args().skip(1);
    let input = args.next().expect("usage: translate <input.hl> [output.s]");
    let source = std::fs::read_to_string(&input).expect("failed to read the input");
    match formal::hl::translate(&source) {
        Ok(dialect) => match args.next() {
            Some(output) => std::fs::write(output, dialect).expect("failed to write the output"),
            None => print!("{dialect}"),
        },
        Err(error) => {
            eprintln!("{input}: {error}");
            std::process::exit(1);
        }
    }
}
