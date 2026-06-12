use formal::*;

fn main() {
    let path = std::path::PathBuf::from("./assets/two.s");
    let source = std::fs::read_to_string(&path).unwrap();
    let chars = source.chars().collect::<Vec<_>>();

    // Parse
    let mut ast = new_ast(&chars, path);

    // Compress
    compress(&mut ast);

    // Print
    print!("{}", print_ast(ast));

    // The verifier is not yet wired into the binary; it is currently exercised
    // through the integration tests (see `tests/`). Run `cargo test`.
    todo!();
}
