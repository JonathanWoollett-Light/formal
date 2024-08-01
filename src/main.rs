#![feature(let_chains)]

mod ast;
use ast::*;

mod verifier;
use verifier::*;

mod draw;

fn main() {
    println!("Hello, world!");
    let source = std::fs::read_to_string("./assets/two.s").unwrap();
    let chars = source.chars().collect::<Vec<_>>();

    // Parse the ast
    let ast = new_ast(&chars);

    // Print the ast
    let mut next_opt = ast;
    while let Some(next) = next_opt {
        let as_ref = unsafe { next.as_ref() };
        println!("{:?}", as_ref.this);
        next_opt = as_ref.next;
    }

    println!();

    // Verify the ast
    unsafe {
        verify(ast, 1..3);
    }
}
