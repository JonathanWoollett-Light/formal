#![feature(let_chains)]
#![feature(iter_intersperse)]
#![feature(generic_arg_infer)]

use std::alloc::dealloc;
use std::alloc::{alloc, Layout};
use std::ptr::NonNull;

mod ast;

use ast::*;

mod verifier;
use verifier::*;

mod draw;

fn main() {
    let source = std::fs::read_to_string("./assets/two.s").unwrap();
    let chars = source.chars().collect::<Vec<_>>();

    // Parse
    let mut ast = new_ast(&chars);

    // Compress
    compress(&mut ast);

    // Print
    print_ast(ast);

    // Verify the ast
    unsafe {
        // verify(ast, 1..3);
        let mut explorerer = Explorerer::new(ast, 1..3);
        let mut path = explorerer.new_path();
        let mut check = 0;
        let final_state = loop {
            check += 1;
            if check > 10000 {
                panic!();
            }
            path = match ExplorererPath::next_step(path) {
                ExplorePathResult::Continue(p) => p,

                // The path was invalid and there is no other valid path.
                ExplorePathResult::Invalid(true) => break None,
                // The path was invalid but there may be another valid path.
                ExplorePathResult::Invalid(false) => explorerer.new_path(),
                ExplorePathResult::Valid {
                    initial_types,
                    touched,
                } => break Some((initial_types, touched)),
            }
        };
    }
}

// Re-allocates AST node contiguously to be more cache efficient.
fn compress(root: &mut Option<NonNull<AstNode>>) {
    unsafe {
        // Counts
        let mut next_opt = *root;
        let mut stack = Vec::new();
        while let Some(next) = next_opt {
            let as_ref = next.as_ref();
            stack.push(next);
            next_opt = as_ref.next;
        }

        // Re-allocates
        let ptr = alloc(Layout::array::<AstNode>(stack.len()).unwrap()).cast::<AstNode>();
        let mut next = None;
        while let Some(prev) = stack.pop() {
            // Copy
            let mut dest = NonNull::new(ptr.add(stack.len())).unwrap();
            prev.copy_to_nonoverlapping(dest, 1);

            // Update
            dest.as_mut().next = next;
            if let Some(mut next_val) = next {
                next_val.as_mut().prev = Some(dest);
            }

            // Carry
            next = Some(dest);

            // Update root
            if stack.is_empty() {
                *root = Some(prev);
            }
        }
    }
}

// Prints the AST nodes.
fn print_ast(root: Option<NonNull<AstNode>>) {
    let now = std::time::Instant::now();
    let mut next_opt = root;
    while let Some(next) = next_opt {
        let as_ref = unsafe { next.as_ref() };
        println!("{}", as_ref.this);
        next_opt = as_ref.next;
    }
    println!();
    println!("{:?}", now.elapsed());
}
