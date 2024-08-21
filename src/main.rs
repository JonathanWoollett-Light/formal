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
                // TODO Stuff more of this functionality into a destructor or something so the semantics are more iterator-like and nice.
                ExplorePathResult::Invalid { initial_types } => {
                    // Since there is an indefinite number of types we can never reduce the types.
                    // E.g. you might think if we have excluded `[a:u8,b:u8]` and `[a:u8,b:u16]` (etc.
                    // with b being all integer types) we can exclude `[a:u8]` but this doesn't work
                    // since lists can be indefinitely long and there might be a valid combination `[a:u8, b:[u8,u8]]`.
                    explorerer.excluded.insert(initial_types.clone());

                    // Dealloc the current tree so we can restart.
                    for mut root in explorerer.roots.iter().copied() {
                        let stack = &mut root.as_mut().next;
                        while let Some(next) = stack.pop() {
                            stack.extend(next.as_ref().next.iter());
                            dealloc(next.as_ptr().cast(), Layout::new::<VerifierNode>());
                        }
                    }

                    // TODO Make this explanation better and doublecheck if this is actually correct behaviour.
                    // This case only occurs when all types are excluded thus it continually breaks out
                    // of the exploration loop with empty `initial_types`. This case means there is no
                    // valid type combination and thus no valid path.
                    if initial_types.is_empty() {
                        break None;
                    }

                    explorerer.new_path()
                }
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
