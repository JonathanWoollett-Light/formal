use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

mod ast;

use ast::*;

mod verifier;
pub use verifier::*;

pub mod verifier_types;

pub mod draw;

mod optimizer;
pub use optimizer::*;

fn main() {
    let path = std::path::PathBuf::from("./assets/two.s");
    let source = std::fs::read_to_string(&path).unwrap();
    let chars = source.chars().collect::<Vec<_>>();

    // Parse
    let mut ast = new_ast(&chars, path);

    // Compress
    compress(&mut ast);

    // Print
    print_ast(ast);

    todo!();

    // // Verify the ast
    // unsafe {
    //     // verify(ast, 1..3);

    //     // TODO Simplify this iteration.
    //     let explorerer = Rc::new(RefCell::new(Explorerer::new(ast, 1..3)));
    //     let mut path = Explorerer::new_path(explorerer.clone());
    //     let mut check = 0;
    //     let _final_state = loop {
    //         check += 1;
    //         if check > 10000 {
    //             panic!();
    //         }
    //         path = match ExplorererPath::next_step(path) {
    //             ExplorePathResult::Continue(p) => p,
    //             // The path was invalid and there is no other valid path.
    //             ExplorePathResult::Invalid(InvalidPathResult { complete: true, .. }) => break None,
    //             // The path was invalid but there may be another valid path.
    //             ExplorePathResult::Invalid(InvalidPathResult {
    //                 complete: false, ..
    //             }) => Explorerer::new_path(explorerer.clone()),
    //             ExplorePathResult::Valid(ValidPathResult {
    //                 configuration,
    //                 touched,
    //                 jumped,
    //             }) => break Some((configuration, touched)),
    //         }
    //     };
    // }
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
fn print_ast(root: Option<NonNull<AstNode>>) -> String {
    let mut next_opt = root;
    let mut string = String::new();
    while let Some(next) = next_opt {
        let as_ref = unsafe { next.as_ref() };
        string.push_str(&as_ref.as_ref().this.to_string());
        #[cfg(target_os = "windows")]
        string.push('\r');
        string.push('\n');
        next_opt = as_ref.next;
    }
    string
}

#[cfg(test)]
mod tests;
