use std::alloc::{alloc, Layout};
use std::ptr::NonNull;

pub mod ast;
pub use ast::*;

pub mod verifier;
pub use verifier::*;

pub mod verifier_types;

pub mod draw;

pub mod optimizer;
pub use optimizer::*;

pub mod codegen;
pub use codegen::*;

/// Re-allocates the AST nodes contiguously to be more cache efficient.
pub fn compress(root: &mut Option<NonNull<AstNode>>) {
    unsafe {
        // Counts
        let mut next_opt = *root;
        let mut stack = Vec::new();
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while let Some(next) = next_opt {
            debug_assert!(check.next().is_some());
            let as_ref = next.as_ref();
            stack.push(next);
            next_opt = as_ref.next;
        }

        // Re-allocates
        let ptr = alloc(Layout::array::<AstNode>(stack.len()).unwrap()).cast::<AstNode>();
        let mut next = None;
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while let Some(prev) = stack.pop() {
            debug_assert!(check.next().is_some());

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

/// Serializes the AST nodes back to their canonical textual form.
pub fn print_ast(root: Option<NonNull<AstNode>>) -> String {
    let mut next_opt = root;
    let mut string = String::new();
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let Some(next) = next_opt {
        debug_assert!(check.next().is_some());
        let as_ref = unsafe { next.as_ref() };
        string.push_str(&as_ref.as_ref().this.to_string());
        #[cfg(target_os = "windows")]
        string.push('\r');
        string.push('\n');
        next_opt = as_ref.next;
    }
    string
}
