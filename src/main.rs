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

        // TODO Simplify this iteration.
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

#[cfg(test)]
mod tests {
    use super::*;
    use draw::draw_tree;
    use tracing_test::traced_test;

    #[test]
    #[traced_test]
    fn two() {
        let source = std::fs::read_to_string("./assets/two.s").unwrap();
        let chars = source.chars().collect::<Vec<_>>();

        // Parse
        let mut ast = new_ast(&chars);

        // Compress
        compress(&mut ast);

        // Print
        print_ast(ast);

        let width_spacing = 2;
        let closure = |x: NonNull<VerifierNode>| unsafe {
            let y = x.as_ref();
            format!("({}| {})", y.hart, y.node.as_ref().this.to_string())
        };
        let seperator = (0..1)
            .map(|_| format!("{}\n", "-".repeat(20)))
            .collect::<String>();

        // Checks that there exists a log containing `prefix` and that the
        // most recent instance of this ends with `suffix`.
        macro_rules! log_assertion {
            ($prefix:expr, $suffix: expr) => {{
                logs_assert(|lines: &[&str]| {
                    let found = lines.iter().rev()
                        .find(|line|line.contains($prefix))
                        .ok_or(format!("Could not find log contains {:?}", $prefix));
                    match found {
                        Ok(line) => match line.ends_with($suffix)   {
                            true => Ok(()),
                            false => Err(format!("Most recent instance of a log containing {:?} ({:?}) does not end with {:?}.", $prefix, line, $suffix))
                        },
                        Err(err) => Err(err),
                    }
                });
            }};
        }

        // Verify the ast
        unsafe {
            let mut explorerer = Explorerer::new(ast, 1..3);
            let path = explorerer.new_path();

            // The next step continues, exploring:
            let path = ExplorererPath::next_step(path).continued().unwrap();
            log_assertion!("initial_types:", "{0: {}, 1: {}}");
            log_assertion!("branch_ptr node:", "_start:"); // the 1st instruction
            log_assertion!("hart:", "0"); // for the 1st hart
            log_assertion!("harts:", "1"); // when 1 harts are running

            // The next step continues, exploring:
            let path = ExplorererPath::next_step(path).continued().unwrap();
            log_assertion!("initial_types:", "{0: {}, 1: {}}");
            log_assertion!("branch_ptr node:", "_start:"); // the 1st instruction
            log_assertion!("hart:", "0"); // for the 1st hart
            log_assertion!("harts:", "2"); // when 2 harts are running

            // The next step continues, exploring:
            let path = ExplorererPath::next_step(path).continued().unwrap();
            log_assertion!("initial_types:", "{0: {}, 1: {}}");
            log_assertion!("branch_ptr node:", "la t0, value"); // the 2nd instruction
            log_assertion!("hart:", "0"); // for the 1st hart
            log_assertion!("harts:", "1"); // when 1 harts are running.

            // The next step continues, exploring:
            let path = ExplorererPath::next_step(path).continued().unwrap();
            log_assertion!("initial_types:", "{0: {\"value\": U8}, 1: {}}");
            log_assertion!("branch_ptr node:", "la t0, value"); // the 2nd instruction
            log_assertion!("hart:", "0"); // for the 1st hart
            log_assertion!("harts:", "2"); // when 2 harts are running.

            // The next step continues, exploring:
            let path = ExplorererPath::next_step(path).continued().unwrap();
            log_assertion!("initial_types:", "{0: {\"value\": U8}, 1: {}}");
            log_assertion!("branch_ptr node:", "li t1, 0"); // the 3rd instruction
            log_assertion!("hart:", "0"); // for the 1st hart
            log_assertion!("harts:", "1"); // when 1 harts are running.

            // The next step continues, exploring:
            let path = ExplorererPath::next_step(path).continued().unwrap();
            log_assertion!("initial_types:", "{0: {\"value\": U8}, 1: {}}");
            log_assertion!("branch_ptr node:", "li t1, 0"); // the 3rd instruction
            log_assertion!("hart:", "0"); // for the 1st hart
            log_assertion!("harts:", "2"); // when 2 harts are running.

            // The next step encounter an invalid instruction for the initial type assumptions.
            // i.e. you cannot store a word (4 bytes) in a u8 (1 byte).
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(false)
            ));
            log_assertion!("initial_types:", "{0: {\"value\": U8}, 1: {}}");
            log_assertion!("branch_ptr node:", "sw t1, (t0)"); // the 3rd instruction
            log_assertion!("hart:", "0"); // for the 1st hart

            let path = explorerer.new_path();

            todo!();
        }
    }
}
