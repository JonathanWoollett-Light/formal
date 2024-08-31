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
                ExplorePathResult::Invalid { complete: true, .. } => break None,
                // The path was invalid but there may be another valid path.
                ExplorePathResult::Invalid {
                    complete: false, ..
                } => explorerer.new_path(),
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
    use std::io::Write;

    use crate::*;
    use draw::draw_tree;
    use tracing::{info, level_filters::LevelFilter};
    use tracing_subscriber::layer::SubscriberExt;
    #[test]
    fn two() {
        let now = std::time::Instant::now();
        let asserter = tracing_assertions::Layer::default();
        asserter.disable(); // TODO Remove this, only here for debugging.

        // let registry = tracing_subscriber::Registry::default();
        let file = std::fs::OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open("foo.txt")
            .unwrap();

        let registry = tracing_subscriber::fmt::Subscriber::builder()
            .with_max_level(LevelFilter::ERROR)
            .with_test_writer()
            .with_writer(file)
            .with_ansi(false)
            .finish();
        let subscriber = registry.with(asserter.clone());
        let guard = tracing::subscriber::set_default(subscriber);

        let source = std::fs::read_to_string("./assets/two.s").unwrap();
        let chars = source.chars().collect::<Vec<_>>();

        // Parse
        let mut ast = new_ast(&chars);

        // Compress
        compress(&mut ast);

        // // Print
        // print_ast(ast);

        // Verify the ast
        unsafe {
            let mut explorerer = Explorerer::new(ast, 1..3);

            // Start new path.
            let mut path = explorerer.new_path();

            // With each step we check the logs to ensure the state is as expected.

            // At the start of the program there are no found variables so no initial types for variables.
            let a = asserter.matches("initial_types: {0: {}, 1: {}}");
            // The initial state of the queue contains the 1st instruction for
            // the 1st hart for each number of running harts (in this case we
            // are checking program for systems with 1 hart and with 2 harts).
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"_start:\" }, { hart: 1/2, instruction: \"_start:\" }]");
            // The current instruction is the first instruction popped off the queue.
            let c = asserter.matches("current: { hart: 1/1, instruction: \"_start:\" }");
            // We start with no types explored so none excluded.
            let d = asserter.matches("excluded: {}");
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b & c & d);

            let a = asserter.matches("initial_types: {0: {}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 1/2, instruction: \"_start:\" }, { hart: 1/1, instruction: \"la t0, value\" }]");
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"la t0, value\" }, { hart: 2/2, instruction: \"la t0, value\" }]");
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"la t0, value\" }, { hart: 1/1, instruction: \"li t1, 0\" }]");
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": U8}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"li t1, 0\" }, { hart: 2/2, instruction: \"li t1, 0\" }]");
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": U8}}");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"li t1, 0\" }, { hart: 1/1, instruction: \"sw t1, (t0)\" }]");
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": U8}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": I8}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": U16}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": I16}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": U32}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": I32}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": U64}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {\"value\": I64}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}, \
                {0: {\"value\": U8}, 1: {\"value\": I64}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U8}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"la t0, value\" }, { hart: 1/1, instruction: \"li t1, 0\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {}}, \
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}, \
                {0: {\"value\": U8}, 1: {\"value\": I64}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            path = explorerer.new_path();

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": I8}, 1: {\"value\": U8}}");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {}}, \
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}, \
                {0: {\"value\": U8}, 1: {\"value\": I64}}, \
                {0: {\"value\": I8}, 1: {\"value\": U8}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            // Iterate over all possibilities for `value: I8` on hart 0.
            let mut types_iter = TYPE_LIST.iter().skip(1);
            for _ in 0..7 {
                path = explorerer.new_path();
                for _ in 0..6 {
                    path = ExplorererPath::next_step(path).continued().unwrap();
                }

                let s = format!(
                    "initial_types: {{0: {{\"value\": I8}}, 1: {{\"value\": {:?}}}}}",
                    types_iter.next().unwrap()
                );
                let a = asserter.matches(s);
                let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"sw t1, (t0)\" }, { hart: 1/2, instruction: \"la t0, value\" }]");
                assert!(matches!(
                    ExplorererPath::next_step(path),
                    ExplorePathResult::Invalid {
                        complete: false,
                        ..
                    }
                ));
                assert!(a);
                assert!(b);
            }

            path = explorerer.new_path();

            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": I8}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"la t0, value\" }, { hart: 1/1, instruction: \"li t1, 0\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {}}, \
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}, \
                {0: {\"value\": U8}, 1: {\"value\": I64}}, \
                {0: {\"value\": I8}, 1: {}}, \
                {0: {\"value\": I8}, 1: {\"value\": U8}}, \
                {0: {\"value\": I8}, 1: {\"value\": I8}}, \
                {0: {\"value\": I8}, 1: {\"value\": U16}}, \
                {0: {\"value\": I8}, 1: {\"value\": I16}}, \
                {0: {\"value\": I8}, 1: {\"value\": U32}}, \
                {0: {\"value\": I8}, 1: {\"value\": I32}}, \
                {0: {\"value\": I8}, 1: {\"value\": U64}}, \
                {0: {\"value\": I8}, 1: {\"value\": I64}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            for _ in 0..8 {
                path = explorerer.new_path();
                for _ in 0..6 {
                    path = ExplorererPath::next_step(path).continued().unwrap();
                }
                assert!(matches!(
                    ExplorererPath::next_step(path),
                    ExplorePathResult::Invalid {
                        complete: false,
                        ..
                    }
                ));
            }
            path = explorerer.new_path();
            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("initial_types: {0: {\"value\": U16}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"la t0, value\" }, { hart: 1/1, instruction: \"li t1, 0\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {}}, \
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}, \
                {0: {\"value\": U8}, 1: {\"value\": I64}}, \
                {0: {\"value\": I8}, 1: {}}, \
                {0: {\"value\": I8}, 1: {\"value\": U8}}, \
                {0: {\"value\": I8}, 1: {\"value\": I8}}, \
                {0: {\"value\": I8}, 1: {\"value\": U16}}, \
                {0: {\"value\": I8}, 1: {\"value\": I16}}, \
                {0: {\"value\": I8}, 1: {\"value\": U32}}, \
                {0: {\"value\": I8}, 1: {\"value\": I32}}, \
                {0: {\"value\": I8}, 1: {\"value\": U64}}, \
                {0: {\"value\": I8}, 1: {\"value\": I64}}, \
                {0: {\"value\": U16}, 1: {}}, \
                {0: {\"value\": U16}, 1: {\"value\": U8}}, \
                {0: {\"value\": U16}, 1: {\"value\": I8}}, \
                {0: {\"value\": U16}, 1: {\"value\": U16}}, \
                {0: {\"value\": U16}, 1: {\"value\": I16}}, \
                {0: {\"value\": U16}, 1: {\"value\": U32}}, \
                {0: {\"value\": U16}, 1: {\"value\": I32}}, \
                {0: {\"value\": U16}, 1: {\"value\": U64}}, \
                {0: {\"value\": U16}, 1: {\"value\": I64}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            for _ in 0..8 {
                path = explorerer.new_path();
                for _ in 0..6 {
                    path = ExplorererPath::next_step(path).continued().unwrap();
                }
                assert!(matches!(
                    ExplorererPath::next_step(path),
                    ExplorePathResult::Invalid {
                        complete: false,
                        ..
                    }
                ));
            }
            path = explorerer.new_path();
            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            let a = asserter.matches("initial_types: {0: {\"value\": I16}, 1: {}}");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"la t0, value\" }, { hart: 1/1, instruction: \"li t1, 0\" }]");
            let c = asserter.matches(
                "excluded: {\
                {0: {\"value\": U8}, 1: {}}, \
                {0: {\"value\": U8}, 1: {\"value\": U8}}, \
                {0: {\"value\": U8}, 1: {\"value\": I8}}, \
                {0: {\"value\": U8}, 1: {\"value\": U16}}, \
                {0: {\"value\": U8}, 1: {\"value\": I16}}, \
                {0: {\"value\": U8}, 1: {\"value\": U32}}, \
                {0: {\"value\": U8}, 1: {\"value\": I32}}, \
                {0: {\"value\": U8}, 1: {\"value\": U64}}, \
                {0: {\"value\": U8}, 1: {\"value\": I64}}, \
                {0: {\"value\": I8}, 1: {}}, \
                {0: {\"value\": I8}, 1: {\"value\": U8}}, \
                {0: {\"value\": I8}, 1: {\"value\": I8}}, \
                {0: {\"value\": I8}, 1: {\"value\": U16}}, \
                {0: {\"value\": I8}, 1: {\"value\": I16}}, \
                {0: {\"value\": I8}, 1: {\"value\": U32}}, \
                {0: {\"value\": I8}, 1: {\"value\": I32}}, \
                {0: {\"value\": I8}, 1: {\"value\": U64}}, \
                {0: {\"value\": I8}, 1: {\"value\": I64}}, \
                {0: {\"value\": U16}, 1: {}}, \
                {0: {\"value\": U16}, 1: {\"value\": U8}}, \
                {0: {\"value\": U16}, 1: {\"value\": I8}}, \
                {0: {\"value\": U16}, 1: {\"value\": U16}}, \
                {0: {\"value\": U16}, 1: {\"value\": I16}}, \
                {0: {\"value\": U16}, 1: {\"value\": U32}}, \
                {0: {\"value\": U16}, 1: {\"value\": I32}}, \
                {0: {\"value\": U16}, 1: {\"value\": U64}}, \
                {0: {\"value\": U16}, 1: {\"value\": I64}}, \
                {0: {\"value\": I16}, 1: {}}, \
                {0: {\"value\": I16}, 1: {\"value\": U8}}, \
                {0: {\"value\": I16}, 1: {\"value\": I8}}, \
                {0: {\"value\": I16}, 1: {\"value\": U16}}, \
                {0: {\"value\": I16}, 1: {\"value\": I16}}, \
                {0: {\"value\": I16}, 1: {\"value\": U32}}, \
                {0: {\"value\": I16}, 1: {\"value\": I32}}, \
                {0: {\"value\": I16}, 1: {\"value\": U64}}, \
                {0: {\"value\": I16}, 1: {\"value\": I64}}\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            assert!(a & b & c);

            // Now starting with U32, we have reached a type for `value` in hart 0 that will pass.
            // It will need to iterate up to U32 for `value` in hart 1.
            for _ in 0..4 {
                path = explorerer.new_path();
                for _ in 0..11 {
                    path = ExplorererPath::next_step(path).continued().unwrap();
                }
                assert!(matches!(
                    ExplorererPath::next_step(path),
                    ExplorePathResult::Invalid {
                        complete: false,
                        ..
                    }
                ));
            }

            // Now we are on the u32 path for `value` in both harts.
            path = explorerer.new_path();
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            // So now is the first time we get past `sw t1, (t0)` on both harts.
            let a = asserter.matches("initial_types: {0: {\"value\": U32}, 1: {\"value\": U32}}");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"li t1, 0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {\"value\": U32}, 1: {\"value\": U32}}");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"li t1, 0\" }, \
                { hart: 1/1, instruction: \"addi t1, t1, 1\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches("initial_types: {0: {\"value\": U32}, 1: {\"value\": U32}}");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"addi t1, t1, 1\" }, \
                { hart: 2/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"sw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a & b);

            let a = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"sw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            let a = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"sw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"sw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            let a = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"sw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            // See the queue has grown.
            let a = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            let a = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"addi t1, t1, 1\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            // And it grows again.
            let a = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"sw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"addi t1, t1, 1\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }\
                ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            // And it grows again.
            let a = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"addi t1, t1, 1\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            let a = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"addi t1, t1, 1\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"addi t1, t1, 1\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            assert!(a);

            // TODO I think this is where the endless loop comes from, we get stuck on the racy instructions.
            let mut count = 0;
            let invalid = loop {
                if count % 10_000 == 0 {
                    print!(".");
                    std::io::stdout().flush().unwrap();
                }
                // // Prints the tree for 1 harts
                // if count % 3_000_000 == 0 {
                //     let root = path
                //         .explorerer
                //         .roots
                //         .iter()
                //         .find(|r| r.as_ref().harts == 1)
                //         .unwrap();
                //     let [hart_root] = root.as_ref().next.as_slice() else {
                //         panic!()
                //     };
                //     let check = draw_tree(*hart_root, 2, |n| {
                //         let r = n.as_ref();
                //         format!("{}", r.node.as_ref().this)
                //     });
                //     println!();
                //     println!("{check}");
                //     println!();
                // }
                path = match ExplorererPath::next_step(path) {
                    ExplorePathResult::Continue(p) => p,
                    invalid @ ExplorePathResult::Invalid { .. } => break invalid,
                    _ => todo!(),
                };
                count += 1;
            };
            let ExplorePathResult::Invalid {
                complete,
                path,
                explanation,
            } = invalid
            else {
                panic!()
            };

            println!("test time: {:?}", now.elapsed());

            println!("\n\n{complete}\n\n");
            println!("\n\n{path}\n\n");
            println!("\n\n{explanation}\n\n");

            todo!();
        }

        drop(guard);
    }
}
