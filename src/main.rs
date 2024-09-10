use std::alloc::{alloc, Layout};
use std::ptr::NonNull;

mod ast;

use ast::*;

mod verifier;
use verifier::*;

mod draw;

use std::cell::RefCell;
use std::rc::Rc;

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

    // Verify the ast
    unsafe {
        // verify(ast, 1..3);

        // TODO Simplify this iteration.
        let explorerer = Rc::new(RefCell::new(Explorerer::new(ast, 1..3)));
        let mut path = Explorerer::new_path(explorerer.clone());
        let mut check = 0;
        let _final_state = loop {
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
                } => Explorerer::new_path(explorerer.clone()),
                ExplorePathResult::Valid {
                    configuration,
                    touched,
                } => break Some((configuration, touched)),
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

    // use opentelemetry::global;
    // use std::process;
    // use tracing_subscriber::fmt::format::FmtSpan;
    // use tracing_subscriber::util::SubscriberInitExt;

    use tracing::level_filters::LevelFilter;
    use tracing_subscriber::layer::SubscriberExt;

    // const LOKI_URL: &str = "http://localhost/3100";

    #[test]
    fn two() {
        let now = std::time::Instant::now();

        // Create file.
        let file = std::fs::OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open("foo.txt")
            .unwrap();

        // Create base subscriber.
        let registry = tracing_subscriber::fmt::Subscriber::builder()
            .with_max_level(LevelFilter::TRACE)
            .with_test_writer()
            .with_writer(file)
            .with_ansi(false)
            .without_time()
            .with_target(false)
            .with_level(false)
            .finish();

        // Create assertion layer.
        let asserter = tracing_assertions::Layer::default();
        // asserter.disable(); // TODO Remove this, only here for debugging.
        let subscriber = registry.with(asserter.clone());

        // // Create jeager OTEL
        // global::set_text_map_propagator(opentelemetry_jaeger::Propagator::new());
        // let tracer = opentelemetry_jaeger::new_pipeline()
        //     .with_service_name("mini-redis")
        //     .install_simple().unwrap();
        // let opentelemetry = tracing_opentelemetry::layer().with_tracer(tracer);
        // let subscriber = subscriber.with(opentelemetry);

        // // Create grafana loki layer.
        // let (loki, task) = tracing_loki::builder()
        //     .label("host", "mine")
        //     .unwrap()
        //     .extra_field("pid", format!("{}", process::id()))
        //     .unwrap()
        //     .build_url(Url::parse(LOKI_URL).unwrap())
        //     .unwrap();
        // // Start background task to deliver logs.
        // tokio::spawn(task);
        // let subscriber = subscriber.with(loki);

        // Add layers
        let guard = tracing::subscriber::set_default(subscriber);

        let path = std::path::PathBuf::from("./assets/two.s");
        let source = std::fs::read_to_string(&path).unwrap();
        let chars = source.chars().collect::<Vec<_>>();

        // Parse
        let mut ast = new_ast(&chars, path);

        // Compress
        compress(&mut ast);

        // // Print
        // print_ast(ast);
        use std::cell::RefCell;
        use std::rc::Rc;

        // Verify the ast
        unsafe {
            let explorerer = Rc::new(RefCell::new(Explorerer::new(ast, 1..3)));

            // Start new path.
            let mut path = Explorerer::new_path(explorerer.clone());

            // With each step we check the logs to ensure the state is as expected.

            // At the start of the program there are no found variables so no initial types for variables.
            let a = asserter.matches("configuration: ProgramConfiguration({})");
            // The initial state of the queue contains the 1st instruction for
            // the 1st hart for each number of running harts (in this case we
            // are checking program for systems with 1 hart and with 2 harts).
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:2:0\" }, { hart: 1/2, instruction: \"./assets/two.s:2:0\" }]");
            // The current instruction is the first instruction popped off the queue.
            let c = asserter.matches("current: { hart: 1/1, instruction: \"./assets/two.s:2:0\" }");
            // We start with no types explored so none excluded.
            let d = asserter.matches("excluded: {}");
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b & c & d).assert();

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:2:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            // Since we are storing a word in `value` it cannot be u8 as this would store outside of memory.
            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let c = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            // Iterate until excluding value as i8.
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I8)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let c = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            // Iterate until excluding value as u16.
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U16)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let c = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I16)})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let c = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)}), \
                ProgramConfiguration({\"value\": (Global, I16)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid {
                    complete: false,
                    ..
                }
            ));
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            // 454
            for _ in 0..300 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U32), \"welcome\": (Thread({0}), List([U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8]))})");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
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
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
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
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
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
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
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
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"./assets/two.s:6:0\" }, { hart: 1/1, instruction: \"./assets/two.s:9:0\" }]");
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
            (a & b & c).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..6 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
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
            (a & b & c).assert();

            // Iterate over all possibilities for `value: I8` on hart 0.
            // let mut types_iter = TYPE_LIST.iter().skip(1);
            // for _ in 0..7 {
            //     path = Explorerer::new_path(explorerer.clone());
            //     for _ in 0..6 {
            //         path = ExplorererPath::next_step(path).continued().unwrap();
            //     }

            //     let s = format!(
            //         "configuration: ProgramConfiguration({})",
            //         types_iter.next().unwrap()
            //     );
            //     let a = asserter.matches(s);
            //     let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
            //     assert!(matches!(
            //         ExplorererPath::next_step(path),
            //         ExplorePathResult::Invalid {
            //             complete: false,
            //             ..
            //         }
            //     ));
            //     a.assert();
            //     assert!(b);
            // }

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"./assets/two.s:6:0\" }, { hart: 1/1, instruction: \"./assets/two.s:9:0\" }]");
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
            (a & b & c).assert();

            for _ in 0..8 {
                path = Explorerer::new_path(explorerer.clone());
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
            path = Explorerer::new_path(explorerer.clone());
            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"./assets/two.s:6:0\" }, { hart: 1/1, instruction: \"./assets/two.s:9:0\" }]");
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
            (a & b & c).assert();

            for _ in 0..8 {
                path = Explorerer::new_path(explorerer.clone());
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
            path = Explorerer::new_path(explorerer.clone());
            for _ in 0..3 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches("queue: [{ hart: 2/2, instruction: \"./assets/two.s:6:0\" }, { hart: 1/1, instruction: \"./assets/two.s:9:0\" }]");
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
            (a & b & c).assert();

            // Now starting with U32, we have reached a type for `value` in hart 0 that will pass.
            // It will need to iterate up to U32 for `value` in hart 1.
            for _ in 0..4 {
                path = Explorerer::new_path(explorerer.clone());
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
            path = Explorerer::new_path(explorerer.clone());
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            // So now is the first time we get past `sw t1, (t0)` on both harts.
            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 1/1, instruction: \"addi t1, t1, 1\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a = asserter.matches("configuration: ProgramConfiguration({})");
            let b = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"addi t1, t1, 1\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            (a & b).assert();

            let a = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            a.assert();

            let a = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            a.assert();

            let a = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            a.assert();

            // See the queue has grown.
            let a = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            a.assert();

            let a = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"addi t1, t1, 1\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            a.assert();

            // And it grows again.
            let a = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/1, instruction: \"lw t1, (t0)\" }, \
                { hart: 2/2, instruction: \"addi t1, t1, 1\" }, \
                { hart: 2/2, instruction: \"lw t1, (t0)\" }, \
                { hart: 1/2, instruction: \"lw t1, (t0)\" }\
                ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            a.assert();

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
            a.assert();

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
            a.assert();

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
        }

        drop(guard);

        todo!();
    }
}
