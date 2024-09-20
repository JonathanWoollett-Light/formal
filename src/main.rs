use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

mod ast;

use ast::*;

mod verifier;
use verifier::*;

mod verifier_types;

mod draw;

mod optimizer;
use optimizer::*;

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
                ExplorePathResult::Invalid(InvalidPathResult { complete: true, .. }) => break None,
                // The path was invalid but there may be another valid path.
                ExplorePathResult::Invalid(InvalidPathResult {
                    complete: false, ..
                }) => Explorerer::new_path(explorerer.clone()),
                ExplorePathResult::Valid(ValidPathResult {
                    configuration,
                    touched,
                    jumped,
                }) => break Some((configuration, touched)),
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
fn print_ast(root: Option<NonNull<AstNode>>) -> String {
    let mut next_opt = root;
    let mut string = String::new();
    while let Some(next) = next_opt {
        let as_ref = unsafe { next.as_ref() };
        string.push_str(&format!("{}\n", as_ref.this));
        next_opt = as_ref.next;
    }
    string
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::*;

    // use opentelemetry::global;
    // use std::process;
    // use tracing_subscriber::fmt::format::FmtSpan;
    // use tracing_subscriber::util::SubscriberInitExt;

    use tracing::{level_filters::LevelFilter, subscriber::DefaultGuard};
    use tracing_subscriber::layer::SubscriberExt;
    use verifier_types::{LabelLocality, ProgramConfiguration};

    // const LOKI_URL: &str = "http://localhost/3100";
    
    use std::path::PathBuf;
    use std::sync::LazyLock;
    static LOCAL_TMP: LazyLock<PathBuf> = LazyLock::new(|| {
        const LOCAL_STR: &str = "./tmp";
        if std::fs::exists(LOCAL_STR).unwrap() {
            PathBuf::from(LOCAL_STR)
        }
        else {
            std::fs::create_dir(LOCAL_STR).unwrap();
            PathBuf::from(LOCAL_STR)
        }
    });

    fn setup_test(asm: &str) -> (DefaultGuard, Option<NonNull<AstNode>>, tracing_assertions::Layer){
        // Create file.
        let file = std::fs::OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(format!("{}/{asm}.txt",LOCAL_TMP.display()))
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

        let guard = tracing::subscriber::set_default(subscriber);

        let path = std::path::PathBuf::from(format!("./assets/{asm}.s"));
        let source = std::fs::read_to_string(&path).unwrap();
        let chars = source.chars().collect::<Vec<_>>();

        // Parse
        let mut ast = new_ast(&chars, path);

        compress(&mut ast);

        (guard,ast,asserter)
    }

    #[test]
    fn five() {
        let (guard, mut ast, asserter) = setup_test("five");

        let explorerer = Rc::new(RefCell::new(unsafe { Explorerer::new(ast, 1..3) }));

        // Find valid path.
        let ValidPathResult {
            configuration,
            touched,
            jumped,
        } = unsafe {
            let mut path = Explorerer::new_path(explorerer.clone());

            // With each step we check the logs to ensure the state is as expected.

            // At the start of the program there are no found variables so no initial types for variables.
            let config_is_empty = asserter.matches("configuration: ProgramConfiguration({})");
            // The initial state of the queue contains the 1st instruction for
            // the 1st hart for each number of running harts (in this case we
            // are checking program for systems with 1 hart and with 2 harts).
            let queue = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/five.s:2:0\" }, { hart: 1/2, instruction: \"./assets/five.s:2:0\" }]");
            // We start with no types explored so none excluded.
            let empty_excluded = asserter.matches("excluded: {}");
            // There are no racy instructions when queueing up the next instructions.
            let is_not_racy = asserter.matches("racy: false");
            // The initial conditions.
            let base_assertions = &(&config_is_empty & &is_not_racy) & &empty_excluded;
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/five.s:2:0\" }, \
                { hart: 1/1, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:17:0\" }, \
                { hart: 2/2, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let u8_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let base_assertions = &u8_config & &empty_excluded.repeat() & is_not_racy.repeat();
            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/five.s:17:0\" }, \
                { hart: 1/1, instruction: \"./assets/five.s:18:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:18:0\" }, \
                { hart: 2/2, instruction: \"./assets/five.s:18:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/five.s:18:0\" }, \
                { hart: 1/1, instruction: \"./assets/five.s:21:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let is_racy = asserter.matches("racy: true");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:21:0\" }, \
                { hart: 2/2, instruction: \"./assets/five.s:21:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            u8_config.assert().reset();
            empty_excluded.assert().reset();
            is_racy.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/five.s:21:0\" }, \
                { hart: 1/1, instruction: \"./assets/five.s:22:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            // Since we are storing a word in `value` it cannot be u8 as this would store outside of memory.
            u8_config.reset();
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:22:0\" }, \
                { hart: 1/2, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            let u8_excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult {
                    complete: false,
                    ..
                })
            ));
            u8_config.assert();
            queue.assert();
            u8_excluded.assert().reset();

            path = Explorerer::new_path(explorerer.clone());

            // Iterate until excluding value as i8.
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let i8_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I8)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:22:0\" }, \
                { hart: 1/2, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult {
                    complete: false,
                    ..
                })
            ));
            (i8_config & queue & excluded).assert();

            path = Explorerer::new_path(explorerer.clone());

            // Iterate until excluding value as u16.
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let u16_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U16)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:22:0\" }, \
                { hart: 1/2, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult{
                    complete: false,
                    ..
                })
            ));
            (u16_config & queue & excluded).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let i32_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I16)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:22:0\" }, \
                { hart: 1/2, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)}), \
                ProgramConfiguration({\"value\": (Global, I16)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult {
                    complete: false,
                    ..
                })
            ));
            (i32_config & queue & excluded).assert();

            // The valid path is now entered with `value` as `u32`.
            path = Explorerer::new_path(explorerer.clone());

            let queue = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/five.s:2:0\" }, { hart: 1/2, instruction: \"./assets/five.s:2:0\" }]");
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)}), \
                ProgramConfiguration({\"value\": (Global, I16)})\
            }",
            );
            let base_assertions = (&config_is_empty.repeat() & &excluded) & is_not_racy.repeat();
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/five.s:2:0\" }, \
                { hart: 1/1, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/five.s:17:0\" }, \
                { hart: 2/2, instruction: \"./assets/five.s:17:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            for _ in 0..54 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            ExplorererPath::next_step(path).valid().unwrap()
        };

        // Optimize based on path.
        assert_eq!(
            configuration,
            ProgramConfiguration(
                vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
                    .into_iter()
                    .collect()
            )
        );

        // Remove untouched nodes.
        unsafe {
            remove_untouched(&mut ast, &touched);
        }
        let expected = "\
                _start:\n\
                #$ value global _\n\
                la t0, value\n\
                li t1, 0\n\
                sw t1, (t0)\n\
                lw t1, (t0)\n\
                li t2, 0\n\
                bne t1, t2, _invalid\n\
            ";
        let actual = print_ast(ast);
        assert_eq!(actual, expected);

        // Remove branches that never jump.
        unsafe {
            remove_branches(&mut ast, &jumped);
        }
        let expected = "\
                _start:\n\
                #$ value global _\n\
                la t0, value\n\
                li t1, 0\n\
                sw t1, (t0)\n\
                lw t1, (t0)\n\
                li t2, 0\n\
            ";
        let actual = print_ast(ast);
        assert_eq!(actual, expected);

        drop(guard);
    }

    #[test]
    fn four() {
        let (guard, mut ast, asserter) = setup_test("four");

        let explorerer = Rc::new(RefCell::new(unsafe { Explorerer::new(ast, 1..3) }));

        let ValidPathResult {
            configuration,
            touched,
            jumped,
        } = unsafe {
            let mut path = Explorerer::new_path(explorerer.clone());
            let u32_config = asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U32)})");
            
            // Iterate until reaching `u32` for `value`.
            for _ in 0..4 {
                for _ in 0..8 {
                    path = ExplorererPath::next_step(path).continued().unwrap();
                }
                ExplorererPath::next_step(path).invalid().unwrap();
                path = Explorerer::new_path(explorerer.clone());
            }
            for _ in 0..4 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            u32_config.assert();

            for _ in 0..574 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            ExplorererPath::next_step(path).valid().unwrap()
        };

        // Optimize based on path.
        assert_eq!(
            configuration,
            ProgramConfiguration(
                vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
                    .into_iter()
                    .collect()
            )
        );

        // Remove untouched nodes.
        unsafe {
            remove_untouched(&mut ast, &touched);
        }
        let expected = "\
                _start:\n\
                #$ value global _\n\
                la t0, value\n\
                li t1, 0\n\
                sw t1, (t0)\n\
                lw t1, (t0)\n\
                addi t1, t1, 1\n\
                sw t1, (t0)\n\
                lw t1, (t0)\n\
                li t2, 4\n\
                bge t1, t2, _invalid\n\
            ";
        let actual = print_ast(ast);
        assert_eq!(actual, expected);

        // Remove branches that never jump.
        unsafe {
            remove_branches(&mut ast, &jumped);
        }
        let expected = "\
                _start:\n\
                #$ value global _\n\
                la t0, value\n\
                li t1, 0\n\
                sw t1, (t0)\n\
                lw t1, (t0)\n\
                addi t1, t1, 1\n\
                sw t1, (t0)\n\
                lw t1, (t0)\n\
                li t2, 4\n\
            ";
        let actual = print_ast(ast);
        assert_eq!(actual, expected);

        drop(guard);
    }

    #[test]
    fn three() {
        let (guard, mut ast, asserter) = setup_test("three");

        let explorerer = Rc::new(RefCell::new(unsafe { Explorerer::new(ast, 1..3) }));

        let ValidPathResult {
            configuration,
            touched,
            jumped,
        } = unsafe {
            let mut path = Explorerer::new_path(explorerer.clone());
            let u32_config = asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U32)})");
            
            // Iterate until reaching `u32` for `value`.
            for _ in 0..4 {
                for _ in 0..8 {
                    path = ExplorererPath::next_step(path).continued().unwrap();
                }
                ExplorererPath::next_step(path).invalid().unwrap();
                path = Explorerer::new_path(explorerer.clone());
            }
            for _ in 0..4 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            u32_config.assert();

            for _ in 0..6274 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }
            let res = ExplorererPath::next_step(path);
            println!("res: {res:?}");
            match res {
                ExplorePathResult::Invalid(InvalidPathResult { complete, path, explanation }) => {
                    println!("path:\n{path}");
                }
                _ => todo!()
            }
            todo!();
        };

        // Optimize based on path.
        assert_eq!(
            configuration,
            ProgramConfiguration(
                vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
                    .into_iter()
                    .collect()
            )
        );
    }

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
            let config_is_empty = asserter.matches("configuration: ProgramConfiguration({})");
            // The initial state of the queue contains the 1st instruction for
            // the 1st hart for each number of running harts (in this case we
            // are checking program for systems with 1 hart and with 2 harts).
            let queue = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:2:0\" }, { hart: 1/2, instruction: \"./assets/two.s:2:0\" }]");
            // We start with no types explored so none excluded.
            let empty_excluded = asserter.matches("excluded: {}");
            // There are no racy instructions when queueing up the next instructions.
            let is_not_racy = asserter.matches("racy: false");
            // The initial conditions.
            let base_assertions = &(&config_is_empty & &is_not_racy) & &empty_excluded;
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:2:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let u8_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
            let base_assertions = &u8_config & &empty_excluded.repeat() & is_not_racy.repeat();
            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let is_racy = asserter.matches("racy: true");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            u8_config.assert().reset();
            empty_excluded.assert().reset();
            is_racy.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            // Since we are storing a word in `value` it cannot be u8 as this would store outside of memory.
            u8_config.reset();
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let u8_excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult {
                    complete: false,
                    ..
                })
            ));
            u8_config.assert();
            queue.assert();
            u8_excluded.assert().reset();

            path = Explorerer::new_path(explorerer.clone());

            // Iterate until excluding value as i8.
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let i8_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I8)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult{
                    complete: false,
                    ..
                })
            ));
            (i8_config & queue & excluded).assert();

            path = Explorerer::new_path(explorerer.clone());

            // Iterate until excluding value as u16.
            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let u16_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U16)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult {
                    complete: false,
                    ..
                })
            ));
            (u16_config & queue & excluded).assert();

            path = Explorerer::new_path(explorerer.clone());

            for _ in 0..8 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            let i32_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I16)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)}), \
                ProgramConfiguration({\"value\": (Global, I16)})\
            }",
            );
            assert!(matches!(
                ExplorererPath::next_step(path),
                ExplorePathResult::Invalid(InvalidPathResult{
                    complete: false,
                    ..
                })
            ));
            (i32_config & queue & excluded).assert();

            // The valid path is now entered with `value` as `u32`.
            path = Explorerer::new_path(explorerer.clone());

            let queue = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:2:0\" }, { hart: 1/2, instruction: \"./assets/two.s:2:0\" }]");
            let excluded = asserter.matches(
                "excluded: {\
                ProgramConfiguration({\"value\": (Global, U8)}), \
                ProgramConfiguration({\"value\": (Global, I8)}), \
                ProgramConfiguration({\"value\": (Global, U16)}), \
                ProgramConfiguration({\"value\": (Global, I16)})\
            }",
            );
            let base_assertions = (&config_is_empty.repeat() & &excluded) & is_not_racy.repeat();
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:2:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let u32_config =
                asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U32)})");
            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            let base_assertions = &u32_config & &excluded & is_not_racy;
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            config_is_empty.assert().reset();
            excluded.assert().reset();
            is_racy.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let racy_assertions = &u32_config & &excluded & is_racy;
            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            racy_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:5:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:13:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:13:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:6:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:6:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:14:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            base_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:14:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:9:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            racy_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/2, instruction: \"./assets/two.s:9:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:15:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            racy_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 1/1, instruction: \"./assets/two.s:15:0\" }, \
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            racy_assertions.assert().reset();
            queue.assert();

            let queue = asserter.matches(
                "queue: [\
                { hart: 2/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/2, instruction: \"./assets/two.s:10:0\" }, \
                { hart: 1/1, instruction: \"./assets/two.s:20:0\" }\
            ]",
            );
            path = ExplorererPath::next_step(path).continued().unwrap();
            racy_assertions.assert().reset();
            queue.assert();

            // 454
            for _ in 0..16000 {
                path = ExplorererPath::next_step(path).continued().unwrap();
            }

            // let a = asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U32), \"welcome\": (Thread({0}), List([U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8, U8]))})");
            // let b = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/two.s:10:0\" }, { hart: 1/2, instruction: \"./assets/two.s:6:0\" }]");
            // let c = asserter.matches(
            //     "excluded: {\
            //     {0: {\"value\": U8}, 1: {\"value\": U8}}, \
            //     {0: {\"value\": U8}, 1: {\"value\": I8}}, \
            //     {0: {\"value\": U8}, 1: {\"value\": U16}}, \
            //     {0: {\"value\": U8}, 1: {\"value\": I16}}, \
            //     {0: {\"value\": U8}, 1: {\"value\": U32}}\
            // }",
            // );
            // assert!(matches!(
            //     ExplorererPath::next_step(path),
            //     ExplorePathResult::Invalid {
            //         complete: false,
            //         ..
            //     }
            // ));
            // (a & b & c).assert();

            // path = Explorerer::new_path(explorerer.clone());

            // // TODO I think this is where the endless loop comes from, we get stuck on the racy instructions.
            // let mut count = 0;
            // let invalid = loop {
            //     if count % 10_000 == 0 {
            //         print!(".");
            //         std::io::stdout().flush().unwrap();
            //     }
            //     // // Prints the tree for 1 harts
            //     // if count % 3_000_000 == 0 {
            //     //     let root = path
            //     //         .explorerer
            //     //         .roots
            //     //         .iter()
            //     //         .find(|r| r.as_ref().harts == 1)
            //     //         .unwrap();
            //     //     let [hart_root] = root.as_ref().next.as_slice() else {
            //     //         panic!()
            //     //     };
            //     //     let check = draw_tree(*hart_root, 2, |n| {
            //     //         let r = n.as_ref();
            //     //         format!("{}", r.node.as_ref().this)
            //     //     });
            //     //     println!();
            //     //     println!("{check}");
            //     //     println!();
            //     // }
            //     path = match ExplorererPath::next_step(path) {
            //         ExplorePathResult::Continue(p) => p,
            //         invalid @ ExplorePathResult::Invalid { .. } => break invalid,
            //         _ => todo!(),
            //     };
            //     count += 1;
            // };
            // let ExplorePathResult::Invalid {
            //     complete,
            //     path,
            //     explanation,
            // } = invalid
            // else {
            //     panic!()
            // };

            println!("test time: {:?}", now.elapsed());

            // println!("\n\n{complete}\n\n");
            // println!("\n\n{path}\n\n");
            // println!("\n\n{explanation}\n\n");
        }

        drop(guard);

        todo!();
    }
}
