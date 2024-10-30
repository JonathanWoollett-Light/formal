use crate::verifier_types::*;
use crate::*;
use tracing::info;

#[test]
fn six() {
    let (guard, mut ast, asserter) = super::setup_test("six");

    let mut explorerer = unsafe { Explorerer::new(ast, 1..3) };

    // Find valid path.
    let ValidPathResult {
        configuration,
        touched,
        jumped,
    } = unsafe {
        // With each step we check the logs to ensure the state is as expected.

        // At the start of the program there are no found variables so no initial types for variables.
        let config_is_empty = asserter.matches("configuration: ProgramConfiguration({})");
        // The initial state of the queue contains the 1st instruction for
        // the 1st hart for each number of running harts (in this case we
        // are checking program for systems with 1 hart and with 2 harts).
        // The 1st instruction processed is the 1st hart out of 1 harts looking at the `_start:`.
        let current = asserter.matches("current: { hart: 1/1, instruction: \"./assets/six.s:2:0\" }");
        // We start with no types explored so none excluded.
        let empty_excluded = asserter.matches("excluded: {}");
        // There are no racy instructions when queueing up the next instructions.
        let is_not_racy = asserter.matches("racy: false");
        // The initial conditions.
        let base_assertions = &(&config_is_empty & &is_not_racy) & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        current.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 1/2, instruction: \"./assets/six.s:2:0\" }, \
            { hart: 1/1, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:17:0\" }, \
            { hart: 2/2, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let u8_config =
            asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U8)})");
        let base_assertions = &u8_config & &empty_excluded.repeat() & is_not_racy.repeat();
        let queue = asserter.matches(
            "queue: [\
            { hart: 2/2, instruction: \"./assets/six.s:17:0\" }, \
            { hart: 1/1, instruction: \"./assets/six.s:18:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:18:0\" }, \
            { hart: 2/2, instruction: \"./assets/six.s:18:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 2/2, instruction: \"./assets/six.s:18:0\" }, \
            { hart: 1/1, instruction: \"./assets/six.s:21:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let is_racy = asserter.matches("racy: true");
        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:21:0\" }, \
            { hart: 2/2, instruction: \"./assets/six.s:21:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        u8_config.assert().reset();
        empty_excluded.assert().reset();
        is_racy.assert().reset();
        queue.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 2/2, instruction: \"./assets/six.s:21:0\" }, \
            { hart: 1/1, instruction: \"./assets/six.s:22:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        // Since we are storing a word in `value` it cannot be u8 as this would store outside of memory.
        u8_config.reset();
        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:22:0\" }, \
            { hart: 1/2, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        let u8_excluded = asserter.matches(
            "excluded: {\
            ProgramConfiguration({\"value\": (Global, U8)})\
        }",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        u8_config.assert();
        queue.assert();
        u8_excluded.assert().reset();

        // Iterate until excluding value as i8.
        for _ in 0..8 {
            explorerer = explorerer.next_step().continued().unwrap();
        }

        let i8_config =
            asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I8)})");
        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:22:0\" }, \
            { hart: 1/2, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        let excluded = asserter.matches(
            "excluded: {\
            ProgramConfiguration({\"value\": (Global, U8)}), \
            ProgramConfiguration({\"value\": (Global, I8)})\
        }",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        (i8_config & queue & excluded).assert();

        // Iterate until excluding value as u16.
        for _ in 0..8 {
            explorerer = explorerer.next_step().continued().unwrap();
        }

        let u16_config =
            asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U16)})");
        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:22:0\" }, \
            { hart: 1/2, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        let excluded = asserter.matches(
            "excluded: {\
            ProgramConfiguration({\"value\": (Global, U8)}), \
            ProgramConfiguration({\"value\": (Global, I8)}), \
            ProgramConfiguration({\"value\": (Global, U16)})\
        }",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        (u16_config & queue & excluded).assert();

        for _ in 0..8 {
            explorerer = explorerer.next_step().continued().unwrap();
        }

        let i32_config =
            asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, I16)})");
        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:22:0\" }, \
            { hart: 1/2, instruction: \"./assets/six.s:17:0\" }\
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
        explorerer = explorerer.next_step().continued().unwrap();
        (i32_config & queue & excluded).assert();

        // The valid path is now entered with `value` as `u32`.

        let queue = asserter.matches("queue: [{ hart: 1/1, instruction: \"./assets/six.s:2:0\" }, { hart: 1/2, instruction: \"./assets/six.s:2:0\" }]");
        let excluded = asserter.matches(
            "excluded: {\
            ProgramConfiguration({\"value\": (Global, U8)}), \
            ProgramConfiguration({\"value\": (Global, I8)}), \
            ProgramConfiguration({\"value\": (Global, U16)}), \
            ProgramConfiguration({\"value\": (Global, I16)})\
        }",
        );
        let base_assertions = (&config_is_empty.repeat() & &excluded) & is_not_racy.repeat();
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 1/2, instruction: \"./assets/six.s:2:0\" }, \
            { hart: 1/1, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        let queue = asserter.matches(
            "queue: [\
            { hart: 1/1, instruction: \"./assets/six.s:17:0\" }, \
            { hart: 2/2, instruction: \"./assets/six.s:17:0\" }\
        ]",
        );
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        queue.assert();

        for _ in 0..54 {
            explorerer = explorerer.next_step().continued().unwrap();
        }
        explorerer.next_step().valid().unwrap()
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
            #$ value global u32\n\
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
            #$ value global u32\n\
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
