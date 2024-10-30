use std::fs::read_to_string;
use std::path::PathBuf;

use crate::verifier_types::*;
use crate::*;
use tracing::info;

#[test]
fn six() {
    let (guard, mut ast, asserter) = super::setup_test("six");

    let mut explorerer = unsafe { Explorerer::new(ast, 1..3) };
    let path = PathBuf::from("./assets/six.s");
    use crate::Instruction;
    use crate::Locality;

    // Find valid path.
    let ValidPathResult {
        configuration,
        touched,
        jumped,
    } = unsafe {
        // With each step we check the logs to ensure the state is as expected.

        // At the start of the program there are no found variables so no initial types for variables.
        let mut program_configuration = ProgramConfiguration::new();
        let config_is_empty = asserter.debug(&program_configuration);
        // We start with no types explored so none excluded.
        let empty_excluded = asserter.matches("excluded: {}");
        // There are no racy instructions when queueing up the next instructions.
        let is_not_racy = asserter.matches("racy: false");
        // The initial conditions.
        let base_assertions = &config_is_empty & &is_not_racy & &empty_excluded;

        // The initial state of the queue contains the 1st instruction for
        // the 1st hart for each number of running harts (in this case we
        // are checking program for systems with 1 hart and with 2 harts).
        // The 1st instruction processed is the 1st hart out of 1 harts looking at the `_start:`.
        let hart1of1 = asserter.matches("hart: 1/1");
        let current = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 16..23,
            },
            this: Instruction::Label(LabelInstruction {
                tag: "_start".into(),
            }),
        });
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        // Since we enque nodes to the back of the queue and pop from the front we perform a breadth
        // first search that will cover all harts (as in cover system with 1 hart then system with 2
        // harts) before advancing any.
        let hart1of2 = asserter.matches("hart: 1/2");
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 819..842,
            },
            this: Instruction::Define(Define {
                label: "value".into(),
                locality: Some(Locality::Global),
                cast: Some(Type::U32),
            }),
        });
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        // Following the define the configuration should be updated.
        program_configuration.insert("value".into(), 1, (Locality::Global, Type::U32));
        let config = asserter.debug(&program_configuration);
        let base_assertions = &config & &is_not_racy & &empty_excluded;

        let hart2of2 = asserter.matches("hart: 2/2");
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 844..860,
            },
            this: Instruction::La(La {
                register: Register::X5,
                label: "value".into(),
            }),
        });
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let is_racy = asserter.matches("racy: true");
        let base_assertions = &config & &is_racy & &empty_excluded;

        // This repition is a symptom of an infinite loop.
        let current = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 880..892,
            },
            this: Instruction::Li(Li {
                register: Register::X6,
                immediate: Immediate { value: 0 },
            }),
        });
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        // Since the system with 2 harts has 1 front at `li x6, 0` where the next hart is `sw` and
        // 1 front at `_start:` where the next hart is `#$ value global u32` it's not racy since it
        // can advance a hart without hitting evaluating a racy node
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        todo!();

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
