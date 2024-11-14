use std::collections::BTreeMap;
use std::fs::read_to_string;
use std::path::PathBuf;

use crate::verifier_types::*;
use crate::*;
use tracing::info;

#[test]
fn six() {
    let (guard, mut ast, asserter) = super::setup_test("six");

    let mut explorerer = unsafe {
        Explorerer::new(
            ast,
            &[
                InnerVerifierConfiguration {
                    sections: Default::default(),
                    harts: 1,
                },
                InnerVerifierConfiguration {
                    sections: Default::default(),
                    harts: 2,
                },
            ],
        )
    };
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
        let mut program_configuration = TypeConfiguration::new();
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

        let define = asserter.debug(AstValue {
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
        let current = define.clone();
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

        let la = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 844..860,
            },
            this: Instruction::La(La {
                register: Register::X5,
                label: "value".into(),
            }),
        });
        let current = la.clone();
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // With only 1 hart on the system with 1 hart, when it encounters a racy instruction it has
        // no other option but to immedately evaluate it.
        let is_racy = asserter.matches("racy: true");
        let base_assertions = &config & &is_racy & &empty_excluded;

        // This repition is a symptom of an infinite loop.
        let li_t1 = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 880..892,
            },
            this: Instruction::Li(Li {
                register: Register::X6,
                immediate: Immediate {
                    radix: 10,
                    value: 0,
                },
            }),
        });
        let current = li_t1.clone();
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

        let sw = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 894..909,
            },
            this: Instruction::Sw(Sw {
                to: Register::X5,
                from: Register::X6,
                offset: Offset {
                    value: Immediate {
                        radix: 10,
                        value: 0,
                    },
                },
            }),
        });
        let current = sw.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        let current = define.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let lw = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 1051..1066,
            },
            this: Instruction::Lw(Lw {
                to: Register::X6,
                from: Register::X5,
                offset: Offset {
                    value: Immediate {
                        radix: 10,
                        value: 0,
                    },
                },
            }),
        });

        // 1/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        let current = la.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let li_t2 = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 1068..1080,
            },
            this: Instruction::Li(Li {
                register: Register::X7,
                immediate: Immediate {
                    radix: 10,
                    value: 0,
                },
            }),
        });
        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        // This is racy becuase both harts are at the `li t1, 0` instruction before the racy `sw`.
        let current = li_t1.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let bne = asserter.debug(AstValue {
            span: Span {
                path: path.clone(),
                span: 1082..1106,
            },
            this: Instruction::Bne(Bne {
                lhs: Register::X6,
                rhs: Register::X7,
                out: "_invalid".into(),
            }),
        });
        let current = bne.clone();
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of1.assert().reset();
        current.assert().reset();

        // At this point hart 2/2 is at `sw` and has `lw` next which is racy and hart 1/2 is at `li`
        // and has `sw` next which is also racy, so no harts can be advanced without evaluating racy
        // instructions thus its racy.
        let current = sw.clone();
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = sw.clone();
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        // 2/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // The thought might arise, that why would a system with 2 harts evaluate the same
        // instruction (in this case `sw`) more than 2 times? The answer is that since it needs to
        // evaluate race conditions it needs to evaluate all the orderings which will result in the
        // instruction being evaluated many times (in this specific case 4 times).
        //
        // Notably the following `lw` instruction will be evaluated 16 times since it needs to be
        // evaluated by each hart (2) times the possible orderings (2) times the current diverging
        // paths from previous orderings (4 from the 4 possible ordering of this `sw`) resulting in
        // 2 * 2 * 4 = 16.
        //
        // And if there where another racy instruction after the `lw` it would be evaluated 64 times
        // (2 * 2 * 16). This is one of the two major sources of the atrocious O'notation of the
        // compiler. Of course in reality the verifier path might diverge but the paths may not be
        // equally long so it's the worst case scenario.
        let current = sw.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = sw.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 3/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 4/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 5/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        // 6/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 7/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = sw.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = sw.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 8/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        // 9/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        // 10/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 11/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        // 12/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        // 13/16
        let current = lw.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = li_t2.clone();
        let base_assertions = &config & &is_not_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart1of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        let current = bne.clone();
        let base_assertions = &config & &is_racy & &empty_excluded;
        explorerer = explorerer.next_step().continued().unwrap();
        base_assertions.assert().reset();
        hart2of2.assert().reset();
        current.assert().reset();

        explorerer.next_step().valid().unwrap()
    };

    info!("configuration: {configuration:?}");
    info!("touched: {touched:?}");
    info!("jumped: {jumped:?}");

    // Optimize based on path.
    assert_eq!(
        configuration,
        TypeConfiguration(
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
