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
        let u32_config =
            asserter.matches("configuration: ProgramConfiguration({\"value\": (Global, U32)})");

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
