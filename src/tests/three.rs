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

        for _ in 0..19000 {
            path = ExplorererPath::next_step(path).continued().unwrap();
        }
        let res = ExplorererPath::next_step(path);
        // println!("res: {res:?}");
        match res {
            ExplorePathResult::Invalid(InvalidPathResult {
                complete,
                path,
                explanation,
            }) => {
                println!("path:\n{path}");
            }
            _ => todo!(),
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
