mod six;

use crate::*;
use std::ptr::NonNull;

pub fn setup_test(
    asm: &str,
) -> (
    tracing::subscriber::DefaultGuard,
    Option<NonNull<AstNode>>,
    tracing_assertions::Layer,
) {
    use tracing_subscriber::layer::SubscriberExt;
    // Unforutnately `CARGO_TARGET_TMPDIR` isn't defined for unit tests.
    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let tmpdir = format!("{dir}/target/tmp");
    if !std::fs::exists(&tmpdir).unwrap() {
        std::fs::create_dir(&tmpdir).unwrap();
    }

    // Create file.
    let file = std::fs::OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open(format!("{tmpdir}/{asm}.txt"))
        .unwrap();

    // Create base subscriber.
    let registry = tracing_subscriber::fmt::Subscriber::builder()
        .with_max_level(tracing_subscriber::filter::LevelFilter::TRACE)
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

    (guard, ast, asserter)
}
