//! Re-injects the committed language-comparison metrics
//! (tests/comparisons/metrics.prom) into index.html's generated data block:
//!
//! ```sh
//! cargo run --example update_website
//! ```
//!
//! The metrics file itself is written by the `comparisons` test (see
//! tests/comparisons/main.rs); this example only re-renders the page from it,
//! for when index.html was edited (or a metrics change was merged) and the
//! generated block needs refreshing without re-measuring anything. The
//! `comparisons` test's check mode asserts the page and the file agree.

#[path = "../tests/comparisons/support.rs"]
mod support;

fn main() {
    let manifest = env!("CARGO_MANIFEST_DIR");
    let metrics_path = format!("{manifest}/tests/comparisons/metrics.prom");
    let html_path = format!("{manifest}/index.html");
    let metrics = support::Metrics::parse(
        &std::fs::read_to_string(&metrics_path)
            .expect("failed to read tests/comparisons/metrics.prom"),
    );
    let html = std::fs::read_to_string(&html_path).expect("failed to read index.html");
    match support::update_html(&html, &metrics) {
        Ok(updated) => {
            if updated == html {
                println!("index.html is already in sync with tests/comparisons/metrics.prom");
            } else {
                std::fs::write(&html_path, updated).expect("failed to write index.html");
                println!("index.html updated from tests/comparisons/metrics.prom");
            }
        }
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
