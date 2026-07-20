//! Support for the language-comparison metrics pipeline: the Prometheus-format
//! metrics file ([`Metrics`]: parse/render), the site's number formatting, and
//! the injection of the numbers into `index.html`'s generated data block.
//!
//! Shared between the `comparisons` test (tests/comparisons/main.rs), which
//! measures and re-baselines the file, and `examples/update_website.rs`, which
//! re-injects an existing file into the page (both include this module by
//! path). Everything here is pure string/data transformation - deterministic,
//! so a re-render of unchanged data is byte-identical (the file and the page
//! are committed, and CI diffs them).
#![allow(dead_code)]

use std::collections::BTreeMap;

/// The metrics, in presentation order, as `(prometheus name, JS field)`. The JS
/// field is the key the page's `METRICS` object uses for the value.
pub const METRICS: [(&str, &str); 6] = [
    ("formal_comparison_compile_seconds", "compile"),
    ("formal_comparison_static_instructions", "count"),
    ("formal_comparison_binary_bytes", "bytes"),
    ("formal_comparison_executed_instructions", "exec"),
    ("formal_comparison_peak_memory_kib", "mem"),
    ("formal_comparison_run_seconds", "time"),
];

/// The environment-description metric: its labels record the controlled
/// conditions the measured samples were taken under.
pub const ENVIRONMENT_METRIC: &str = "formal_comparison_environment_info";

/// Programs and languages, in the page's presentation order.
pub const PROGRAMS: [&str; 2] = ["hello", "fannkuch"];
pub const LANGUAGES: [&str; 6] = ["formal", "rust", "c", "cpp", "zig", "ada"];

/// Where a sample came from.
///
/// `Legacy` marks values inherited from the pre-pipeline experiments (the
/// numbers the page used to hardcode): they keep the page complete until a
/// machine with the language's pinned toolchain re-measures them, and the
/// check run only warns (never fails) when a fresh measurement disagrees with
/// them. `Measured` values were produced by this pipeline under the
/// environment recorded in the file, and the check run holds them exact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    Measured,
    Legacy,
}

impl Origin {
    pub fn label(self) -> &'static str {
        match self {
            Origin::Measured => "measured",
            Origin::Legacy => "legacy",
        }
    }

    pub fn from_label(s: &str) -> Option<Self> {
        match s {
            "measured" => Some(Origin::Measured),
            "legacy" => Some(Origin::Legacy),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Sample {
    pub value: f64,
    pub origin: Origin,
}

/// A sample's identity: `(metric name, program, language)`.
pub type Key = (String, String, String);

/// The parsed metrics file: the comparison samples plus the environment labels.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Metrics {
    pub samples: BTreeMap<Key, Sample>,
    pub environment: BTreeMap<String, String>,
}

impl Metrics {
    pub fn get(&self, metric: &str, program: &str, language: &str) -> Option<Sample> {
        self.samples
            .get(&(
                metric.to_string(),
                program.to_string(),
                language.to_string(),
            ))
            .copied()
    }

    pub fn set(&mut self, metric: &str, program: &str, language: &str, sample: Sample) {
        self.samples.insert(
            (
                metric.to_string(),
                program.to_string(),
                language.to_string(),
            ),
            sample,
        );
    }

    /// Parses the Prometheus text format this module renders. Unknown lines
    /// (comments, HELP/TYPE) are skipped; unknown metrics are ignored, so the
    /// parse is total on any file [`Metrics::render`] wrote.
    pub fn parse(text: &str) -> Metrics {
        let mut out = Metrics::default();
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let Some((name, rest)) = line.split_once('{') else {
                continue;
            };
            let Some((labels, value)) = rest.rsplit_once('}') else {
                continue;
            };
            let labels = parse_labels(labels);
            let value = value.trim();
            if name == ENVIRONMENT_METRIC {
                out.environment = labels;
                continue;
            }
            if !METRICS.iter().any(|(metric, _)| *metric == name) {
                continue;
            }
            let (Some(program), Some(language)) = (labels.get("program"), labels.get("language"))
            else {
                continue;
            };
            let origin = labels
                .get("origin")
                .and_then(|o| Origin::from_label(o))
                .unwrap_or(Origin::Measured);
            let Ok(value) = value.parse::<f64>() else {
                continue;
            };
            out.samples.insert(
                (name.to_string(), program.clone(), language.clone()),
                Sample { value, origin },
            );
        }
        out
    }

    /// Renders the file: a fixed header, the environment info metric, then each
    /// metric's samples in `PROGRAMS` x `LANGUAGES` presentation order. The
    /// output is deterministic, so re-rendering unchanged data is a no-op diff.
    pub fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(
            "# Language-comparison metrics backing the index.html comparison panels.\n\
             # GENERATED, like Cargo.lock: committed, but written by the test suite, not\n\
             # by hand. `BLESS=1 cargo nextest run --run-ignored all comparisons`\n\
             # re-measures every language whose pinned toolchain is installed and\n\
             # rewrites this file plus the page (FORMAL_COMPARISONS_FULL=1 adds the\n\
             # heavy fannkuch-redux runtime runs); the normal run re-measures and\n\
             # asserts this file still matches (see tests/comparisons/main.rs for the\n\
             # per-metric comparison policy). origin=\"legacy\" marks values inherited\n\
             # from the pre-pipeline experiment (a different environment than recorded\n\
             # below); the first BLESS run with the language's toolchain replaces them.\n",
        );
        out.push_str(&format!(
            "# HELP {ENVIRONMENT_METRIC} The controlled environment the measured samples were taken under (in the labels; the value is always 1).\n\
             # TYPE {ENVIRONMENT_METRIC} gauge\n"
        ));
        let environment = self
            .environment
            .iter()
            .map(|(k, v)| format!("{k}=\"{}\"", escape_label(v)))
            .collect::<Vec<_>>()
            .join(",");
        out.push_str(&format!("{ENVIRONMENT_METRIC}{{{environment}}} 1\n"));
        for (metric, _) in METRICS {
            let help = match metric {
                "formal_comparison_compile_seconds" => {
                    "Wall-clock seconds to compile the program with the language's pinned toolchain (cold output directory, warm toolchain caches)."
                }
                "formal_comparison_static_instructions" => {
                    "Machine instructions in the compiled program (formal: lines of emitted assembly; others: riscv64-unknown-elf-objdump of the stripped static binary; Ada: host objdump)."
                }
                "formal_comparison_binary_bytes" => {
                    "Size in bytes of the stripped static executable."
                }
                "formal_comparison_executed_instructions" => {
                    "Guest instructions executed under user-mode qemu-riscv64, counted by the formal_stats TCG plugin."
                }
                "formal_comparison_peak_memory_kib" => {
                    "Peak guest memory working set in KiB (distinct 4 KiB pages touched: instruction fetches + data), from the formal_stats TCG plugin."
                }
                "formal_comparison_run_seconds" => {
                    "Wall-clock seconds of the uninstrumented (plugin-free) run under user-mode qemu-riscv64."
                }
                _ => "",
            };
            out.push_str(&format!("# HELP {metric} {help}\n# TYPE {metric} gauge\n"));
            for program in PROGRAMS {
                for language in LANGUAGES {
                    let Some(sample) = self.get(metric, program, language) else {
                        continue;
                    };
                    let value = if metric.ends_with("_seconds") {
                        format!("{:.3}", sample.value)
                    } else {
                        format!("{}", sample.value.round() as u64)
                    };
                    out.push_str(&format!(
                        "{metric}{{program=\"{program}\",language=\"{language}\",origin=\"{}\"}} {value}\n",
                        sample.origin.label()
                    ));
                }
            }
        }
        out
    }

    /// True if any sample still carries the legacy origin.
    pub fn any_legacy(&self) -> bool {
        self.samples.values().any(|s| s.origin == Origin::Legacy)
    }
}

fn escape_label(v: &str) -> String {
    v.replace('\\', "\\\\").replace('"', "\\\"")
}

fn parse_labels(s: &str) -> BTreeMap<String, String> {
    // label="value",label="value"; our values never contain escaped quotes
    // beyond the render-side escaping, which this walk undoes.
    let mut out = BTreeMap::new();
    let mut chars = s.chars().peekable();
    loop {
        let key: String = chars.by_ref().take_while(|&c| c != '=').collect();
        if key.is_empty() {
            break;
        }
        if chars.next() != Some('"') {
            break;
        }
        let mut value = String::new();
        let mut escaped = false;
        for c in chars.by_ref() {
            if escaped {
                value.push(c);
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                break;
            } else {
                value.push(c);
            }
        }
        out.insert(key.trim_start_matches(',').trim().to_string(), value);
        if chars.peek().is_none() {
            break;
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Presentation formatting (the strings the page shows).
// ---------------------------------------------------------------------------

/// Comma-grouped integer: `1234567` -> `"1,234,567"`.
pub fn fmt_group(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// Memory in KiB: `8` -> `"8 KiB"`.
pub fn fmt_mem(kib: u64) -> String {
    format!("{} KiB", fmt_group(kib))
}

/// Times: under a second in whole milliseconds (`"16 ms"`), under ten seconds
/// with one decimal (`"1.4 s"`), else whole seconds (`"36 s"`).
pub fn fmt_time(seconds: f64) -> String {
    if seconds < 0.9995 {
        format!("{} ms", (seconds * 1000.0).round() as u64)
    } else if seconds < 9.95 {
        format!("{:.1} s", seconds)
    } else {
        format!("{} s", seconds.round() as u64)
    }
}

/// The presentation string for one sample of `metric`.
pub fn fmt_metric(metric: &str, value: f64) -> String {
    match metric {
        "formal_comparison_compile_seconds" | "formal_comparison_run_seconds" => fmt_time(value),
        "formal_comparison_peak_memory_kib" => fmt_mem(value.round() as u64),
        _ => fmt_group(value.round() as u64),
    }
}

// ---------------------------------------------------------------------------
// index.html injection.
// ---------------------------------------------------------------------------

const BEGIN_MARKER: &str = "// COMPARISON-DATA-BEGIN";
const END_MARKER: &str = "// COMPARISON-DATA-END";

/// Renders the generated `METRICS` / tooltip-environment block for the page.
fn render_data_block(metrics: &Metrics) -> String {
    let mut out = String::new();
    let indent = "        ";
    out.push_str(&format!(
        "{indent}{BEGIN_MARKER} -- generated from tests/comparisons/metrics.prom\n\
         {indent}// by the comparisons test (BLESS mode) / `cargo run --example\n\
         {indent}// update_website`; do NOT edit by hand.\n"
    ));
    out.push_str(&format!("{indent}// prettier-ignore\n"));
    out.push_str(&format!("{indent}var METRICS = {{\n"));
    for program in PROGRAMS {
        out.push_str(&format!("{indent}  {program}: {{\n"));
        for language in LANGUAGES {
            let fields: Vec<String> = METRICS
                .iter()
                .filter_map(|(metric, field)| {
                    metrics
                        .get(metric, program, language)
                        .map(|s| format!("{field}: \"{}\"", fmt_metric(metric, s.value)))
                })
                .collect();
            if fields.is_empty() {
                continue;
            }
            out.push_str(&format!(
                "{indent}    {language}: {{ {} }},\n",
                fields.join(", ")
            ));
        }
        out.push_str(&format!("{indent}  }},\n"));
    }
    out.push_str(&format!("{indent}}};\n"));

    let get = |k: &str| metrics.environment.get(k).cloned().unwrap_or_default();
    let legacy_note = if metrics.any_legacy() {
        "\\nFigures marked origin=legacy in tests/comparisons/metrics.prom predate this environment."
    } else {
        ""
    };
    out.push_str(&format!("{indent}// prettier-ignore\n"));
    out.push_str(&format!(
        "{indent}var TIP_HOST =\n\
         {indent}  \"Host: {}\\n\" +\n\
         {indent}  \"OS: {}\\n\" +\n\
         {indent}  \"Measured as QEMU TCG (software-emulation) wall-clock, not native hardware.\";\n",
        escape_js(&get("host")),
        escape_js(&get("os")),
    ));
    out.push_str(&format!("{indent}// prettier-ignore\n"));
    out.push_str(&format!(
        "{indent}var TIP_USER = \"QEMU {} qemu-riscv64 (user-mode), -accel tcg{legacy_note}\";\n",
        escape_js(&get("qemu")),
    ));
    out.push_str(&format!("{indent}{END_MARKER}"));
    out
}

fn escape_js(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Splices the generated data block into `html` (between the BEGIN/END marker
/// lines) and syncs the static body defaults (the hello panels' numbers, shown
/// before the script runs / without JS). Returns the updated page.
pub fn update_html(html: &str, metrics: &Metrics) -> Result<String, String> {
    let begin = html
        .find(BEGIN_MARKER)
        .ok_or_else(|| format!("index.html: missing `{BEGIN_MARKER}` marker"))?;
    let line_start = html[..begin].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let end = html
        .find(END_MARKER)
        .ok_or_else(|| format!("index.html: missing `{END_MARKER}` marker"))?;
    if end < begin {
        return Err("index.html: comparison-data markers out of order".to_string());
    }
    let end = end + END_MARKER.len();
    let mut out = String::new();
    out.push_str(&html[..line_start]);
    out.push_str(&render_data_block(metrics));
    out.push_str(&html[end..]);

    // The body's default (no-JS) numbers: the hello panels for formal and the
    // default language tab (rust).
    for (id, metric, language) in [
        (
            "formal-compile",
            "formal_comparison_compile_seconds",
            "formal",
        ),
        (
            "formal-count",
            "formal_comparison_static_instructions",
            "formal",
        ),
        ("formal-bytes", "formal_comparison_binary_bytes", "formal"),
        (
            "formal-exec",
            "formal_comparison_executed_instructions",
            "formal",
        ),
        ("formal-mem", "formal_comparison_peak_memory_kib", "formal"),
        ("formal-time", "formal_comparison_run_seconds", "formal"),
        ("lang-compile", "formal_comparison_compile_seconds", "rust"),
        (
            "lang-count",
            "formal_comparison_static_instructions",
            "rust",
        ),
        ("lang-bytes", "formal_comparison_binary_bytes", "rust"),
        (
            "lang-exec",
            "formal_comparison_executed_instructions",
            "rust",
        ),
        ("lang-mem", "formal_comparison_peak_memory_kib", "rust"),
        ("lang-time", "formal_comparison_run_seconds", "rust"),
    ] {
        let Some(sample) = metrics.get(metric, "hello", language) else {
            continue;
        };
        out = set_element_text(&out, id, &fmt_metric(metric, sample.value))?;
    }
    Ok(out)
}

/// Replaces the text content of the (first) element with `id`: the text between
/// the tag's closing `>` and the next `<`. The formatted values never contain
/// `<`/`>`, so this simple splice is exact.
fn set_element_text(html: &str, id: &str, text: &str) -> Result<String, String> {
    let needle = format!("id=\"{id}\"");
    let at = html
        .find(&needle)
        .ok_or_else(|| format!("index.html: no element with id=\"{id}\""))?;
    let open = html[at..]
        .find('>')
        .map(|i| at + i + 1)
        .ok_or_else(|| format!("index.html: unterminated tag for id=\"{id}\""))?;
    let close = html[open..]
        .find('<')
        .map(|i| open + i)
        .ok_or_else(|| format!("index.html: no text node for id=\"{id}\""))?;
    Ok(format!("{}{}{}", &html[..open], text, &html[close..]))
}
