//! Runs an `hl` program through the whole pipeline (`formal::compile`) and
//! prints the dialect + runnable assembly, plus a rough instruction count.
//! A scratch driver for developing `hl` programs (e.g. the fannkuch test).

use std::fs;

fn main() {
    let path = match std::env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: cargo run --example compile -- <file.hl>");
            std::process::exit(2);
        }
    };
    let source = fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(2);
    });
    match formal::compile(&source) {
        Ok(c) => {
            println!("=== DIALECT ===\n{}", c.dialect);
            println!("=== ASSEMBLY ===\n{}", c.assembly);
            let instructions = c
                .assembly
                .lines()
                .filter(|l| {
                    l.starts_with("    ")
                        && l.trim()
                            .chars()
                            .next()
                            .is_some_and(|ch| ch.is_ascii_lowercase())
                })
                .count();
            eprintln!("instructions ~ {instructions}");
        }
        Err(e) => {
            eprintln!("COMPILE ERROR: {e}");
            std::process::exit(1);
        }
    }
}
