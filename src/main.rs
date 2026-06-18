//! The `formal` command-line tool.
//!
//! `formal new <name>` scaffolds a Rust project that compiles a Python-dialect
//! `main.hl` through the `formal` library: its `cargo run` *is* the build,
//! verifying the program and lowering it to runnable RISC-V in `build/`.

use std::fs;
use std::path::Path;
use std::process::Command;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    match args.get(1).map(String::as_str) {
        Some("new") => match args.get(2) {
            Some(name) => {
                if let Err(error) = new_project(name) {
                    eprintln!("formal new: {error}");
                    std::process::exit(1);
                }
            }
            None => {
                eprintln!("usage: formal new <name>");
                std::process::exit(1);
            }
        },
        Some("mpi-selftest") => {
            #[cfg(feature = "hpc")]
            {
                formal::dist::mpi_selftest();
            }
            #[cfg(not(feature = "hpc"))]
            {
                eprintln!(
                    "mpi-selftest needs the `hpc` feature and a system MPI library; build with \
                     `cargo build --features hpc` and run under `mpirun` (see build.rs / deploy/)."
                );
                std::process::exit(1);
            }
        }
        _ => {
            eprintln!(
                "formal: a verifying compiler for a Python-like RISC-V dialect.\n\n\
                 usage:\n  \
                 formal new <name>      scaffold a project whose `cargo run` verifies and\n                         \
                 compiles its `main.hl` to RISC-V in `build/`\n  \
                 formal mpi-selftest    (--features hpc) run a distributed verification under MPI"
            );
            std::process::exit(1);
        }
    }
}

/// Scaffolds a new `formal` project: `cargo new` plus the `formal` dependency,
/// a starter `main.hl`, and the build-script `src/main.rs`.
fn new_project(name: &str) -> std::io::Result<()> {
    let status = Command::new("cargo")
        .args(["new", "--bin", name])
        .status()?;
    if !status.success() {
        return Err(std::io::Error::other("`cargo new` failed"));
    }
    let dir = Path::new(name);

    // Depend on the `formal` library (from GitHub, not crates.io). `cargo new`
    // ends the manifest with an empty `[dependencies]`, so appending adds to it.
    let manifest = dir.join("Cargo.toml");
    let mut toml = fs::read_to_string(&manifest)?;
    toml.push_str("formal = { git = \"https://github.com/JonathanWoollett-Light/formal\" }\n");
    fs::write(&manifest, toml)?;

    // The Python-dialect program, the build script, and a `build/` ignore.
    fs::write(dir.join("main.hl"), MAIN_HL)?;
    fs::write(dir.join("src").join("main.rs"), MAIN_RS)?;
    let ignore = dir.join(".gitignore");
    let mut gitignore = fs::read_to_string(&ignore).unwrap_or_default();
    gitignore.push_str("/build\n");
    fs::write(&ignore, gitignore)?;

    println!("created `{name}`. Next:\n  cd {name}\n  cargo run   # verify + compile main.hl into build/");
    Ok(())
}

/// The starter program: "Hello World!" in the Python dialect.
const MAIN_HL: &str = "\
# Hello World, verified and compiled by `formal`.
#
# Edit this file, then `cargo run` to verify it and lower it to RISC-V in
# `build/`. `print` and `exit` come from the formal standard library (which the
# compiler prepends), so this is the whole program.
print(\"Hello World!\\n\")
exit(0)
";

/// The generated project's `src/main.rs`: the build script. `cargo run`
/// verifies + lowers `main.hl` through the `formal` library, writes the
/// artifacts into `build/`, then assembles + links the runnable RISC-V into an
/// executable with the RISC-V GNU toolchain (downloaded once into `build/`).
const MAIN_RS: &str = r##"//! Build script for this `formal` project: `cargo run` verifies `main.hl` and
//! lowers it to runnable RISC-V, writing every artifact into `build/`.

use std::fs;
use std::process::Command;

fn main() {
    let source = fs::read_to_string("main.hl").unwrap_or_else(|error| {
        eprintln!("error: cannot read main.hl: {error}");
        std::process::exit(1);
    });

    // Translate (with the std prelude), parse, verify, optimize, and lower.
    let compiled = formal::compile(&source).unwrap_or_else(|error| {
        eprintln!("error: {error}");
        std::process::exit(1);
    });

    fs::create_dir_all("build").expect("create build/");
    // The combined Python dialect (std prelude + program), the RISC-V dialect,
    // and the runnable assembly.
    fs::write("build/main.hl", &compiled.combined).expect("write build/main.hl");
    fs::write("build/main.dialect.s", &compiled.dialect).expect("write build/main.dialect.s");
    fs::write("build/main.s", &compiled.assembly).expect("write build/main.s");
    println!("verified main.hl and lowered it to build/main.s");

    // Assemble + link into an executable with the RISC-V GNU toolchain.
    match build_executable() {
        Ok(()) => println!("assembled and linked -> build/main"),
        Err(error) => {
            eprintln!("note: wrote the assembly, but building the executable failed:\n{error}");
            std::process::exit(1);
        }
    }
}

/// Assembles and links `build/main.s` into the RISC-V executable `build/main`,
/// using the RISC-V GNU toolchain downloaded once into `build/toolchain`. The
/// later (toolchain) stages run through WSL when it is available, so this works
/// on Windows; everything is kept under `build/`.
fn build_executable() -> Result<(), String> {
    let script = r#"set -e
TC=build/toolchain
AS="$TC/bin/riscv64-unknown-elf-as"
if [ ! -x "$AS" ]; then
  echo "downloading the RISC-V GNU toolchain into build/toolchain (one time)..."
  api=https://api.github.com/repos/riscv-collab/riscv-gnu-toolchain/releases/latest
  url="$(curl -fsSL "$api" | grep -oE 'https://[^"]*riscv64-elf-ubuntu-24.04-gcc\.tar\.(gz|xz)' | head -1)"
  [ -n "$url" ] || url="$(curl -fsSL "$api" | grep -oE 'https://[^"]*riscv64-elf-ubuntu-[0-9.]+-gcc\.tar\.(gz|xz)' | head -1)"
  [ -n "$url" ] || { echo "could not find a RISC-V toolchain release asset"; exit 1; }
  mkdir -p "$TC"
  curl -fL "$url" -o build/toolchain.tar
  tar xf build/toolchain.tar -C "$TC" --strip-components=1
  rm -f build/toolchain.tar
fi
LD="$TC/bin/riscv64-unknown-elf-ld"
"$AS" -o build/main.o build/main.s
"$LD" --no-relax -e _start -o build/main build/main.o
rm -f build/main.o
"#;
    run_shell(script)
}

/// Runs a bash script for the toolchain stages: through WSL when it is present
/// (so the Linux toolchain works on Windows), otherwise with `sh`.
fn run_shell(script: &str) -> Result<(), String> {
    let via_wsl = cfg!(windows)
        && Command::new("wsl")
            .args(["-e", "true"])
            .output()
            .map(|out| out.status.success())
            .unwrap_or(false);

    let status = if via_wsl {
        Command::new("wsl").args(["-e", "bash", "-lc", script]).status()
    } else {
        Command::new("sh").args(["-c", script]).status()
    }
    .map_err(|error| format!("could not start the build shell: {error}"))?;

    if status.success() {
        Ok(())
    } else {
        Err("the toolchain assemble/link step failed (see the output above)".to_string())
    }
}
"##;
