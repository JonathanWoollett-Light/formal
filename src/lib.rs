use std::alloc::{alloc, Layout};
use std::ptr::NonNull;

pub mod ast;
pub use ast::*;

pub mod hl;

pub mod verifier;
pub use verifier::*;

pub mod verifier_types;

pub mod explore;
pub use explore::*;

/// The distributed (MPI) backend, compiled only with `--features hpc` (which
/// links a system MPI library via rsmpi). See [`dist`] / `build.rs`.
#[cfg(feature = "hpc")]
pub mod dist;

pub mod draw;

pub mod optimizer;
pub use optimizer::*;

pub mod codegen;
pub use codegen::*;

/// Re-allocates the AST nodes contiguously to be more cache efficient.
pub fn compress(root: &mut Option<NonNull<AstNode>>) {
    unsafe {
        // Counts
        let mut next_opt = *root;
        let mut stack = Vec::new();
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while let Some(next) = next_opt {
            debug_assert!(check.next().is_some());
            let as_ref = next.as_ref();
            stack.push(next);
            next_opt = as_ref.next;
        }

        // Re-allocates
        let ptr = alloc(Layout::array::<AstNode>(stack.len()).unwrap()).cast::<AstNode>();
        let mut next = None;
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while let Some(prev) = stack.pop() {
            debug_assert!(check.next().is_some());

            // Copy
            let mut dest = NonNull::new(ptr.add(stack.len())).unwrap();
            prev.copy_to_nonoverlapping(dest, 1);

            // Update
            dest.as_mut().next = next;
            if let Some(mut next_val) = next {
                next_val.as_mut().prev = Some(dest);
            }

            // Carry
            next = Some(dest);

            // Update root to the head of the freshly-relaid-out list (`dest`),
            // not the original head (`prev`); the latter left `*root` pointing at
            // the old, scattered nodes, so the contiguous block was built and
            // then leaked (the relayout never took effect).
            if stack.is_empty() {
                *root = Some(dest);
            }
        }
    }
}

/// The artifacts of compiling an `hl` (Python-dialect) program end to end.
pub struct Compiled {
    /// The program with the standard-library prelude prepended: the combined
    /// source the compiler actually sees ([`hl::prelude`] + the program).
    pub combined: String,
    /// The annotated RISC-V dialect ([`hl::translate`]'s output).
    pub dialect: String,
    /// The verified, optimized, runnable RISC-V assembly ([`emit_executable`]).
    pub assembly: String,
}

/// An error from [`compile`].
#[derive(Debug)]
pub enum CompileError {
    /// The Python-dialect source did not translate to the dialect.
    Translate(hl::TranslateError),
    /// The verifier rejected or could not handle the program.
    Verify(CompilerError),
    /// The program has no valid type configuration: a `#!` (`fail`) is reachable.
    Invalid,
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Translate(e) => write!(f, "translation failed: {e}"),
            Self::Verify(e) => write!(f, "verification failed: {e}"),
            Self::Invalid => write!(
                f,
                "the program is invalid: a `fail` is reachable on some interleaving \
                 or type assignment"
            ),
        }
    }
}

impl std::error::Error for CompileError {}

/// Compiles an `hl` program end to end: translate (with the standard-library
/// prelude) to the dialect, parse, **verify**, optimize, and lower to runnable
/// RISC-V. Returns the combined source, the dialect, and the assembly.
///
/// The program is verified for a single hart with no memory-mapped regions, the
/// configuration a hosted program (one that reaches the outside world through
/// `ecall`, like the `print`/`exit` standard library) needs. Bare-metal
/// programs that declare `#@` regions or rely on multiple harts need the lower
/// level API ([`Explorerer`]) with the appropriate systems.
pub fn compile(source: &str) -> Result<Compiled, CompileError> {
    let dialect = hl::translate(source).map_err(CompileError::Translate)?;
    let combined = format!("{}\n{source}", hl::prelude());

    // `new_ast` records the source path in spans, which are re-read from disk
    // only to render an error; write the dialect to a temp file so any such
    // read resolves, then parse from its characters.
    let dialect_path =
        std::env::temp_dir().join(format!("formal-{}.dialect.s", std::process::id()));
    let _ = std::fs::write(&dialect_path, &dialect);
    let chars = dialect.chars().collect::<Vec<_>>();
    let mut ast = new_ast(&chars, dialect_path.clone());
    compress(&mut ast);

    let result = (|| unsafe {
        let systems = [InnerVerifierConfiguration {
            sections: Vec::new(),
            harts: 1,
        }];
        let mut explorerer = Explorerer::new(ast, &systems).map_err(CompileError::Verify)?;
        let valid = loop {
            match explorerer.next_step().map_err(CompileError::Verify)? {
                ExplorePathResult::Continue(next) => explorerer = next,
                ExplorePathResult::Valid(valid) => break valid,
                ExplorePathResult::Invalid => return Err(CompileError::Invalid),
            }
        };
        remove_untouched(&mut ast, &valid.touched);
        remove_branches(&mut ast, &valid.jumped);
        Ok(emit_executable(
            ast,
            &valid.configuration,
            &valid.accessed,
            &valid.transitions,
            &valid.uncompactable,
            &valid.pinned_nodes,
        ))
    })();
    let _ = std::fs::remove_file(&dialect_path);

    Ok(Compiled {
        combined,
        dialect,
        assembly: result?,
    })
}

/// Serializes the AST nodes back to their canonical textual form.
pub fn print_ast(root: Option<NonNull<AstNode>>) -> String {
    let mut next_opt = root;
    let mut string = String::new();
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let Some(next) = next_opt {
        debug_assert!(check.next().is_some());
        let as_ref = unsafe { next.as_ref() };
        string.push_str(&as_ref.as_ref().this.to_string());
        #[cfg(target_os = "windows")]
        string.push('\r');
        string.push('\n');
        next_opt = as_ref.next;
    }
    string
}
