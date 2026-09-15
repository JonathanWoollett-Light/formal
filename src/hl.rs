//! The high-level front-end: a Python-like dialect (working name `hl`; the
//! language itself is not yet named) that translates to the annotated RISC-V
//! dialect the verifier consumes.
//!
//! The translation is deliberately trivial: every simple statement lowers to
//! exactly one dialect line, and the three structured statements (`if`,
//! `while`, `require`) each lower to a fixed pattern of branches and
//! generated labels (`_l0`, `_l1`, ...), the way C maps near one-to-one onto
//! assembly. There is no register allocation, no implicit control flow beyond
//! those patterns, and no code synthesis; the value of the layer is purely
//! syntactic:
//!
//! ```text
//! value: global _              ->  #$ value global _
//! welcome: [u8*13]             ->  #$ welcome thread [u8 u8 ... u8]  (elided = default)
//! t0 = &value                  ->  la t0, value
//! t0 = type(welcome)           ->  #& t0, welcome
//! t0 = csr(mhartid)            ->  csrr t0, mhartid
//! t1 = 0x10000000              ->  li t1, 0x10000000
//! t1 = t1 + 1                  ->  addi t1, t1, 1
//! t0[0] = t1                   ->  #] t1, 0(t0)
//! t1 = t0[2]                   ->  #[ t1, 2(t0)
//! t0[0:4] = t1                 ->  sw t1, 0(t0)
//! t1 = t0[8:16]                ->  ld t1, 8(t0)
//! section 0x100 0x200 rw       ->  #@ 0x100 0x200 rw
//! fail                         ->  #!
//! unreachable                  ->  #?
//! require t1 < t2              ->      blt t1, t2, _l0
//!                                      #!
//!                                  _l0:
//! if t0 == 0:                  ->      bnez t0, _l1
//!     <body>                           <body>
//!                                  _l1:
//! while t5 != t2:              ->  _l2:
//!     <body>                           beq t5, t2, _l3
//!                                      <body>
//!                                      j _l2
//!                                  _l3:
//! asm:                         ->  (each indented line emitted verbatim)
//!     wfi
//! ```
//!
//! A `def` takes one thing. Several values travel as a tuple of tokens,
//! `f([a0, a1])` against `def f([a, b]: [i64, i64]):`, which is a two-entry
//! substitution map and materialises nothing. Several `def`s of one name are
//! overloads, resolved here by arity and by each argument's category (a
//! register or integer is a scalar, a variable name or string an array); two
//! that could both fit some call are refused where the second is defined.
//!
//! A `def` is inlined, so `return <value>` is not a jump: it is the assignment
//! to whatever the call site asked for. `def double(x): return x + x` called
//! as `a1 = double(a0)` is the single line `add a1, a0, a0`. It is therefore
//! confined to the body's tail, since skipping the rest of a body would need a
//! jump to a label the source never wrote; a compile-time `if typeof` arm is
//! exempt, because it is spliced with no branch.
//!
//! Control flow is structured only: `if` and `while` take an indented block,
//! and `require <cond>` is `if not <cond>: fail` in one line. The surface
//! language has no `goto` and no labels; the labels in the dialect output are
//! generated (`asm:` remains the escape hatch for anything else). A condition
//! is `<reg> <op> <reg>` with `<`/`<=`/`>`/`>=`/`==`/`!=` (`>` and `<=` swap
//! the operands onto `blt`/`bge`), or `<reg> ==|!= 0` (`beqz`/`bnez`).
//!
//! `#` starts a comment exactly as in Python; comments and blank lines do not
//! appear in the output.
//!
//! Indexing is **element-based**: `t0[k]` is element `k` of whatever `t0`
//! points at, so the width comes from the pointee's type rather than the call
//! site. The front-end is stateless and does not track what a register points
//! at, so it lowers the access to the `#[` / `#]` directives and the verifier
//! (the only part that knows every pointer's pointee type, per state and per
//! type configuration) resolves each one to a byte offset and a width, checks
//! the index is in bounds, and hands codegen the sized load/store. A *runtime*
//! index is not supported yet: compute the address (`t = i * <element size>`,
//! `p = base + t`) and index that with `p[0]`.
//!
//! `reg[a:b]` is the raw byte slice, for memory that has no element type of
//! its own: a memory-mapped address, a `#@` region, or a variable whose type
//! the verifier is still inferring (there the access width is what drives the
//! inference). It lowers directly, the width visible at the call site:
//! 1 = `lb`/`sb`, 2 = `lh`/`sh`, 4 = `lw`/`sw`, 8 = `ld`.

use std::collections::HashMap;
use std::fmt;

/// The standard-library prelude, prepended to every program by [`translate`].
/// It is written in this same dialect and contains only `def`s (e.g. `print`),
/// which emit no code until called, so prepending it to a program that uses
/// nothing from it leaves the lowering byte-for-byte unchanged.
const STD: &str = include_str!("../std/std.hl");

/// The standard-library prelude that [`translate`] prepends to every program.
/// Exposed so a build tool can write out the combined source (prelude +
/// program), exactly what the compiler sees.
pub fn prelude() -> &'static str {
    STD
}

/// A translation failure: the offending (1-based) line and what went wrong.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranslateError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for TranslateError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

const SCALARS: [&str; 8] = ["u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64"];
const REGISTERS: [&str; 14] = [
    "t0", "t1", "t2", "t3", "t4", "t5", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
];
const LOCALITIES: [&str; 3] = ["global", "thread", "_"];
/// The locality a define gets when it does not name one. Thread-local is
/// the safe default (nothing is shared by accident) and the one the
/// verifier's own search tries first, so eliding the locality lands on what
/// an inferred one would almost always have picked, without paying for the
/// search. Write `_` to ask for the search instead.
const DEFAULT_LOCALITY: &str = "thread";
/// Call-shaped forms the assignment translator owns, which a `def` may not
/// shadow: `t0 = type(x)` and `t0 = csr(x)`.
const BUILTIN_CALLS: [&str; 2] = ["type", "csr"];

fn is_register(token: &str) -> bool {
    REGISTERS.contains(&token)
}

fn is_label(token: &str) -> bool {
    !token.is_empty()
        && token.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && token
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
}

/// Parses a decimal or `0x` hexadecimal integer literal (optionally negative),
/// returning its value. The literal's *text* is preserved in the output, so
/// the radix the programmer wrote survives translation.
fn parse_int(token: &str) -> Option<i64> {
    let (negative, body) = match token.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, token),
    };
    let value = match body.strip_prefix("0x") {
        Some(hex) => i64::from_str_radix(hex, 16).ok()?,
        None => body.parse::<i64>().ok()?,
    };
    Some(if negative { -value } else { value })
}

/// A non-empty source line after comment stripping: its 1-based number, its
/// indentation (leading spaces), and the trimmed statement text. Owns its text
/// so a captured `def` body can be re-emitted with the parameter substituted.
#[derive(Clone)]
struct Line {
    number: usize,
    indent: usize,
    text: String,
    /// From the prepended standard library, so an error can say so.
    std: bool,
}

/// What the stateless front-end can tell about a call argument: a register
/// or an integer literal is a scalar value; a label or a string literal names
/// storage. Nothing finer (a register's width is not knowable here), so this
/// is also all a type pattern can dispatch on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Scalar,
    Array,
}

/// One overload of an inline function. `def f([a, b]: [i32, i32]):` is a
/// tuple pattern of two names with two type patterns; `def f(x):` is a bare
/// pattern of one untyped name. A call is matched against every overload of
/// its name by arity, tuple-ness and each element's [`Kind`] (`None` matches
/// either), and exactly one must fit. The body is translated afresh at each
/// call with every pattern name substituted, so there is still no calling
/// convention, stack, or `ret`: several overloads are one function with a
/// compile-time arm per signature, the `if typeof` dispatch written as
/// headers.
#[derive(Clone)]
struct Overload {
    params: Vec<String>,
    tuple: bool,
    kinds: Vec<Option<Kind>>,
    body: Vec<Line>,
    /// The parameter text as written, for error messages.
    spec: String,
    /// Where it was defined: `line N`, or `std/std.hl line N`.
    origin: String,
}

impl Overload {
    /// The signature as the user wrote it.
    fn signature(&self, name: &str) -> String {
        format!("{name}({})", self.spec)
    }

    /// Whether some call could fit both overloads: same shape, same arity,
    /// and at every position the two kinds could be the same (an untyped or
    /// `_` position accepts either kind). Two overlapping overloads would make
    /// every such call ambiguous, so the second is refused where it is
    /// written, and a call then fits at most one.
    fn overlaps(&self, other: &Overload) -> bool {
        self.tuple == other.tuple
            && self.kinds.len() == other.kinds.len()
            && self
                .kinds
                .iter()
                .zip(&other.kinds)
                .all(|(a, b)| a.is_none() || b.is_none() || a == b)
    }
}

/// Translates `hl` source into the annotated RISC-V dialect. Pure text to
/// text; simple statements emit one output line each and `if`/`while`/
/// `require` emit their fixed branch + generated-label patterns. The output
/// uses the platform line ending (the dialect parser splits on `\r\n` on
/// Windows), instructions and directives indented four spaces and labels at
/// column zero, matching the canonical form `print_ast` emits.
pub fn translate(source: &str) -> Result<String, TranslateError> {
    // Prepend the standard library (see [`STD`]). Its `def`s emit nothing until
    // called, so a program that uses none of them lowers exactly as before.
    // User line numbers in errors stay 1-based by subtracting the prelude's
    // length (the prelude is correct, so its own lines should not surface).
    let std_lines = STD.lines().count();
    let combined = format!("{STD}\n{source}");

    let mut lines = Vec::new();
    for (index, raw) in combined.lines().enumerate() {
        // Strip the comment, keep the indentation for block structure.
        let uncommented = match raw.find('#') {
            Some(at) => &raw[..at],
            None => raw,
        };
        let line = uncommented.trim_end();
        let stripped = line.trim_start();
        if stripped.is_empty() {
            continue;
        }
        let number = if index < std_lines {
            index + 1
        } else {
            index - std_lines
        };
        lines.push(Line {
            number,
            indent: line.len() - stripped.len(),
            text: stripped.to_string(),
            std: index < std_lines,
        });
    }

    // A list initialiser may span lines, so a fixture can be laid out in the
    // shape of its data (`num_islands` writes its grid a row per line).
    // Nothing else in the language spans lines, so joining a statement whose
    // brackets are still open only ever affects an initialiser.
    let lines = join_open_brackets(lines);

    let mut translator = Translator {
        out: Vec::new(),
        labels: 0,
        strings: 0,
        locals: 0,
        functions: HashMap::new(),
        depth: 0,
        returns: Vec::new(),
        runtime_depth: 0,
    };
    if let Some(first) = lines.first() {
        let indent = first.indent;
        let mut position = 0;
        translator.block(&lines, &mut position, indent)?;
        if let Some(rest) = lines.get(position) {
            // Only reachable by out-denting below the first line's level.
            return Err(TranslateError {
                line: rest.number,
                message: "unindent below the program's first statement".to_string(),
            });
        }
    }

    let newline = if cfg!(target_os = "windows") {
        "\r\n"
    } else {
        "\n"
    };
    let mut text = translator.out.join(newline);
    text.push_str(newline);
    Ok(text)
}

/// One inlined call's return context. `def`s are inlined, so a `return`
/// is not a jump: it is an assignment to whatever the caller asked for, and
/// the stack is here only because inlining nests.
struct ReturnSlot {
    /// Where the caller wants the value, `None` for a bare statement call
    /// (whose returned value is simply dropped).
    destination: Option<String>,
    /// The runtime block depth at the call, so a `return` can tell "the tail
    /// of the body" from "inside an `if` or a `while`", which would need a
    /// jump the language does not have.
    entry_depth: usize,
    fired: bool,
}

struct Translator {
    out: Vec<String>,
    labels: usize,
    strings: usize,
    /// Counter for hygienic renaming of a `def` body's local definitions; kept
    /// separate from `labels` so freshening them does not perturb branch-label
    /// numbering (and thus the pinned translations of callers that take a
    /// different `if typeof` arm).
    locals: usize,
    functions: HashMap<String, Vec<Overload>>,
    /// Inlining depth, a guard against a `def` that calls itself.
    depth: usize,
    /// The call being inlined, innermost last. Empty outside a `def`.
    returns: Vec<ReturnSlot>,
    /// How many runtime `if`/`while` bodies enclose the statement being
    /// translated. A compile-time `if typeof` arm does not count: it is
    /// spliced with no branch, so its tail is still the body's tail.
    runtime_depth: usize,
}

impl Translator {
    /// Allocates the next generated label (`_l0`, `_l1`, ...).
    fn fresh_label(&mut self) -> String {
        let label = format!("_l{}", self.labels);
        self.labels += 1;
        label
    }

    /// Allocates the next generated string-storage label (`__str0`, ...).
    fn fresh_string(&mut self) -> String {
        let label = format!("__str{}", self.strings);
        self.strings += 1;
        label
    }

    /// Allocates the next hygienic label for a `def` body's local definition
    /// (`__local0`, ...). Separate from `fresh_label` (see `locals`).
    fn fresh_local(&mut self) -> String {
        let label = format!("__local{}", self.locals);
        self.locals += 1;
        label
    }

    /// Translates a run of statements sharing one indentation level, stopping
    /// (without consuming) at the first line indented less than the block.
    fn block(
        &mut self,
        lines: &[Line],
        position: &mut usize,
        indent: usize,
    ) -> Result<(), TranslateError> {
        while let Some(line) = lines.get(*position) {
            if line.indent < indent {
                return Ok(());
            }
            if line.indent > indent {
                return Err(TranslateError {
                    line: line.number,
                    message: "unexpected indentation (only `if`/`while`/`def`/`asm:` open a block)"
                        .to_string(),
                });
            }
            self.statement(lines, position)?;
        }
        Ok(())
    }

    /// Translates the indented block belonging to the `if:`/`while:` header
    /// at `header`; the block is the following run of deeper-indented lines.
    fn body(
        &mut self,
        lines: &[Line],
        position: &mut usize,
        header: &Line,
    ) -> Result<(), TranslateError> {
        match lines.get(*position) {
            Some(first) if first.indent > header.indent => {
                let indent = first.indent;
                self.block(lines, position, indent)
            }
            _ => Err(TranslateError {
                line: header.number,
                message: format!("expected an indented block after `{}`", header.text),
            }),
        }
    }

    /// Captures the indented block below `header` as raw (cloned) lines without
    /// translating them: a `def` body is translated later, at each call site.
    fn capture_body(
        &self,
        lines: &[Line],
        position: &mut usize,
        header: &Line,
    ) -> Result<Vec<Line>, TranslateError> {
        if !matches!(lines.get(*position), Some(l) if l.indent > header.indent) {
            return Err(TranslateError {
                line: header.number,
                message: "expected an indented block after the `def`".to_string(),
            });
        }
        let mut body = Vec::new();
        while let Some(l) = lines.get(*position) {
            if l.indent <= header.indent {
                break;
            }
            body.push(l.clone());
            *position += 1;
        }
        Ok(body)
    }

    /// Inlines a call `name(arg)`: binds the function's parameter to the
    /// argument, then translates the body afresh with the parameter token
    /// substituted. A **string** argument is laid down in fresh storage and the
    /// parameter is bound to its label (`&param` in the body becomes `&__strN`,
    /// as `print` uses it); an **integer** argument binds the parameter directly
    /// to the literal (`param` in the body becomes the value, as `exit` uses
    /// it). Generated labels stay unique because the body is translated through
    /// the same fresh-label counter as everything else.
    fn inline_call(
        &mut self,
        name: &str,
        arg: &str,
        number: usize,
        destination: Option<&str>,
    ) -> Result<(), TranslateError> {
        let err = |message: String| TranslateError {
            line: number,
            message,
        };
        self.depth += 1;
        if self.depth > 32 {
            return Err(err(
                "`def` inlining nested too deep (a recursive call?)".to_string()
            ));
        }
        // The argument is one element, or a tuple `[e1, e2, ...]` of them.
        let (elements, tuple) = match arg.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            Some(inner) => (split_top_level(inner, ','), true),
            None => (vec![arg], false),
        };
        if tuple && elements.len() < 2 {
            return Err(err(format!(
                "a tuple argument needs at least two elements; `{name}(e)` passes one"
            )));
        }
        // Laying a string down (`emit_string_storage`) writes t0 and t1, so
        // a tuple that also passes either register would bind a value the
        // string just overwrote.
        if elements.iter().any(|e| e.trim().starts_with('"'))
            && elements.iter().any(|e| matches!(e.trim(), "t0" | "t1"))
        {
            return Err(err(
                "a tuple argument may not mix a string literal with `t0` or `t1`: laying the string down clobbers them"
                    .to_string(),
            ));
        }
        // Each element binds to a token: a string literal is laid down in fresh
        // storage and binds to its label; an integer, a register or a label
        // binds as written. Its kind is what the overloads dispatch on.
        let mut bindings = Vec::with_capacity(elements.len());
        let mut kinds = Vec::with_capacity(elements.len());
        for element in &elements {
            let element = element.trim();
            if element.starts_with('"') {
                let bytes = parse_string_literal(element).map_err(err)?;
                let label = self.fresh_string();
                self.emit_string_storage(&label, &bytes);
                bindings.push(label);
                kinds.push(Kind::Array);
            } else if parse_int(element).is_some() || is_register(element) {
                bindings.push(element.to_string());
                kinds.push(Kind::Scalar);
            } else if is_reserved(element) {
                return Err(err(format!(
                    "`{element}` is a reserved word, not a variable"
                )));
            } else if is_label(element) {
                bindings.push(element.to_string());
                kinds.push(Kind::Array);
            } else {
                return Err(err(format!(
                    "a call argument must be a string, an integer, a register or a variable name, got `{element}`"
                )));
            }
        }

        let Some(overloads) = self.functions.get(name) else {
            return Err(err(format!("unknown function `{name}`")));
        };
        let fitting: Vec<&Overload> = overloads
            .iter()
            .filter(|o| {
                o.tuple == tuple
                    && o.kinds.len() == kinds.len()
                    && o.kinds
                        .iter()
                        .zip(&kinds)
                        .all(|(want, got)| want.is_none_or(|w| w == *got))
            })
            .collect();
        // Overlapping overloads are refused where they are defined, so at
        // most one fits here.
        debug_assert!(fitting.len() <= 1);
        let Some(func) = fitting.first().map(|o| (*o).clone()) else {
            let signatures: Vec<String> = overloads.iter().map(|o| o.signature(name)).collect();
            return Err(err(format!(
                "no overload of `{name}` takes `{arg}` ({}); defined: {}",
                describe_kinds(&kinds, tuple),
                signatures.join(", ")
            )));
        };
        // Hygiene: give each call's body-local definitions (`name: <locality> ...`)
        // a fresh label, so repeated calls do not collide on storage -- e.g.
        // `print`'s integer scratch buffer, which two `print(int)`s would otherwise
        // both define. Each fresh name is substituted through the body alongside the
        // parameter bindings.
        let mut subs: Vec<(String, String)> = func.params.iter().cloned().zip(bindings).collect();
        for decl in body_defines(&func.body) {
            let fresh = self.fresh_local();
            subs.push((decl.to_string(), fresh));
        }
        let inlined: Vec<Line> = func
            .body
            .iter()
            .map(|l| {
                let text = substitute_tokens(&l.text, &subs);
                Line {
                    number: l.number,
                    indent: l.indent,
                    text,
                    std: l.std,
                }
            })
            .collect();
        self.returns.push(ReturnSlot {
            destination: destination.map(str::to_string),
            entry_depth: self.runtime_depth,
            fired: false,
        });
        let mut translated = Ok(());
        if let Some(first) = inlined.first() {
            let indent = first.indent;
            let mut position = 0;
            // Re-point any error in the (prepended, invisible) body at the call
            // site and name the function, rather than surfacing a std-internal
            // line. A mismatch like `exit("x")` (a string bound where the body
            // uses the parameter as a value) lands here.
            translated = self
                .block(&inlined, &mut position, indent)
                .map_err(|e| err(format!("while inlining `{name}`: {}", e.message)));
        }
        let slot = self.returns.pop();
        self.depth -= 1;
        translated?;
        // Asking for a value from a body that does not produce one is a
        // mistake worth naming: with `if typeof` dispatch it also catches the
        // case where the arm that *would* have returned was not the one taken.
        if destination.is_some() && !slot.is_some_and(|slot| slot.fired) {
            return Err(err(format!(
                "the overload `{}` taken here does not return a value",
                func.signature(name)
            )));
        }
        Ok(())
    }

    /// Lays a NUL-terminated byte string down in fresh thread-local storage:
    /// the `#$` define plus a `li`/`sb` per byte, so the verifier knows the
    /// exact contents (a reader can then branch on them, as `print` does).
    /// `t0` holds the base address and `t1` each value.
    fn emit_string_storage(&mut self, label: &str, bytes: &[u8]) {
        let mut all = bytes.to_vec();
        all.push(0);
        let elements = vec!["u8"; all.len()].join(" ");
        self.out.push(format!("    #$ {label} thread [{elements}]"));
        self.out.push(format!("    la t0, {label}"));
        for (offset, byte) in all.iter().enumerate() {
            self.out.push(format!("    li t1, {byte}"));
            self.out.push(format!("    sb t1, {offset}(t0)"));
        }
    }

    /// `name: <locality> <type> = [v, ...]`: defines a list and fills it in,
    /// so a fixture reads as the data it is rather than as three lines per
    /// element. The expansion is the `#$` define, one `la`, and a `li` plus an
    /// element store per value: byte for byte what the same program written out
    /// by hand lowers to, and visible in the emitted output, which is the
    /// condition the cost contract puts on a multi-instruction lowering
    /// (DEVELOPMENT.md §11). The string-literal argument expansion set the
    /// precedent.
    ///
    /// It **clobbers `t0` and `t1`** (the address and the value being stored),
    /// like that string expansion. A definition normally introduces its storage
    /// before anything is live, so this is stated rather than worked around: an
    /// initialiser that has to preserve `t0` is written out by hand.
    fn define_initialised(
        &mut self,
        name: &str,
        annotation: &str,
        values: &str,
        line: usize,
    ) -> Result<(), TranslateError> {
        let err = |message: String| TranslateError { line, message };
        let define = translate_define(name, annotation).map_err(err)?;
        let elements = define
            .rsplit_once(" [")
            .and_then(|(_, rest)| rest.strip_suffix(']'))
            .map(|inner| inner.split_whitespace().count())
            .ok_or_else(|| {
                err(format!(
                    "`{name}` is initialised with a list, so it needs a list type \
                     (e.g. `{name}: [u32]*4 = ...`)"
                ))
            })?;
        let inner = values
            .strip_prefix('[')
            .and_then(|rest| rest.strip_suffix(']'))
            .ok_or_else(|| err(format!("expected a list literal `[...]`, got `{values}`")))?;
        let items: Vec<&str> = inner
            .split(',')
            .map(str::trim)
            .filter(|item| !item.is_empty())
            .collect();
        if items.len() != elements {
            return Err(err(format!(
                "`{name}` has {elements} elements but its initialiser has {}",
                items.len()
            )));
        }
        for item in &items {
            if parse_int(item).is_none() {
                return Err(err(format!("invalid value `{item}` in the initialiser")));
            }
        }
        self.out.push(define);
        self.out.push(format!("    la t0, {name}"));
        for (index, item) in items.iter().enumerate() {
            self.out.push(format!("    li t1, {item}"));
            self.out.push(format!("    #] t1, {index}(t0)"));
        }
        Ok(())
    }

    /// Translates the statement at `position` (consuming its indented block
    /// if it has one).
    fn statement(&mut self, lines: &[Line], position: &mut usize) -> Result<(), TranslateError> {
        let line = &lines[*position];
        *position += 1;
        let stripped = line.text.as_str();
        let err = |message: String| TranslateError {
            line: line.number,
            message,
        };

        // `asm:` block: every following line indented deeper than the tag is
        // emitted verbatim (one dialect line per source line).
        if stripped == "asm:" {
            let mut emitted = 0usize;
            while let Some(next) = lines.get(*position) {
                if next.indent <= line.indent {
                    break;
                }
                self.out.push(format!("    {}", next.text));
                emitted += 1;
                *position += 1;
            }
            if emitted == 0 {
                return Err(err("empty `asm:` block".to_string()));
            }
            return Ok(());
        }

        // `assume:` block: the indented body is translated normally (so e.g.
        // `n = n % t` becomes `rem`) but bracketed by `#(` / `#)`, which the
        // verifier executes to narrow its symbolic state while codegen drops the
        // whole block. A deliberate, unsound narrowing for tractability.
        if stripped == "assume:" {
            self.out.push("    #(".to_string());
            self.body(lines, position, line)?;
            self.out.push("    #)".to_string());
            return Ok(());
        }

        // Keyword statements.
        if stripped == "fail" {
            self.out.push("    #!".to_string());
            return Ok(());
        }
        if stripped == "unreachable" {
            self.out.push("    #?".to_string());
            return Ok(());
        }
        // `forget <reg>`: havoc the register to `any()` for the verifier (so it
        // treats the value as unknown), emitting nothing at runtime.
        if let Some(register) = stripped.strip_prefix("forget ") {
            let register = register.trim();
            if !is_register(register) {
                return Err(err(format!("`{register}` is not a register")));
            }
            self.out.push(format!("    #~ {register}"));
            return Ok(());
        }
        if let Some(rest) = stripped.strip_prefix("section ") {
            let tokens: Vec<&str> = rest.split_whitespace().collect();
            let [start, end, perms] = tokens.as_slice() else {
                return Err(err("expected `section <start> <end> <r|w|rw>`".to_string()));
            };
            for bound in [start, end] {
                if !is_register(bound) && parse_int(bound).is_none() {
                    return Err(err(format!("invalid section bound `{bound}`")));
                }
            }
            if !matches!(*perms, "r" | "w" | "rw") {
                return Err(err(format!("invalid section permissions `{perms}`")));
            }
            self.out.push(format!("    #@ {start} {end} {perms}"));
            return Ok(());
        }

        // `require <cond>`: `if not <cond>: fail` in one line. Branch over
        // the `#!` when the condition holds.
        if let Some(rest) = stripped.strip_prefix("require ") {
            let condition = parse_condition(rest).map_err(err)?;
            let label = self.fresh_label();
            self.out.push(condition.branch(true, &label));
            self.out.push("    #!".to_string());
            self.out.push(format!("{label}:"));
            return Ok(());
        }

        // `if typeof X == TYPE:` block: a **compile-time** type dispatch, resolved
        // here rather than at runtime. The front-end knows X's category (an integer
        // or a register holds a scalar; a label names string/array storage) and the
        // literal TYPE, compares them, and either translates the body inline (no
        // branch emitted) or skips it entirely. Skipping is what lets `print` carry
        // a string arm and an integer arm in one body: the arm that does not match
        // the argument is never translated, so e.g. the string arm's `&msg` is not
        // emitted (and cannot fail) when `msg` is an integer. (Checked before the
        // plain `if` below, which it also prefix-matches.)
        if let Some(rest) = stripped.strip_prefix("if typeof ") {
            let cond = rest
                .strip_suffix(':')
                .ok_or_else(|| err("`if typeof ...:` needs a trailing `:`".to_string()))?;
            let (operand, type_text) = cond
                .split_once("==")
                .ok_or_else(|| err("expected `if typeof X == TYPE:`".to_string()))?;
            let operand = operand.trim();
            // Reuse the type-expression parser (the one `define` uses) to validate
            // and canonicalise the literal; a leading `[` marks an array type.
            let resolved = translate_type(type_text.trim()).map_err(err)?;
            if resolved == "_" {
                return Err(err(
                    "`if typeof x == _` is always taken: `_` matches a scalar and an array alike, so drop the `if typeof`"
                        .to_string(),
                ));
            }
            let type_is_array = resolved.trim_start().starts_with('[');
            let operand_is_array = parse_int(operand).is_none() && !is_register(operand);
            if operand_is_array == type_is_array {
                self.body(lines, position, line)?;
            } else {
                skip_block(lines, position, line);
            }
            return Ok(());
        }

        // `if <cond>:` block: branch over the body when the condition fails.
        if let Some(rest) = stripped.strip_prefix("if ") {
            let condition = header_condition(rest).map_err(err)?;
            let end = self.fresh_label();
            self.out.push(condition.branch(false, &end));
            self.runtime_depth += 1;
            let body = self.body(lines, position, line);
            self.runtime_depth -= 1;
            body?;
            self.out.push(format!("{end}:"));
            return Ok(());
        }

        // `while <cond>:` block: top-tested loop.
        if let Some(rest) = stripped.strip_prefix("while ") {
            let condition = header_condition(rest).map_err(err)?;
            let start = self.fresh_label();
            let end = self.fresh_label();
            self.out.push(format!("{start}:"));
            self.out.push(condition.branch(false, &end));
            self.runtime_depth += 1;
            let body = self.body(lines, position, line);
            self.runtime_depth -= 1;
            body?;
            self.out.push(format!("    j {start}"));
            self.out.push(format!("{end}:"));
            return Ok(());
        }

        // `def NAME(PARAM):` defines an inline function; its indented body is
        // captured (not translated here) and emitted only where it is called.
        if let Some(rest) = stripped.strip_prefix("def ") {
            let header = rest
                .trim()
                .strip_suffix(':')
                .ok_or_else(|| err("a `def` header needs a trailing `:`".to_string()))?;
            let inner = header
                .strip_suffix(')')
                .ok_or_else(|| err("a `def` needs `name(param)`".to_string()))?;
            let (name, spec) = inner
                .split_once('(')
                .ok_or_else(|| err("a `def` needs `name(param)`".to_string()))?;
            let name = name.trim();
            if !is_label(name) {
                return Err(err(format!("invalid function name `{name}`")));
            }
            // `t0 = type(x)` and `t0 = csr(x)` are assignment forms, and the
            // call branch above runs first, so a def by either name would
            // silently take them over.
            if BUILTIN_CALLS.contains(&name) {
                return Err(err(format!(
                    "`{name}` is a builtin, so a `def` cannot take that name"
                )));
            }
            let spec = spec.trim();
            let ParameterSpec {
                params,
                tuple,
                kinds,
            } = parse_parameter_spec(spec).map_err(err)?;
            let body = self.capture_body(lines, position, line)?;
            // A parameter that the body also defines would have the define
            // renamed to the argument (`a0: [u8*4]`) by the same substitution
            // that binds the parameter.
            if let Some(clash) = body_defines(&body).find(|d| params.iter().any(|p| p == d)) {
                return Err(err(format!(
                    "parameter `{clash}` is also defined in the body of `{name}`: rename one of them"
                )));
            }
            let new = Overload {
                params,
                tuple,
                kinds,
                body,
                spec: spec.to_string(),
                origin: if line.std {
                    format!("std/std.hl line {}", line.number)
                } else {
                    format!("line {}", line.number)
                },
            };
            let overloads = self.functions.entry(name.to_string()).or_default();
            if let Some(twin) = overloads.iter().find(|o| o.overlaps(&new)) {
                return Err(err(format!(
                    "`def {}` overlaps `def {}` ({}): both accept the same call, and the front-end dispatches on arity and on scalar-versus-array only",
                    new.signature(name),
                    twin.signature(name),
                    twin.origin
                )));
            }
            overloads.push(new);
            return Ok(());
        }

        // `NAME(ARG)`: a call to a defined function, inlined here. Checked
        // before assignment because a string argument may contain `=`.
        if let Some(open) = stripped.find('(') {
            let name = stripped[..open].trim();
            if stripped.ends_with(')') && self.functions.contains_key(name) {
                let arg = stripped[open + 1..stripped.len() - 1].trim();
                return self.inline_call(name, arg, line.number, None);
            }
        }

        // `return <value>`: a `def` is inlined, so this is not a jump. It
        // assigns the value to whatever the call site asked for, which is only
        // meaningful in the body's tail: anywhere else the statements after it
        // would still run, and skipping them needs a jump the language does
        // not have. So it is allowed at the tail of a body, or at the tail of
        // a compile-time `if typeof` arm (spliced with no branch, so still the
        // tail), and refused inside a runtime `if`/`while`.
        if stripped == "return" || stripped.starts_with("return ") {
            let value = stripped["return".len()..].trim();
            let Some((destination, entry_depth)) = self
                .returns
                .last()
                .map(|slot| (slot.destination.clone(), slot.entry_depth))
            else {
                return Err(err("`return` outside a `def`".to_string()));
            };
            if value.is_empty() {
                return Err(err("`return` needs a value".to_string()));
            }
            if self.runtime_depth > entry_depth {
                return Err(err(
                    "`return` inside an `if`/`while` would have to jump over the rest of the body, which this language cannot do; set a register and `return` it from the tail instead"
                        .to_string(),
                ));
            }
            // Nothing may follow a `return`: the statement after it would still
            // run. The one exception is the next arm of a compile-time
            // `if typeof`, at a shallower indent, since only one arm is ever
            // translated.
            if let Some(next) = lines.get(*position) {
                let next_arm = next.indent < line.indent && next.text.starts_with("if typeof ");
                if !next_arm {
                    return Err(err(format!(
                        "`return` must be the last statement of its body (only another `if typeof` arm may follow), but `{}` does",
                        next.text
                    )));
                }
            }
            // Validated whether or not the caller wanted the value, so a typo
            // in a dropped return is still an error.
            let assignment =
                translate_assignment(destination.as_deref().unwrap_or("t0"), value).map_err(err)?;
            if destination.is_some() {
                self.out.push(assignment);
            }
            if let Some(slot) = self.returns.last_mut() {
                slot.fired = true;
            }
            return Ok(());
        }

        // Removed constructs get pointed at their replacements.
        if stripped.starts_with("goto ") {
            return Err(err(
                "`goto` is not part of the language; use `if`/`while` blocks".to_string(),
            ));
        }

        // `<reg> = <name>(<arg>)`: a call whose returned value is assigned.
        // Checked before the assignment branch, which cannot express it (that
        // returns one line, and a call expands to a whole body), and gated on
        // the name being a *defined* function so the builtins `type(...)` and
        // `csr(...)` still fall through to it.
        if let Some((lhs, rhs)) = stripped.split_once('=') {
            let (lhs, rhs) = (lhs.trim(), rhs.trim());
            if is_register(lhs) {
                if let Some(open) = rhs.find('(') {
                    let name = rhs[..open].trim();
                    if rhs.ends_with(')') && self.functions.contains_key(name) {
                        let arg = rhs[open + 1..rhs.len() - 1].trim();
                        // The call must be the WHOLE right-hand side. Without
                        // this, `t0 = f(1) + g(2)` matches (it opens with `f(`
                        // and ends with `)`) and the argument comes out as
                        // `1) + g(2`. A call inside a larger expression is not
                        // supported: it would need a scratch register the
                        // language has not decided how to allocate.
                        if unquoted_paren(arg) {
                            return Err(err(format!(
                                "`{rhs}` is not a single call: a call cannot be part of a larger expression, so assign it on its own line first"
                            )));
                        }
                        return self.inline_call(name, arg, line.number, Some(lhs));
                    }
                }
            }
        }

        // `name: <locality> <type> = [v, ...]`: a definition with an
        // initialiser. Checked before the assignment branch, whose `=` split
        // would otherwise take it. The two are told apart by the text before
        // the colon: a definition's is a bare label, while a slice store's
        // (`t0[0:4] = t1`) is `t0[0`, which is not one.
        if let Some((declaration, values)) = stripped.split_once('=') {
            if let Some((name, annotation)) = declaration.split_once(':') {
                let (name, annotation) = (name.trim(), annotation.trim());
                if is_label(name) && !annotation.is_empty() {
                    return self.define_initialised(name, annotation, values.trim(), line.number);
                }
            }
        }

        // Assignments first: a slice store like `t0[0:4] = t1` contains a
        // colon, so it must not be mistaken for a definition.
        if let Some((lhs, rhs)) = stripped.split_once('=') {
            self.out
                .push(translate_assignment(lhs.trim(), rhs.trim()).map_err(err)?);
            return Ok(());
        }

        // `name: <locality> <type>` (a variable definition).
        if let Some((before, after)) = stripped.split_once(':') {
            let name = before.trim();
            let annotation = after.trim();
            if !is_label(name) {
                return Err(err(format!("invalid name `{name}`")));
            }
            if annotation.is_empty() {
                return Err(err(format!(
                    "labels are not part of the language (a definition needs \
                     `{name}: <type>`, with an optional `global`/`thread` before it); \n                     use `if`/`while` blocks"
                )));
            }
            self.out
                .push(translate_define(name, annotation).map_err(err)?);
            return Ok(());
        }

        Err(err(format!("unrecognized statement `{stripped}`")))
    }
}

/// Joins each statement that leaves a `[` open onto the line after it, so a
/// list initialiser can be written in the shape of its data. Only an
/// initialiser can leave one open (every other bracketed form is an index, and
/// comments are already stripped), and the joined statement keeps the first
/// line's number and indentation, so errors still point at where it starts.
fn join_open_brackets(lines: Vec<Line>) -> Vec<Line> {
    let mut out: Vec<Line> = Vec::new();
    for line in lines {
        match out
            .last_mut()
            .filter(|open| open.text.contains('=') && bracket_depth(&open.text) > 0)
        {
            Some(open) => {
                open.text.push(' ');
                open.text.push_str(&line.text);
            }
            None => out.push(line),
        }
    }
    out
}

fn bracket_depth(text: &str) -> i32 {
    let (mut depth, mut quoted, mut escaped) = (0, false, false);
    for c in text.chars() {
        match c {
            _ if escaped => escaped = false,
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            _ if quoted => {}
            '[' => depth += 1,
            ']' => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// A register comparison: `Lt`/`Le`/`Gt`/`Ge`/`Eq`/`Ne`.
#[derive(Clone, Copy)]
enum Comparison {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Comparison {
    fn parse(op: &str) -> Option<Self> {
        Some(match op {
            "<" => Self::Lt,
            "<=" => Self::Le,
            ">" => Self::Gt,
            ">=" => Self::Ge,
            "==" => Self::Eq,
            "!=" => Self::Ne,
            _ => return None,
        })
    }

    fn negated(self) -> Self {
        match self {
            Self::Lt => Self::Ge,
            Self::Ge => Self::Lt,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
        }
    }
}

/// A parsed `if`/`while`/`require` condition.
enum Condition {
    /// `<reg> ==|!= 0` (`equal` distinguishes the two).
    Zero { register: String, equal: bool },
    /// `<reg> <op> <reg>`.
    Registers {
        lhs: String,
        op: Comparison,
        rhs: String,
    },
}

impl Condition {
    /// The branch instruction taken when the condition's truth equals `when`
    /// (so `when = false` branches on the negated condition, which is how an
    /// `if`/`while` jumps over its body).
    fn branch(&self, when: bool, target: &str) -> String {
        match self {
            Self::Zero { register, equal } => {
                if *equal == when {
                    format!("    beqz {register}, {target}")
                } else {
                    format!("    bnez {register}, {target}")
                }
            }
            Self::Registers { lhs, op, rhs } => {
                let op = if when { *op } else { op.negated() };
                match op {
                    Comparison::Lt => format!("    blt {lhs}, {rhs}, {target}"),
                    Comparison::Ge => format!("    bge {lhs}, {rhs}, {target}"),
                    // `>` and `<=` swap the operands onto `blt`/`bge`.
                    Comparison::Gt => format!("    blt {rhs}, {lhs}, {target}"),
                    Comparison::Le => format!("    bge {rhs}, {lhs}, {target}"),
                    Comparison::Eq => format!("    beq {lhs}, {rhs}, {target}"),
                    Comparison::Ne => format!("    bne {lhs}, {rhs}, {target}"),
                }
            }
        }
    }
}

/// Parses an `if`/`while` header's `<cond>:` (the colon with nothing after it;
/// the body is the indented block).
fn header_condition(rest: &str) -> Result<Condition, String> {
    let (condition, tail) = rest
        .split_once(':')
        .ok_or_else(|| "expected `:` after the condition".to_string())?;
    if !tail.trim().is_empty() {
        return Err(format!(
            "nothing may follow `:` (the body is the indented block), got `{}`",
            tail.trim()
        ));
    }
    parse_condition(condition)
}

/// Parses `<reg> <op> <reg>` or `<reg> ==|!= 0`.
fn parse_condition(text: &str) -> Result<Condition, String> {
    let tokens: Vec<&str> = text.split_whitespace().collect();
    let [lhs, op, rhs] = tokens.as_slice() else {
        return Err(format!("invalid condition `{}`", text.trim()));
    };
    if !is_register(lhs) {
        return Err(format!("`{lhs}` is not a register"));
    }
    let Some(op) = Comparison::parse(op) else {
        return Err(format!("unsupported comparison `{op}`"));
    };
    // Zero comparisons get the dedicated zero-branch instructions.
    if *rhs == "0" {
        return match op {
            Comparison::Eq => Ok(Condition::Zero {
                register: lhs.to_string(),
                equal: true,
            }),
            Comparison::Ne => Ok(Condition::Zero {
                register: lhs.to_string(),
                equal: false,
            }),
            _ => Err("only `==`/`!=` compare against the literal `0`; \
                      compare against a register"
                .to_string()),
        };
    }
    if !is_register(rhs) {
        return Err(format!("`{rhs}` is not a register (or `0` with `==`/`!=`)"));
    }
    Ok(Condition::Registers {
        lhs: lhs.to_string(),
        op,
        rhs: rhs.to_string(),
    })
}

/// `name: <locality> <type>` to `#$ name <locality> <type>`, expanding the
/// Pythonic list forms (comma-separated runs `[u8*13]` / `[u8*2, u16*2]`, and
/// the legacy outer `[t, t]*n` cycling suffix) to the dialect's
/// space-separated list type.
/// `name: [<locality>] <type>`. The three spellings say three different
/// things, and the difference is what the **verifier** is asked to do:
///
/// - `x: global u32` / `x: thread u32` pin the locality.
/// - `x: _ u32` asks the verifier to *search* it. Locality is part of the
///   configuration sweep exactly as the type is
///   ([`locality_list`](crate::verifier), `Thread` then `Global`), so this
///   costs exploration and buys a program that verifies under either.
/// - `x: u32` **elides** it and takes [`DEFAULT_LOCALITY`]. No search, no
///   placeholder: the facade for a program that does not care.
///
/// The split is unambiguous because no type starts with a locality keyword.
/// The one word that is both a locality and a type is `_`, and `x: _` reads as
/// the type, so it is `#$ x thread _`: the locality elided, the type searched.
fn translate_define(name: &str, annotation: &str) -> Result<String, String> {
    let (locality, type_text) = match annotation.split_once(' ') {
        Some((first, rest)) if LOCALITIES.contains(&first) => (first, rest.trim()),
        _ => (DEFAULT_LOCALITY, annotation),
    };
    if type_text.is_empty() {
        return Err(format!("expected a type after `{name}:`"));
    }
    // A misspelt locality now reads as part of the type, so the type error
    // says what it was probably meant to be rather than leaving the user to
    // spot it.
    let lowered =
        translate_type(type_text).map_err(|message| match annotation.split_once(' ') {
            Some((first, _)) if is_label(first) && !LOCALITIES.contains(&first) => format!(
                "{message} (if `{first}` was meant as a locality, it must be `global` or `thread`)"
            ),
            _ => message,
        })?;
    Ok(format!("    #$ {name} {locality} {lowered}"))
}

/// The translator's cap on expanded list-type elements. Every element is
/// materialized in the flat dialect text today, so a runaway count must fail
/// loudly instead of attempting a multi-gigabyte expansion (the run-length
/// `Type` representation planned in DEVELOPMENT.md §11 lifts this).
const MAX_LIST_ELEMENTS: usize = 1 << 24;

/// A repetition count (`u8*13`, `[t, t]*n`): plain ASCII digits (no sign, no
/// whitespace), at least 1. `context` is the source text named in errors.
fn parse_repetition(count: &str, context: &str) -> Result<usize, String> {
    if count.is_empty() || !count.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("invalid list repetition `{context}`"));
    }
    let n = count
        .parse::<usize>()
        .map_err(|_| format!("invalid list repetition `{context}`"))?;
    if n == 0 {
        return Err("list repetition must be at least 1".to_string());
    }
    Ok(n)
}

fn translate_type(text: &str) -> Result<String, String> {
    if text == "_" {
        return Ok("_".to_string());
    }
    if SCALARS.contains(&text) {
        return Ok(text.to_string());
    }
    // `[run, run, ...]` optionally suffixed `*n` (Python list repetition).
    // A run is `<scalar>` or `<scalar>*<count>` with `*` binding tightly, so
    // `[u8*13]` is thirteen bytes and `[u8*2, u16*2, u8*3]` is a heterogeneous
    // layout. The legacy outer suffix cycles the whole element list
    // (`[u8, u16]*2` = `[u8 u16 u8 u16]`), making `[u8]*13` == `[u8*13]`.
    if let Some(rest) = text.strip_prefix('[') {
        let (inner, suffix) = rest
            .split_once(']')
            .ok_or_else(|| format!("unterminated list type `{text}`"))?;
        let mut elements: Vec<&str> = Vec::new();
        for run in inner.split(',').map(str::trim).filter(|e| !e.is_empty()) {
            match run.split_once('*') {
                None => {
                    if !SCALARS.contains(&run) {
                        return Err(format!("invalid list element types in `{text}`"));
                    }
                    elements.push(run);
                }
                Some((scalar, count)) => {
                    let (s, c) = (scalar.trim(), count.trim());
                    if (s, c) != (scalar, count) {
                        return Err(format!("list repetition binds tightly: write `{s}*{c}`"));
                    }
                    if !SCALARS.contains(&scalar) {
                        return Err(format!("invalid list element types in `{text}`"));
                    }
                    let n = parse_repetition(count, run)?;
                    if elements.len().saturating_add(n) > MAX_LIST_ELEMENTS {
                        return Err(format!(
                            "list type too large (over {MAX_LIST_ELEMENTS} elements)"
                        ));
                    }
                    elements.extend(std::iter::repeat(scalar).take(n));
                }
            }
        }
        if elements.is_empty() {
            return Err(format!("invalid list element types in `{text}`"));
        }
        let repeats = match suffix.trim() {
            "" => 1usize,
            s => {
                let digits = s
                    .strip_prefix('*')
                    .map(str::trim)
                    .ok_or_else(|| format!("invalid list repetition `{s}`"))?;
                parse_repetition(digits, s)?
            }
        };
        let total = elements
            .len()
            .checked_mul(repeats)
            .filter(|t| *t <= MAX_LIST_ELEMENTS)
            .ok_or_else(|| format!("list type too large (over {MAX_LIST_ELEMENTS} elements)"))?;
        let expanded = if repeats == 1 {
            elements.join(" ")
        } else {
            let cycled: Vec<&str> = elements.iter().cycle().take(total).copied().collect();
            cycled.join(" ")
        };
        return Ok(format!("[{expanded}]"));
    }
    Err(format!("unrecognized type `{text}`"))
}

/// Everything of the form `<lhs> = <rhs>`.
fn translate_assignment(lhs: &str, rhs: &str) -> Result<String, String> {
    // Store: `reg[k] = reg2` (element) or `reg[a:b] = reg2` (raw bytes).
    if let Some((register, index)) = split_index(lhs)? {
        if !is_register(rhs) {
            return Err(format!(
                "a store's right-hand side must be a register, got `{rhs}`"
            ));
        }
        return Ok(match index {
            Index::Element(index) => format!("    #] {rhs}, {index}({register})"),
            Index::Bytes { offset, len } => {
                let mnemonic = match len {
                    1 => "sb",
                    2 => "sh",
                    4 => "sw",
                    _ => return Err(format!("unsupported store width {len} (1, 2 or 4)")),
                };
                format!("    {mnemonic} {rhs}, {offset}({register})")
            }
        });
    }

    if !is_register(lhs) {
        return Err(place_error(lhs));
    }

    // Load: `reg = reg2[k]` (element) or `reg = reg2[a:b]` (raw bytes).
    if let Some((register, index)) = split_index(rhs)? {
        return Ok(match index {
            Index::Element(index) => format!("    #[ {lhs}, {index}({register})"),
            Index::Bytes { offset, len } => {
                let mnemonic = match len {
                    1 => "lb",
                    2 => "lh",
                    4 => "lw",
                    8 => "ld",
                    _ => return Err(format!("unsupported load width {len} (1, 2, 4 or 8)")),
                };
                format!("    {mnemonic} {lhs}, {offset}({register})")
            }
        });
    }

    // Address of a variable: `reg = &label`.
    if let Some(label) = rhs.strip_prefix('&') {
        let label = label.trim();
        if !is_label(label) {
            return Err(format!("invalid label `{label}`"));
        }
        return Ok(format!("    la {lhs}, {label}"));
    }

    // Runtime type descriptor: `reg = type(label)`.
    if let Some(inner) = call_argument(rhs, "type") {
        if !is_label(inner) {
            return Err(format!("invalid label `{inner}`"));
        }
        return Ok(format!("    #& {lhs}, {inner}"));
    }

    // Control/status register: `reg = csr(mhartid)`.
    if let Some(inner) = call_argument(rhs, "csr") {
        if inner != "mhartid" {
            return Err(format!("unsupported CSR `{inner}`"));
        }
        return Ok(format!("    csrr {lhs}, {inner}"));
    }

    // Arithmetic: `reg = reg2 + imm` / `reg = reg2 - imm` (immediate `addi`), or
    // register-register `reg = a + b` / `reg = a * b` (`add` / `mul`).
    let tokens: Vec<&str> = rhs.split_whitespace().collect();
    if let [base, op @ ("+" | "-" | "*" | "/" | "%"), operand] = tokens.as_slice() {
        if !is_register(base) {
            return Err(format!("`{base}` is not a register"));
        }
        // Register-register forms lower to `add` / `sub` / `mul` / `div` / `rem`.
        if is_register(operand) {
            return match *op {
                "+" => Ok(format!("    add {lhs}, {base}, {operand}")),
                "-" => Ok(format!("    sub {lhs}, {base}, {operand}")),
                "*" => Ok(format!("    mul {lhs}, {base}, {operand}")),
                "/" => Ok(format!("    div {lhs}, {base}, {operand}")),
                "%" => Ok(format!("    rem {lhs}, {base}, {operand}")),
                _ => unreachable!(),
            };
        }
        // Immediate forms: `+`/`-` lower to `addi`; `*`/`/`/`%` need a register
        // operand (there is no multiply-, divide-, or remainder-immediate).
        if matches!(*op, "*" | "/" | "%") {
            return Err(format!("`{op}` needs a register operand, not `{operand}`"));
        }
        if parse_int(operand).is_none() {
            return Err(format!("invalid immediate `{operand}`"));
        }
        let imm = if *op == "-" {
            format!("-{operand}")
        } else {
            (*operand).to_string()
        };
        return Ok(format!("    addi {lhs}, {base}, {imm}"));
    }

    // Immediate: `reg = imm`.
    if parse_int(rhs).is_some() {
        return Ok(format!("    li {lhs}, {rhs}"));
    }

    // Register copy: `reg = reg2` (move, lowered to `addi rd, rs, 0`).
    if is_register(rhs) {
        return Ok(format!("    addi {lhs}, {rhs}, 0"));
    }

    // `t1 = nums[0]` indexes a variable directly, the load-side twin of
    // the store `place_error` already catches.
    if let Some((label, _)) = rhs.split_once('[') {
        if is_label(label.trim()) {
            return Err(place_error(rhs));
        }
    }
    Err(format!("unrecognized right-hand side `{rhs}`"))
}

/// What the brackets in `reg[...]` select.
enum Index<'a> {
    /// `reg[k]`: element `k` of whatever the register points at. The width and
    /// the byte offset follow from the pointee's type, so they are resolved by
    /// the verifier (`#[` / `#]`), not here.
    Element(&'a str),
    /// `reg[a:b]`: the raw byte range, for memory with no element type of its
    /// own (a memory-mapped address, a `#@` region, a variable whose type the
    /// verifier is still inferring).
    Bytes { offset: &'a str, len: i64 },
}

/// Splits `reg[...]` into the register and what the brackets select; both the
/// index and the byte offset keep the programmer's literal text (radix
/// preserved). `Ok(None)` when the text is not a bracketed register access.
fn split_index<'a>(text: &'a str) -> Result<Option<(&'a str, Index<'a>)>, String> {
    let Some((register, rest)) = text.split_once('[') else {
        return Ok(None);
    };
    let register = register.trim();
    if !is_register(register) {
        return Ok(None);
    }
    let inner = rest
        .strip_suffix(']')
        .ok_or_else(|| format!("unterminated index `{text}`"))?;
    let Some((start_text, end_text)) = inner.split_once(':') else {
        // `reg[k]`: an element index, which must be a constant.
        let index = inner.trim();
        if index.is_empty() {
            return Err(format!("empty index `{text}`"));
        }
        if is_register(index) {
            return Err(format!(
                "a runtime index `{register}[{index}]` is not supported yet: compute the address with std's `at` (`p = at([arr, {index}, size])`) or by hand (`t = {index} * <element size>`, `p = {register} + t`) and index that with `p[0]`"
            ));
        }
        let value = parse_int(index).ok_or_else(|| format!("invalid index `{index}`"))?;
        if value < 0 {
            return Err(format!("negative index `{index}`"));
        }
        return Ok(Some((register, Index::Element(index))));
    };
    let start_text = start_text.trim();
    let start = parse_int(start_text).ok_or_else(|| format!("invalid offset `{start_text}`"))?;
    let end = parse_int(end_text.trim())
        .ok_or_else(|| format!("invalid offset `{}`", end_text.trim()))?;
    if end <= start {
        return Err(format!("empty slice `{inner}`"));
    }
    Ok(Some((
        register,
        Index::Bytes {
            offset: start_text,
            len: end - start,
        },
    )))
}

/// The error for an assignment target that is not a register, pointing a
/// bracketed *label* (`arr[0] = t1`) at the address-then-index form.
fn place_error(place: &str) -> String {
    match place.split_once('[') {
        Some((label, _)) if is_label(label.trim()) => format!(
            "`{place}` indexes a variable directly: take its address first \
             (`t0 = &{}`), then index the register (`t0[0]`)",
            label.trim()
        ),
        _ => format!("`{place}` is not a register"),
    }
}

/// `name(argument)` for a specific builtin, returning the trimmed argument.
fn call_argument<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    text.strip_prefix(name)?
        .trim_start()
        .strip_prefix('(')?
        .strip_suffix(')')
        .map(str::trim)
}

/// Parses a `"..."` string-literal argument into its bytes (the NUL terminator
/// is appended by the caller). Supports the common escapes; non-ASCII bytes are
/// rejected, since the dialect's `[u8]` storage is one byte per element.
fn parse_string_literal(arg: &str) -> Result<Vec<u8>, String> {
    let inner = arg
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .ok_or_else(|| format!("expected a \"string\" argument, got `{arg}`"))?;
    let mut bytes = Vec::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        let byte = if c == '\\' {
            match chars.next() {
                Some('n') => b'\n',
                Some('t') => b'\t',
                Some('r') => b'\r',
                Some('0') => 0,
                Some('\\') => b'\\',
                Some('"') => b'"',
                Some(other) => return Err(format!("unsupported escape `\\{other}`")),
                None => return Err("trailing `\\` in string literal".to_string()),
            }
        } else if c.is_ascii() {
            c as u8
        } else {
            return Err(format!("non-ASCII character `{c}` in string literal"));
        };
        bytes.push(byte);
    }
    Ok(bytes)
}

/// Replaces whole-token occurrences of `from` with `to` in `text` (an
/// identifier bounded by non-identifier characters), to bind a `def`
/// parameter to a call's argument when inlining the body.
/// What a `def` header declares between its parentheses: the pattern names,
/// whether the pattern is a tuple, and the dispatch kind of each position
/// (`None` for untyped or `_`).
struct ParameterSpec {
    params: Vec<String>,
    tuple: bool,
    kinds: Vec<Option<Kind>>,
}

/// Parses what sits between a `def`'s parentheses: `x`, `x: TYPE`, `[a, b]`
/// or `[a, b]: [T1, T2]`.
fn parse_parameter_spec(spec: &str) -> Result<ParameterSpec, String> {
    let (pattern, type_text) = match split_top_level(spec, ':').as_slice() {
        [pattern] => (pattern.trim(), None),
        [pattern, ty] => (pattern.trim(), Some(ty.trim())),
        _ => {
            return Err(format!(
                "expected `name` or `name: TYPE` in `def ...({spec})`"
            ))
        }
    };
    let (names, tuple): (Vec<&str>, bool) =
        match pattern.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            Some(inner) => (
                split_top_level(inner, ',')
                    .into_iter()
                    .map(str::trim)
                    .collect(),
                true,
            ),
            None => (vec![pattern], false),
        };
    if names.is_empty() {
        return Err("a `def` needs at least one parameter".to_string());
    }
    if tuple && names.len() < 2 {
        return Err(format!(
            "a one-name tuple pattern `{pattern}` is just `{}`: write `def f({})`",
            names.first().copied().unwrap_or(""),
            names.first().copied().unwrap_or("")
        ));
    }
    for name in &names {
        if !is_label(name) {
            return Err(format!("invalid parameter name `{name}`"));
        }
        if is_register(name) || is_reserved(name) {
            return Err(format!(
                "parameter `{name}` is a reserved word (a register, a type, a locality, `_` or `typeof`)"
            ));
        }
    }
    if let Some((_, twice)) = names
        .iter()
        .enumerate()
        .find(|(i, n)| names[..*i].contains(n))
    {
        return Err(format!(
            "parameter `{twice}` is named twice in `def ...({spec})`"
        ));
    }
    let kinds = match type_text {
        None => vec![None; names.len()],
        Some(ty) if tuple => {
            let inner = ty
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .ok_or_else(|| {
                    format!("a tuple pattern needs a tuple type `[T, ...]`, got `{ty}`")
                })?;
            let parts = split_top_level(inner, ',');
            if parts.len() != names.len() {
                return Err(format!(
                    "the pattern `{pattern}` names {} parameters but its type `{ty}` lists {}",
                    names.len(),
                    parts.len()
                ));
            }
            parts
                .iter()
                .map(|p| kind_of_type(p.trim()))
                .collect::<Result<_, _>>()?
        }
        Some(ty) => vec![kind_of_type(ty)?],
    };
    Ok(ParameterSpec {
        params: names.into_iter().map(str::to_string).collect(),
        tuple,
        kinds,
    })
}

/// The dispatch kind a type pattern stands for, validated with the same
/// parser `define` uses: a scalar type is a `Scalar`, a list type an `Array`,
/// and `_` matches either.
fn kind_of_type(ty: &str) -> Result<Option<Kind>, String> {
    if ty == "_" {
        return Ok(None);
    }
    // `[_]` is "any array", legal only here: a define needs a real type.
    if ty == "[_]" {
        return Ok(Some(Kind::Array));
    }
    translate_type(ty).map_err(|e| format!("invalid parameter type `{ty}`: {e}"))?;
    Ok(Some(if ty.starts_with('[') {
        Kind::Array
    } else {
        Kind::Scalar
    }))
}

/// A token that names a type, a locality, `_` or the `typeof` keyword: none
/// may be a parameter name (the substitution would rewrite body annotations)
/// or a call argument (it is not a variable).
fn is_reserved(token: &str) -> bool {
    SCALARS.contains(&token) || LOCALITIES.contains(&token) || token == "typeof"
}

/// The body's defines (`name: <annotation>`), by the same test the statement
/// dispatcher uses: a bare label, then a non-empty annotation. Matching only
/// `thread`/`global` here once missed a define that elided its locality.
fn body_defines(body: &[Line]) -> impl Iterator<Item = &str> {
    body.iter().filter_map(|l| {
        let (decl, rest) = l.text.trim().split_once(':')?;
        let decl = decl.trim();
        (is_label(decl) && !rest.trim().is_empty()).then_some(decl)
    })
}

/// A call's shape for the no-overload message: `a scalar`, `an array`, or
/// `[scalar, array]` for a tuple.
fn describe_kinds(kinds: &[Kind], tuple: bool) -> String {
    let word = |k: &Kind| match k {
        Kind::Scalar => "scalar",
        Kind::Array => "array",
    };
    if tuple {
        let inner: Vec<&str> = kinds.iter().map(word).collect();
        format!("[{}]", inner.join(", "))
    } else {
        match kinds.first() {
            Some(Kind::Scalar) => "a scalar".to_string(),
            _ => "an array".to_string(),
        }
    }
}

/// Splits on `separator` at bracket depth zero and outside string literals,
/// so `[a, "x, y"], b` splits into two, not three. Empty pieces are dropped.
fn split_top_level(text: &str, separator: char) -> Vec<&str> {
    let mut pieces = Vec::new();
    let (mut depth, mut quoted, mut escaped, mut start) = (0i32, false, false, 0);
    for (at, c) in text.char_indices() {
        match c {
            _ if escaped => escaped = false,
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            _ if quoted => {}
            '[' | '(' => depth += 1,
            ']' | ')' => depth -= 1,
            _ if c == separator && depth == 0 => {
                pieces.push(&text[start..at]);
                start = at + c.len_utf8();
            }
            _ => {}
        }
    }
    pieces.push(&text[start..]);
    pieces
        .into_iter()
        .filter(|p| !p.trim().is_empty())
        .collect()
}

/// Whether `text` contains a parenthesis outside a string literal, which is
/// how a call that is only part of a larger expression is told from one that
/// is the whole of it.
fn unquoted_paren(text: &str) -> bool {
    let mut quoted = false;
    let mut escaped = false;
    for c in text.chars() {
        match c {
            _ if escaped => escaped = false,
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            '(' | ')' if !quoted => return true,
            _ => {}
        }
    }
    false
}

/// Applies every substitution in ONE left-to-right pass, so each token is
/// rewritten at most once. Doing them one after another let a later rename
/// rewrite an earlier one's output: binding a parameter to `t0` and then
/// freshening a body-local also called `t0` turned the argument into the
/// local. Longer names are tried first so no substitution is a prefix of
/// another's match.
fn substitute_tokens(text: &str, subs: &[(String, String)]) -> String {
    fn is_ident(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }
    let mut order: Vec<&(String, String)> = subs.iter().collect();
    order.sort_by_key(|(from, _)| std::cmp::Reverse(from.len()));
    let mut out = String::with_capacity(text.len());
    let mut at = 0;
    let (mut quoted, mut escaped) = (false, false);
    while at < text.len() {
        // Text inside a string literal is never a token to substitute.
        let ch = text[at..].chars().next().unwrap();
        if quoted || ch == '"' {
            match ch {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                '"' => quoted = !quoted,
                _ => {}
            }
            out.push(ch);
            at += ch.len_utf8();
            continue;
        }
        let before_ok = at == 0 || !is_ident(text[..at].chars().next_back().unwrap());
        let matched = before_ok
            .then(|| {
                order.iter().find(|(from, _)| {
                    text[at..].starts_with(from.as_str())
                        && text[at + from.len()..]
                            .chars()
                            .next()
                            .is_none_or(|c| !is_ident(c))
                })
            })
            .flatten();
        match matched {
            Some((from, to)) => {
                out.push_str(to);
                at += from.len();
            }
            None => {
                // Step a whole character, so a multi-byte one is not split.
                let ch = text[at..].chars().next().unwrap();
                out.push(ch);
                at += ch.len_utf8();
            }
        }
    }
    out
}

/// Advances `position` past the indented block under `header` without
/// translating it: the not-taken arm of a compile-time `if typeof` dispatch.
fn skip_block(lines: &[Line], position: &mut usize, header: &Line) {
    while let Some(l) = lines.get(*position) {
        if l.indent <= header.indent {
            break;
        }
        *position += 1;
    }
}
