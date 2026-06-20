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
//! welcome: _ [u8]*13           ->  #$ welcome _ [u8 u8 ... u8]
//! t0 = &value                  ->  la t0, value
//! t0 = type(welcome)           ->  #& t0, welcome
//! t0 = csr(mhartid)            ->  csrr t0, mhartid
//! t1 = 0x10000000              ->  li t1, 0x10000000
//! t1 = t1 + 1                  ->  addi t1, t1, 1
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
//! Control flow is structured only: `if` and `while` take an indented block,
//! and `require <cond>` is `if not <cond>: fail` in one line. The surface
//! language has no `goto` and no labels; the labels in the dialect output are
//! generated (`asm:` remains the escape hatch for anything else). A condition
//! is `<reg> <op> <reg>` with `<`/`<=`/`>`/`>=`/`==`/`!=` (`>` and `<=` swap
//! the operands onto `blt`/`bge`), or `<reg> ==|!= 0` (`beqz`/`bnez`).
//!
//! `#` starts a comment exactly as in Python; comments and blank lines do not
//! appear in the output. Loads and stores are byte slices off a register
//! (`reg[offset : offset+len]`), so the access width is visible at the call
//! site: 1 = `lb`/`sb`, 4 = `lw`/`sw`, 8 = `ld`.

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
}

/// An inline function captured from a `def`: its single parameter name and the
/// body lines. The body is translated afresh (with the parameter substituted)
/// at each call site, so there is no calling convention, stack, or `ret`.
#[derive(Clone)]
struct FuncDef {
    param: String,
    body: Vec<Line>,
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
        });
    }

    let mut translator = Translator {
        out: Vec::new(),
        labels: 0,
        strings: 0,
        functions: HashMap::new(),
        depth: 0,
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

struct Translator {
    out: Vec<String>,
    labels: usize,
    strings: usize,
    functions: HashMap<String, FuncDef>,
    /// Inlining depth, a guard against a `def` that calls itself.
    depth: usize,
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
    fn inline_call(&mut self, name: &str, arg: &str, number: usize) -> Result<(), TranslateError> {
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
        let binding = if arg.starts_with('"') {
            let bytes = parse_string_literal(arg).map_err(err)?;
            let label = self.fresh_string();
            self.emit_string_storage(&label, &bytes);
            label
        } else if parse_int(arg).is_some() {
            arg.to_string()
        } else {
            return Err(err(format!(
                "a call argument must be a \"string\" or an integer, got `{arg}`"
            )));
        };

        let func = match self.functions.get(name) {
            Some(func) => func.clone(),
            None => return Err(err(format!("unknown function `{name}`"))),
        };
        let inlined: Vec<Line> = func
            .body
            .iter()
            .map(|l| Line {
                number: l.number,
                indent: l.indent,
                text: substitute_token(&l.text, &func.param, &binding),
            })
            .collect();
        if let Some(first) = inlined.first() {
            let indent = first.indent;
            let mut position = 0;
            // Re-point any error in the (prepended, invisible) body at the call
            // site and name the function, rather than surfacing a std-internal
            // line. A mismatch like `exit("x")` (a string bound where the body
            // uses the parameter as a value) lands here.
            self.block(&inlined, &mut position, indent)
                .map_err(|e| err(format!("while inlining `{name}`: {}", e.message)))?;
        }
        self.depth -= 1;
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

        // `if <cond>:` block: branch over the body when the condition fails.
        if let Some(rest) = stripped.strip_prefix("if ") {
            let condition = header_condition(rest).map_err(err)?;
            let end = self.fresh_label();
            self.out.push(condition.branch(false, &end));
            self.body(lines, position, line)?;
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
            self.body(lines, position, line)?;
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
            let (name, param) = inner
                .split_once('(')
                .ok_or_else(|| err("a `def` needs `name(param)`".to_string()))?;
            let name = name.trim();
            let param = param.trim();
            if !is_label(name) {
                return Err(err(format!("invalid function name `{name}`")));
            }
            if !is_label(param) {
                return Err(err(format!("invalid parameter name `{param}`")));
            }
            let body = self.capture_body(lines, position, line)?;
            self.functions.insert(
                name.to_string(),
                FuncDef {
                    param: param.to_string(),
                    body,
                },
            );
            return Ok(());
        }

        // `NAME(ARG)`: a call to a defined function, inlined here. Checked
        // before assignment because a string argument may contain `=`.
        if let Some(open) = stripped.find('(') {
            let name = stripped[..open].trim();
            if stripped.ends_with(')') && self.functions.contains_key(name) {
                let arg = stripped[open + 1..stripped.len() - 1].trim();
                return self.inline_call(name, arg, line.number);
            }
        }

        // Removed constructs get pointed at their replacements.
        if stripped.starts_with("goto ") {
            return Err(err(
                "`goto` is not part of the language; use `if`/`while` blocks".to_string(),
            ));
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
                     `{name}: <locality> <type>`); use `if`/`while` blocks"
                )));
            }
            self.out
                .push(translate_define(name, annotation).map_err(err)?);
            return Ok(());
        }

        Err(err(format!("unrecognized statement `{stripped}`")))
    }
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
/// Pythonic `[t, t]` and `[t]*n` list forms to the dialect's space-separated
/// list type.
fn translate_define(name: &str, annotation: &str) -> Result<String, String> {
    let (locality, type_text) = annotation
        .split_once(' ')
        .ok_or_else(|| format!("expected `<locality> <type>` after `{name}:`"))?;
    if !LOCALITIES.contains(&locality) {
        return Err(format!("invalid locality `{locality}`"));
    }
    let type_text = type_text.trim();
    let lowered = translate_type(type_text)?;
    Ok(format!("    #$ {name} {locality} {lowered}"))
}

fn translate_type(text: &str) -> Result<String, String> {
    if text == "_" {
        return Ok("_".to_string());
    }
    if SCALARS.contains(&text) {
        return Ok(text.to_string());
    }
    // `[t, t, ...]` optionally suffixed `*n` (Python list repetition).
    if let Some(rest) = text.strip_prefix('[') {
        let (inner, suffix) = rest
            .split_once(']')
            .ok_or_else(|| format!("unterminated list type `{text}`"))?;
        let elements: Vec<&str> = inner
            .split(',')
            .map(str::trim)
            .filter(|e| !e.is_empty())
            .collect();
        if elements.is_empty() || !elements.iter().all(|e| SCALARS.contains(e)) {
            return Err(format!("invalid list element types in `{text}`"));
        }
        let repeats = match suffix.trim() {
            "" => 1usize,
            s => {
                let n = s
                    .strip_prefix('*')
                    .map(str::trim)
                    .and_then(|n| n.parse::<usize>().ok())
                    .ok_or_else(|| format!("invalid list repetition `{s}`"))?;
                if n == 0 {
                    return Err("list repetition must be at least 1".to_string());
                }
                n
            }
        };
        let expanded: Vec<&str> = elements
            .iter()
            .cycle()
            .take(elements.len() * repeats)
            .copied()
            .collect();
        return Ok(format!("[{}]", expanded.join(" ")));
    }
    Err(format!("unrecognized type `{text}`"))
}

/// Everything of the form `<lhs> = <rhs>`.
fn translate_assignment(lhs: &str, rhs: &str) -> Result<String, String> {
    // Store: `reg[a:b] = reg2`.
    if let Some((register, slice)) = split_slice(lhs)? {
        if !is_register(rhs) {
            return Err(format!(
                "a store's right-hand side must be a register, got `{rhs}`"
            ));
        }
        let (offset, len) = slice;
        let mnemonic = match len {
            1 => "sb",
            4 => "sw",
            _ => return Err(format!("unsupported store width {len} (1 or 4)")),
        };
        return Ok(format!("    {mnemonic} {rhs}, {offset}({register})"));
    }

    if !is_register(lhs) {
        return Err(format!("`{lhs}` is not a register"));
    }

    // Load: `reg = reg2[a:b]`.
    if let Some((register, (offset, len))) = split_slice(rhs)? {
        let mnemonic = match len {
            1 => "lb",
            4 => "lw",
            8 => "ld",
            _ => return Err(format!("unsupported load width {len} (1, 4 or 8)")),
        };
        return Ok(format!("    {mnemonic} {lhs}, {offset}({register})"));
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
    if let [base, op @ ("+" | "-" | "*" | "%"), operand] = tokens.as_slice() {
        if !is_register(base) {
            return Err(format!("`{base}` is not a register"));
        }
        // Register-register forms lower to `add` / `sub` / `mul` / `rem`.
        if is_register(operand) {
            return match *op {
                "+" => Ok(format!("    add {lhs}, {base}, {operand}")),
                "-" => Ok(format!("    sub {lhs}, {base}, {operand}")),
                "*" => Ok(format!("    mul {lhs}, {base}, {operand}")),
                "%" => Ok(format!("    rem {lhs}, {base}, {operand}")),
                _ => unreachable!(),
            };
        }
        // Immediate forms: `+`/`-` lower to `addi`; `*`/`%` need a register
        // operand (there is no multiply- or remainder-immediate).
        if *op == "*" || *op == "%" {
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

    Err(format!("unrecognized right-hand side `{rhs}`"))
}

/// Splits `reg[a:b]` into the register and `(offset-text, length)`; the
/// offset keeps the programmer's literal text (radix preserved).
#[allow(clippy::type_complexity)]
fn split_slice(text: &str) -> Result<Option<(&str, (&str, i64))>, String> {
    let Some((register, rest)) = text.split_once('[') else {
        return Ok(None);
    };
    let register = register.trim();
    if !is_register(register) {
        return Ok(None);
    }
    let inner = rest
        .strip_suffix(']')
        .ok_or_else(|| format!("unterminated slice `{text}`"))?;
    let (start_text, end_text) = inner
        .split_once(':')
        .ok_or_else(|| format!("a slice needs `start:end`, got `{inner}`"))?;
    let start_text = start_text.trim();
    let start = parse_int(start_text).ok_or_else(|| format!("invalid offset `{start_text}`"))?;
    let end = parse_int(end_text.trim())
        .ok_or_else(|| format!("invalid offset `{}`", end_text.trim()))?;
    if end <= start {
        return Err(format!("empty slice `{inner}`"));
    }
    Ok(Some((register, (start_text, end - start))))
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
fn substitute_token(text: &str, from: &str, to: &str) -> String {
    fn is_ident(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(pos) = rest.find(from) {
        let (before, matched) = rest.split_at(pos);
        let after = &matched[from.len()..];
        out.push_str(before);
        let before_ok = before.chars().next_back().is_none_or(|c| !is_ident(c));
        let after_ok = after.chars().next().is_none_or(|c| !is_ident(c));
        if before_ok && after_ok {
            out.push_str(to);
        } else {
            out.push_str(from);
        }
        rest = after;
    }
    out.push_str(rest);
    out
}
