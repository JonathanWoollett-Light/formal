use std::alloc::{alloc, Layout};
use std::fmt;
use std::path::PathBuf;
use std::ptr::{write, NonNull};

#[derive(Debug)]
pub struct AstNode {
    pub prev: Option<NonNull<AstNode>>,
    pub span: Span,
    pub this: Instruction,
    pub next: Option<NonNull<AstNode>>,
}

#[derive(Debug)]
pub struct Span {
    path: PathBuf,
    row: usize,
    column: usize,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}:{}", self.path.display(), self.row, self.column)
    }
}

pub fn new_ast(src: &[char], path: PathBuf) -> Option<NonNull<AstNode>> {
    let mut front_opt = None;
    let mut a = 0;
    let mut b = 0;
    let mut row = 1;
    while b < src.len() {
        // See https://stackoverflow.com/questions/1761051/difference-between-n-and-r
        #[cfg(target_os = "windows")]
        match src.get(b..=b + 1) {
            Some(['\r', '\n']) => {
                alloc_node(
                    &src[a..b],
                    &mut front_opt,
                    Span {
                        path: path.clone(),
                        row,
                        column: 0,
                    },
                );
                row += 1;
                a = b + 2;
            }
            _ => {}
        }

        #[cfg(target_os = "linux")]
        if src[b] == '\n' {
            alloc_node(
                &src[a..b],
                &mut front_opt,
                Span {
                    path: path.clone(),
                    row,
                    column: 0,
                },
            );
            row += 1;
            a = b + 1;
        }
        b += 1;
    }
    alloc_node(
        &src[a..b],
        &mut front_opt,
        Span {
            path,
            row,
            column: 0,
        },
    );

    let mut first = None;
    while let Some(current) = front_opt {
        first = Some(current);
        front_opt = unsafe { current.as_ref().prev };
    }
    first
}

fn alloc_node(mut src: &[char], front_opt: &mut Option<NonNull<AstNode>>, span: Span) {
    let mut i = 0;
    src = loop {
        match src.get(i) {
            None => return,
            Some(' ') => {}
            Some(_) => break &src[i..],
        }
        i += 1;
    };

    // println!("{src:?} | {span}");

    let instr = match src {
        ['#', '!'] => Instruction::Fail(Fail),
        ['#', '?'] => Instruction::Unreachable(Unreachable),
        ['#', '$', ' ', rem @ ..] => Instruction::Define(new_cast(rem)),
        ['#', ..] => return,
        _ => new_instruction(src),
    };

    let nonnull = unsafe {
        let ptr = alloc(Layout::new::<AstNode>()).cast();
        write(
            ptr,
            AstNode {
                prev: *front_opt,
                span,
                this: instr,
                next: None,
            },
        );
        NonNull::new(ptr).unwrap()
    };
    if let Some(front) = front_opt {
        unsafe {
            front.as_mut().next = Some(nonnull);
        }
        *front = nonnull;
    } else {
        *front_opt = Some(nonnull);
    }
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Csrr(Csrr),
    Bnez(Bnez),
    J(J),
    Wfi(Wfi),
    Label(LabelInstruction),
    Global(Global),
    Data(Data),
    Ascii(Ascii),
    Fail(Fail),
    La(La),
    Li(Li),
    Sw(Sw),
    Lw(Lw),
    Addi(Addi),
    Blt(Blt),
    Lb(Lb),
    Beqz(Beqz),
    Sb(Sb),
    Unreachable(Unreachable),
    Bge(Bge),
    Ld(Ld),
    Bne(Bne),
    Define(Define),
    Lat(Lat),
    Branch(Branch),
    Beq(Beq),
}

impl Instruction {
    /// Returns all the variables found within this instruction.
    pub fn variable(&self) -> Option<&Label> {
        use Instruction as Instr;
        match self {
            Instr::Ascii(Ascii { label, .. }) | Instr::La(La { label, .. }) => Some(label),
            _ => None,
        }
    }
}

fn new_instruction(src: &[char]) -> Instruction {
    match src {
        ['.', 'g', 'l', 'o', 'b', 'a', 'l', ' ', rem @ ..] => Instruction::Global(new_global(rem)),
        ['c', 's', 'r', 'r', ' ', rem @ ..] => Instruction::Csrr(new_csrr(rem)),
        ['b', 'n', 'e', 'z', ' ', rem @ ..] => Instruction::Bnez(new_bnez(rem)),
        ['j', ' ', rem @ ..] => Instruction::J(new_j(rem)),
        ['w', 'f', 'i'] => Instruction::Wfi(Wfi),
        ['.', 'd', 'a', 't', 'a'] => Instruction::Data(Data),
        ['.', 'a', 's', 'c', 'i', 'i', ' ', rem @ ..] => Instruction::Ascii(new_ascii(rem)),
        ['l', 'a', ' ', rem @ ..] => Instruction::La(new_la(rem)),
        ['l', 'i', ' ', rem @ ..] => Instruction::Li(new_li(rem)),
        ['s', 'w', ' ', rem @ ..] => Instruction::Sw(new_sw(rem)),
        ['l', 'w', ' ', rem @ ..] => Instruction::Lw(new_lw(rem)),
        ['a', 'd', 'd', 'i', ' ', rem @ ..] => Instruction::Addi(new_addi(rem)),
        ['b', 'l', 't', ' ', rem @ ..] => Instruction::Blt(new_blt(rem)),
        ['l', 'b', ' ', rem @ ..] => Instruction::Lb(new_lb(rem)),
        ['b', 'e', 'q', 'z', ' ', rem @ ..] => Instruction::Beqz(new_beqz(rem)),
        ['s', 'b', ' ', rem @ ..] => Instruction::Sb(new_sb(rem)),
        ['b', 'g', 'e', ' ', rem @ ..] => Instruction::Bge(new_bge(rem)),
        ['l', 'd', ' ', rem @ ..] => Instruction::Ld(new_ld(rem)),
        ['b', 'n', 'e', ' ', rem @ ..] => Instruction::Bne(new_bne(rem)),
        ['l', 'a', 't', ' ', rem @ ..] => Instruction::Lat(new_lat(rem)),
        ['b', 'r', 'a', 'n', 'c', 'h', ' ', rem @ ..] => Instruction::Branch(new_branch(rem)),
        ['b', 'e', 'q', ' ', rem @ ..] => Instruction::Beq(new_beq(rem)),
        [.., ':'] => Instruction::Label(new_label_instruction(src)),
        x => todo!("{x:?}"),
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Instruction::*;
        match self {
            Lat(lat) => write!(f, "{lat}"),
            Csrr(csrr) => write!(f, "{csrr}"),
            Bnez(bnez) => write!(f, "{bnez}"),
            J(j) => write!(f, "{j}"),
            Wfi(wfi) => write!(f, "{wfi}"),
            Label(label_instruction) => write!(f, "{label_instruction}"),
            Global(global) => write!(f, "{global}"),
            Data(data) => write!(f, "{data}"),
            Ascii(ascii) => write!(f, "{ascii}"),
            Fail(fail) => write!(f, "{fail}"),
            La(la) => write!(f, "{la}"),
            Li(li) => write!(f, "{li}"),
            Sw(sw) => write!(f, "{sw}"),
            Lw(lw) => write!(f, "{lw}"),
            Addi(addi) => write!(f, "{addi}"),
            Blt(blt) => write!(f, "{blt}"),
            Lb(lb) => write!(f, "{lb}"),
            Beqz(beqz) => write!(f, "{beqz}"),
            Sb(sb) => write!(f, "{sb}"),
            Bge(bge) => write!(f, "{bge}"),
            Ld(ld) => write!(f, "{ld}"),
            Bne(bne) => write!(f, "{bne}"),
            Unreachable(unreachable) => write!(f, "{unreachable}"),
            Define(cast) => write!(f, "{cast}"),
            Branch(branch) => write!(f, "{branch}"),
            Beq(beq) => write!(f, "{beq}"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FlatType {
    U8 = 0,
    I8 = 1,
    U16 = 2,
    I16 = 3,
    U32 = 4,
    I32 = 5,
    U64 = 6,
    I64 = 7,
    List = 8,
    Union = 9,
}

impl From<&Type> for FlatType {
    fn from(t: &Type) -> Self {
        match t {
            Type::U8 => FlatType::U8,
            Type::I8 => FlatType::I8,
            Type::U16 => FlatType::U16,
            Type::I16 => FlatType::I16,
            Type::U32 => FlatType::U32,
            Type::I32 => FlatType::I32,
            Type::U64 => FlatType::U64,
            Type::I64 => FlatType::I64,
            Type::List(_) => FlatType::List,
            Type::Union(_) => FlatType::Union,
        }
    }
}
impl From<Type> for FlatType {
    fn from(t: Type) -> Self {
        Self::from(&t)
    }
}
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Locality {
    Thread = 1,
    Global = 0,
}

impl fmt::Display for Locality {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Thread => "thread",
                Self::Global => "global",
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    List(Vec<Type>),
    /// Union are kinda virtual
    Union(BTreeSet<Type>),
}
impl Type {
    pub fn list_mut(&mut self) -> &mut Vec<Type> {
        match self {
            Self::List(list) => list,
            _ => panic!(),
        }
    }
}

impl TryFrom<FlatType> for Type {
    type Error = ();
    fn try_from(flat: FlatType) -> Result<Self, Self::Error> {
        match flat {
            FlatType::I8 => Ok(Self::I8),
            FlatType::U8 => Ok(Self::U8),
            FlatType::I16 => Ok(Self::I16),
            FlatType::U16 => Ok(Self::U16),
            FlatType::I32 => Ok(Self::I32),
            FlatType::U32 => Ok(Self::U32),
            FlatType::I64 => Ok(Self::I64),
            FlatType::U64 => Ok(Self::U64),
            FlatType::List => Err(()),
            FlatType::Union => Err(()),
        }
    }
}

use itertools::intersperse;

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::U8 => write!(f, "u8"),
            Type::I8 => write!(f, "i8"),
            Type::U16 => write!(f, "u16"),
            Type::I16 => write!(f, "i16"),
            Type::U32 => write!(f, "u32"),
            Type::I32 => write!(f, "i32"),
            Type::U64 => write!(f, "u64"),
            Type::I64 => write!(f, "i64"),
            Type::List(types) => write!(
                f,
                "[{}]",
                intersperse(types.iter().map(|t| t.to_string()), String::from(" "))
                    .collect::<String>()
            ),
            Type::Union(union) => write!(
                f,
                "{{{}}}",
                intersperse(union.iter().map(|t| t.to_string()), String::from(" "))
                    .collect::<String>()
            ),
        }
    }
}

fn new_type(src: &[char]) -> Type {
    let mut i = 0;
    let mut current_list: Option<Vec<Type>> = None;
    let mut list_stack: Vec<Vec<Type>> = Vec::new();
    loop {
        let Some(c) = src.get(i) else {
            break;
        };
        match c {
            '#' => break,
            ']' => {
                let current = Type::List(current_list.take().unwrap());
                if let Some(mut stacked) = list_stack.pop() {
                    stacked.push(current);
                    current_list = Some(stacked);
                    i += 1;
                } else {
                    return current;
                }
            }
            ' ' => {
                i += 1;
            }
            '[' => {
                if let Some(existing) = current_list {
                    list_stack.push(existing);
                }
                current_list = Some(Vec::new());
                i += 1;
            }
            'u' => {
                let ttype = if let Some('8') = src.get(i + 1) {
                    i += 2;
                    Type::U8
                } else if let Some(['1', '6']) = src.get(i + 1..i + 3) {
                    i += 3;
                    Type::U16
                } else if let Some(['3', '2']) = src.get(i + 1..i + 3) {
                    i += 3;
                    Type::U32
                } else if let Some(['6', '4']) = src.get(i + 1..i + 3) {
                    i += 3;
                    Type::U64
                } else {
                    todo!()
                };
                if let Some(list) = &mut current_list {
                    list.push(ttype);
                } else {
                    return ttype;
                }
            }
            'i' => {
                let ttype = if let Some('8') = src.get(i + 1) {
                    i += 2;
                    Type::I8
                } else if let Some(['1', '6']) = src.get(i + 1..i + 3) {
                    i += 3;
                    Type::I16
                } else if let Some(['3', '2']) = src.get(i + 1..i + 3) {
                    i += 3;
                    Type::I32
                } else if let Some(['6', '4']) = src.get(i + 1..i + 3) {
                    i += 3;
                    Type::I64
                } else {
                    todo!()
                };
                if let Some(list) = &mut current_list {
                    list.push(ttype);
                } else {
                    return ttype;
                }
            }
            x => todo!("{x:?} {src:?}"),
        }
    }
    todo!()

    // let types = src.split(|c| *c == ',').collect::<Vec<_>>();
    // if let [single] = types.as_slice() {

    // } else {
    //     Type::List(types.iter().map(|c| new_type(c)).collect())
    // }
}

/// Defines a variable.
///
/// This is neccessary since not all type combinations are explored and to be
/// practical (not have absurd compile times) some may need to be manually
/// specified.
#[derive(Debug, Clone)]
pub struct Define {
    pub label: Label,
    pub locality: Option<Locality>,
    pub cast: Option<Type>,
}

impl fmt::Display for Define {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "#$ {} {} {}",
            self.label,
            match &self.locality {
                None => String::from("_"),
                Some(locality) => locality.to_string(),
            },
            match &self.cast {
                None => String::from("_"),
                Some(cast) => cast.to_string(),
            }
        )
    }
}

fn new_cast(src: &[char]) -> Define {
    let mut i = 0;
    let mut j = 1;

    let label = loop {
        if src[j] == ' ' {
            break new_label(&src[i..j]);
        }
        j += 1;
    };
    j += 1;
    i = j;
    let locality = loop {
        if src[j] == ' ' {
            if matches!(src[i..j], ['_']) {
                break None;
            } else {
                break Some(new_locality(&src[i..j]));
            }
        }
        j += 1;
    };
    j += 1;
    i = j;

    let cast = loop {
        match src.get(j) {
            None | Some('#') => {
                if matches!(src[i..j], ['_']) {
                    break None;
                } else {
                    break Some(new_type(&src[i..j]));
                }
            }
            Some(_) => {}
        }
        j += 1;
    };

    Define {
        label,
        locality,
        cast,
    }
}
fn new_locality(src: &[char]) -> Locality {
    match src {
        ['t', 'h', 'r', 'e', 'a', 'd'] => Locality::Thread,
        ['g', 'l', 'o', 'b', 'a', 'l'] => Locality::Global,
        x @ _ => todo!("{x:?}"),
    }
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub out: Label,
}

impl fmt::Display for Branch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "branch {}", self.out)
    }
}
fn new_branch(src: &[char]) -> Branch {
    let out = src
        .iter()
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Branch {
        out: new_label(&out),
    }
}

#[derive(Debug, Clone)]
pub struct Beq {
    pub lhs: Register,
    pub rhs: Register,
    pub out: Label,
}

impl fmt::Display for Beq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "beq {}, {}, {}", self.lhs, self.rhs, self.out)
    }
}

fn new_beq(src: &[char]) -> Beq {
    let lhs = &src[0..2];
    let rhs = &src[4..6];
    let out = src
        .iter()
        .skip(8)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Beq {
        lhs: new_register(lhs).unwrap(),
        rhs: new_register(rhs).unwrap(),
        out: new_label(&out),
    }
}

#[derive(Debug, Clone)]
pub struct Bne {
    pub lhs: Register,
    pub rhs: Register,
    pub out: Label,
}

impl fmt::Display for Bne {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "bne {}, {}, {}", self.lhs, self.rhs, self.out)
    }
}

fn new_bne(src: &[char]) -> Bne {
    let lhs = &src[0..2];
    let rhs = &src[4..6];
    let out = src
        .iter()
        .skip(8)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Bne {
        lhs: new_register(lhs).unwrap(),
        rhs: new_register(rhs).unwrap(),
        out: new_label(&out),
    }
}

#[derive(Debug, Clone)]
pub struct Bge {
    pub lhs: Register,
    pub rhs: Register,
    pub out: Label,
}

impl fmt::Display for Bge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "bge {}, {}, {}", self.lhs, self.rhs, self.out)
    }
}

fn new_bge(src: &[char]) -> Bge {
    let lhs = &src[0..2];
    let rhs = &src[4..6];
    let out = src
        .iter()
        .skip(8)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Bge {
        lhs: new_register(lhs).unwrap(),
        rhs: new_register(rhs).unwrap(),
        out: new_label(&out),
    }
}

#[derive(Debug, Clone)]
pub struct Beqz {
    pub register: Register,
    pub label: Label,
}

impl fmt::Display for Beqz {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "beqz {}, {}", self.register, self.label)
    }
}

fn new_beqz(src: &[char]) -> Beqz {
    Beqz {
        register: new_register(&src[..2]).unwrap(),
        label: new_label(&src[4..]),
    }
}

#[derive(Debug, Clone)]
pub struct Lb {
    pub to: Register,
    pub from: Register,
    pub offset: Offset,
}

impl fmt::Display for Lb {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "lb {}, {}({})", self.to, self.offset, self.from)
    }
}

fn new_lb(src: &[char]) -> Lb {
    let to = new_register(&src[..2]).unwrap();
    for i in 4..src.len() {
        if src[i] == '(' {
            return Lb {
                to,
                from: new_register(&src[i + 1..src.len() - 1]).unwrap(),
                offset: new_offset(&src[4..i]).unwrap(),
            };
        }
    }
    unreachable!()
}

#[derive(Debug, Clone)]
pub struct Blt {
    pub lhs: Register,
    pub rhs: Register,
    pub label: Label,
}

impl fmt::Display for Blt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "blt {}, {}, {}", self.lhs, self.rhs, self.label)
    }
}

fn new_blt(src: &[char]) -> Blt {
    let label = src
        .iter()
        .skip(8)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Blt {
        lhs: new_register(&src[..2]).unwrap(),
        rhs: new_register(&src[4..6]).unwrap(),
        label: new_label(&label),
    }
}

#[derive(Debug, Clone)]
pub struct Addi {
    pub out: Register,
    pub lhs: Register,
    pub rhs: Immediate,
}

impl fmt::Display for Addi {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "addi {}, {}, {}", self.out, self.lhs, self.rhs)
    }
}

fn new_addi(src: &[char]) -> Addi {
    let rhs = src
        .iter()
        .skip(8)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Addi {
        out: new_register(&src[0..2]).unwrap(),
        lhs: new_register(&src[4..6]).unwrap(),
        rhs: new_immediate(&rhs).unwrap(),
    }
}

#[derive(Debug, Clone)]
pub struct Lw {
    pub to: Register,
    pub from: Register,
    pub offset: Offset,
}

impl fmt::Display for Lw {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "lw {}, {}({})", self.to, self.offset, self.from)
    }
}

fn new_lw(src: &[char]) -> Lw {
    let to = new_register(&src[..2]).unwrap();
    for i in 4..src.len() {
        if src[i] == '(' {
            let from = src
                .iter()
                .skip(i + 1)
                .take_while(|&&c| c != ')')
                .copied()
                .collect::<Vec<_>>();
            return Lw {
                to,
                from: new_register(&from).unwrap(),
                offset: new_offset(&src[4..i]).unwrap(),
            };
        }
    }
    unreachable!()
}

#[derive(Debug, Clone)]
pub struct Ld {
    pub to: Register,
    pub from: Register,
    pub offset: Offset,
}

impl fmt::Display for Ld {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ld {}, {}({})", self.to, self.offset, self.from)
    }
}

fn new_ld(src: &[char]) -> Ld {
    let to = new_register(&src[..2]).unwrap();
    for i in 4..src.len() {
        if src[i] == '(' {
            let from = src
                .iter()
                .skip(i + 1)
                .take_while(|&&c| c != ')')
                .copied()
                .collect::<Vec<_>>();
            return Ld {
                to,
                from: new_register(&from).unwrap(),
                offset: new_offset(&src[4..i]).unwrap(),
            };
        }
    }
    unreachable!()
}

#[derive(Debug, Clone)]
pub struct Sb {
    pub to: Register,
    pub from: Register,
    pub offset: Offset,
}

impl fmt::Display for Sb {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "sb {}, {}({})", self.from, self.offset, self.to)
    }
}

fn new_sb(src: &[char]) -> Sb {
    let from = new_register(&src[..2]).unwrap();
    for i in 4..src.len() {
        if src[i] == '(' {
            return Sb {
                from,
                to: new_register(&src[i + 1..src.len() - 1]).unwrap(),
                offset: new_offset(&src[4..i]).unwrap(),
            };
        }
    }
    unreachable!()
}

#[derive(Debug, Clone)]
pub struct Sw {
    pub to: Register,
    pub from: Register,
    pub offset: Offset,
}

impl fmt::Display for Sw {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "sw {}, {}({})", self.from, self.offset, self.to)
    }
}

fn new_sw(src: &[char]) -> Sw {
    let from = new_register(&src[..2]).unwrap();
    for i in 4..src.len() {
        if src[i] == '(' {
            return Sw {
                from,
                to: new_register(&src[i + 1..src.len() - 1]).unwrap(),
                offset: new_offset(&src[4..i]).unwrap(),
            };
        }
    }
    unreachable!()
}

#[derive(Debug, Clone)]
pub struct Offset {
    pub value: Immediate,
}

impl fmt::Display for Offset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let x = if self.value == Immediate::ZERO {
            String::new()
        } else {
            self.value.to_string()
        };
        write!(f, "{x}")
    }
}

fn new_offset(src: &[char]) -> Result<Offset, <i64 as std::str::FromStr>::Err> {
    Ok(Offset {
        value: if src.is_empty() {
            Immediate { value: 0 }
        } else {
            new_immediate(src)?
        },
    })
}

#[derive(Debug, Clone)]
pub struct Unreachable;

impl fmt::Display for Unreachable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#?")
    }
}

#[derive(Debug, Clone)]
pub struct Fail;

impl fmt::Display for Fail {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#!")
    }
}

#[derive(Debug, Clone)]
pub struct Data;

impl fmt::Display for Data {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, ".data")
    }
}

#[derive(Clone)]
pub struct Ascii {
    label: Label,
    string: Vec<u8>,
}

impl fmt::Display for Ascii {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            ".ascii {}, {:?}",
            self.label,
            std::str::from_utf8(&self.string)
        )
    }
}

impl fmt::Debug for Ascii {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Point")
            .field(
                "string",
                &self.string.iter().map(|c| *c as char).collect::<String>(),
            )
            .finish()
    }
}

fn new_ascii(src: &[char]) -> Ascii {
    todo!()
    // assert_eq!(src[0], '"');
    // assert_eq!(src[src.len() - 1], '"');
    // Ascii {
    //     string: src[1..src.len() - 1].iter().map(|c| *c as u8).collect(),
    // }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Clone, Copy)]
#[non_exhaustive]
pub enum Register {
    X0,
    X1,
    X2,
    X3,
    X4,
    X5,
    X6,
    X7,
    X8,
    X9,
    X10,
    X11,
    X12,
    X13,
    X14,
    X15,
    X16,
    X17,
    X18,
    X19,
    X20,
    X21,
    X22,
    X23,
    X24,
    X25,
    X26,
    X27,
    X28,
    X29,
    X30,
    X31,
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::X0 => write!(f, "zero"),
            Self::X1 => write!(f, "ra"),
            Self::X2 => write!(f, "sp"),
            Self::X3 => write!(f, "gp"),
            Self::X4 => write!(f, "tp"),
            Self::X5 => write!(f, "t0"),
            Self::X6 => write!(f, "t1"),
            Self::X7 => write!(f, "t2"),
            Self::X8 => write!(f, "s0"),
            Self::X9 => write!(f, "s1"),
            Self::X10 => write!(f, "a0"),
            Self::X11 => write!(f, "a1"),
            Self::X12 => write!(f, "a2"),
            Self::X13 => write!(f, "a3"),
            Self::X14 => write!(f, "a4"),
            Self::X15 => write!(f, "a5"),
            Self::X16 => write!(f, "a6"),
            Self::X17 => write!(f, "a7"),
            Self::X18 => write!(f, "s2"),
            Self::X19 => write!(f, "s3"),
            Self::X20 => write!(f, "s4"),
            Self::X21 => write!(f, "s5"),
            Self::X22 => write!(f, "s6"),
            Self::X23 => write!(f, "s7"),
            Self::X24 => write!(f, "s8"),
            Self::X25 => write!(f, "s9"),
            Self::X26 => write!(f, "s10"),
            Self::X27 => write!(f, "s11"),
            Self::X28 => write!(f, "t3"),
            Self::X29 => write!(f, "t4"),
            Self::X30 => write!(f, "t5"),
            Self::X31 => write!(f, "t6"),
        }
    }
}

impl fmt::Debug for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::X0 => write!(f, "x0/zero"),
            Self::X1 => write!(f, "x1/ra"),
            Self::X2 => write!(f, "x2/sp"),
            Self::X3 => write!(f, "x3/gp"),
            Self::X4 => write!(f, "x4/tp"),
            Self::X5 => write!(f, "x5/t0"),
            Self::X6 => write!(f, "x6/t1"),
            Self::X7 => write!(f, "x7/t2"),
            Self::X8 => write!(f, "x8/s0/fp"),
            Self::X9 => write!(f, "x9/s1"),
            Self::X10 => write!(f, "x10/a0"),
            Self::X11 => write!(f, "x11/a1"),
            Self::X12 => write!(f, "x12/a2"),
            Self::X13 => write!(f, "x13/a3"),
            Self::X14 => write!(f, "x14/a4"),
            Self::X15 => write!(f, "x15/a5"),
            Self::X16 => write!(f, "x16/a6"),
            Self::X17 => write!(f, "x17/a7"),
            Self::X18 => write!(f, "x18/s2"),
            Self::X19 => write!(f, "x19/s3"),
            Self::X20 => write!(f, "x20/s4"),
            Self::X21 => write!(f, "x21/s5"),
            Self::X22 => write!(f, "x22/s6"),
            Self::X23 => write!(f, "x23/s7"),
            Self::X24 => write!(f, "x24/s8"),
            Self::X25 => write!(f, "x25/s9"),
            Self::X26 => write!(f, "x26/s10"),
            Self::X27 => write!(f, "x27/s11"),
            Self::X28 => write!(f, "x28/t3"),
            Self::X29 => write!(f, "x29/t4"),
            Self::X30 => write!(f, "x30/t5"),
            Self::X31 => write!(f, "x31/t6"),
        }
    }
}

fn new_register(src: &[char]) -> Option<Register> {
    match src {
        ['t', '0'] => Some(Register::X5),
        ['t', '1'] => Some(Register::X6),
        ['t', '2'] => Some(Register::X7),
        ['t', '3'] => Some(Register::X28),
        ['t', '4'] => Some(Register::X29),
        ['t', '5'] => Some(Register::X30),
        ['a', '0'] => Some(Register::X10),
        ['a', '1'] => Some(Register::X11),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct Li {
    pub register: Register,
    pub immediate: Immediate,
}

impl fmt::Display for Li {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "li {}, {}", self.register, self.immediate)
    }
}

fn new_li(src: &[char]) -> Li {
    let imm = src
        .iter()
        .skip(4)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Li {
        register: new_register(&src[..2]).unwrap(),
        immediate: new_immediate(&imm).unwrap(),
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Immediate {
    pub value: i64,
}

impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Immediate {
    pub const ZERO: Immediate = Immediate { value: 0 };
}

impl std::ops::Add for Immediate {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            value: self.value + other.value,
        }
    }
}

impl Immediate {
    pub fn to_ne_bytes(&self) -> [u8; 8] {
        self.value.to_ne_bytes()
    }
}

impl From<[u8; 4]> for Immediate {
    fn from(word: [u8; 4]) -> Self {
        let bytes = <[u8; 8]>::try_from(
            [0u8, 0u8, 0u8, 0u8]
                .iter()
                .chain(word.iter())
                .copied()
                .collect::<Vec<_>>(),
        )
        .unwrap();
        Self {
            value: i64::from_ne_bytes(bytes),
        }
    }
}

impl From<[u8; 8]> for Immediate {
    fn from(doubleword: [u8; 8]) -> Self {
        Self {
            value: i64::from_ne_bytes(doubleword),
        }
    }
}

impl From<u8> for Immediate {
    fn from(byte: u8) -> Self {
        let bytes = <[u8; 8]>::try_from(
            [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
                .iter()
                .chain(std::iter::once(&byte))
                .copied()
                .collect::<Vec<_>>(),
        )
        .unwrap();
        Self {
            value: i64::from_ne_bytes(bytes),
        }
    }
}

fn new_immediate(src: &[char]) -> Result<Immediate, <i64 as std::str::FromStr>::Err> {
    let value = match src {
        ['-', rem @ ..] => -rem.iter().collect::<String>().parse::<i64>()?,
        ['0', 'x', rem @ ..] => i64::from_str_radix(&rem.iter().collect::<String>(), 16).unwrap(),
        _ => src.iter().collect::<String>().parse()?,
    };

    Ok(Immediate { value })
}

#[derive(Debug, Clone)]
pub struct La {
    pub register: Register,
    pub label: Label,
}

impl fmt::Display for La {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "la {}, {}", self.register, self.label)
    }
}

fn new_la(src: &[char]) -> La {
    La {
        register: new_register(&src[..2]).unwrap(),
        label: new_label(&src[4..]),
    }
}

/// Load address type
#[derive(Debug, Clone)]
pub struct Lat {
    pub register: Register,
    pub label: Label,
}

impl fmt::Display for Lat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "lat {}, {}", self.register, self.label)
    }
}

fn new_lat(src: &[char]) -> Lat {
    Lat {
        register: new_register(&src[..2]).unwrap(),
        label: new_label(&src[4..]),
    }
}

#[derive(Debug, Clone)]
pub struct LabelInstruction {
    pub tag: Label,
}

impl fmt::Display for LabelInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:", self.tag)
    }
}

fn new_label_instruction(src: &[char]) -> LabelInstruction {
    assert_eq!(src[src.len() - 1], ':', "{src:?}");
    LabelInstruction {
        tag: new_label(&src[..src.len() - 1]),
    }
}

#[derive(Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Label {
    pub tag: String,
}
impl Label {
    /// Creates a thread local instance of the label.
    pub fn thread_local(&self, hart: u8) -> Self {
        Self {
            tag: format!("{}_{hart}", self.tag),
        }
    }
}
impl fmt::Debug for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.tag)
    }
}
impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.tag)
    }
}
impl From<&str> for Label {
    fn from(s: &str) -> Self {
        Self {
            tag: String::from(s),
        }
    }
}

fn new_label(src: &[char]) -> Label {
    Label {
        tag: src.iter().collect(),
    }
}

/// Control and Status Register Read
#[derive(Debug, Clone)]
pub struct Csrr {
    pub dest: Register,
    pub src: Csr,
}

impl fmt::Display for Csrr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "csrr {}, {}", self.dest, self.src)
    }
}

fn new_csrr(src: &[char]) -> Csrr {
    Csrr {
        dest: new_register(&src[0..2]).unwrap(),
        src: new_csr(&src[4..]),
    }
}

/// Control and Status Register
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Csr {
    Mhartid,
}

impl fmt::Display for Csr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[allow(unreachable_patterns)]
        match self {
            Csr::Mhartid => write!(f, "mhartid"),
            _ => todo!(),
        }
    }
}

fn new_csr(src: &[char]) -> Csr {
    match src {
        ['m', 'h', 'a', 'r', 't', 'i', 'd'] => Csr::Mhartid,
        _ => todo!(),
    }
}

#[derive(Debug, Clone)]
pub struct Bnez {
    pub src: Register,
    pub dest: Label,
}

impl fmt::Display for Bnez {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "bnez {}, {}", self.src, self.dest)
    }
}

fn new_bnez(src: &[char]) -> Bnez {
    let dest = src
        .iter()
        .skip(4)
        .take_while(|&&c| c != ' ')
        .copied()
        .collect::<Vec<_>>();
    Bnez {
        src: new_register(&src[0..2]).unwrap(),
        dest: new_label(&dest),
    }
}

/// Jump
#[derive(Debug, Clone)]
pub struct J {
    dest: Label,
}

impl fmt::Display for J {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "j {}", self.dest)
    }
}

fn new_j(src: &[char]) -> J {
    J {
        dest: new_label(src),
    }
}

#[derive(Debug, Clone)]
pub struct Global {
    pub tag: Label,
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, ".global {}", self.tag)
    }
}

fn new_global(src: &[char]) -> Global {
    Global {
        tag: new_label(src),
    }
}

#[derive(Debug, Clone)]
pub struct Wfi;

impl fmt::Display for Wfi {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "wfi")
    }
}
