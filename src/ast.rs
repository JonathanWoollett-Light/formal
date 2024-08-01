use std::alloc::{alloc, Layout};
use std::fmt;
use std::ptr::{write, NonNull};

#[derive(Debug)]
pub struct AstNode {
    pub prev: Option<NonNull<AstNode>>,
    pub this: Instruction,
    pub next: Option<NonNull<AstNode>>,
}

pub fn new_ast(src: &[char]) -> Option<NonNull<AstNode>> {
    let mut front_opt = None;
    let mut a = 0;
    let mut b = 0;
    while b < src.len() {
        if src[b] == '\n' {
            alloc_node(&src[a..b], &mut front_opt);
            a = b + 1;
        }
        b += 1;
    }
    alloc_node(&src[a..b], &mut front_opt);

    let mut first = None;
    while let Some(current) = front_opt {
        first = Some(current);
        front_opt = unsafe { current.as_ref().prev };
    }
    first
}

fn alloc_node(mut src: &[char], front_opt: &mut Option<NonNull<AstNode>>) {
    let mut i = 0;
    src = loop {
        match src.get(i) {
            None => return,
            Some(' ') => {}
            Some(_) => break &src[i..],
        }
        i += 1;
    };
    let instr = match src {
        ['#', '!'] => Instruction::Fail(Fail),
        ['#', ..] => return,
        _ => new_instruction(src),
    };

    let nonnull = unsafe {
        let ptr = alloc(Layout::new::<AstNode>()).cast();
        write(
            ptr,
            AstNode {
                prev: *front_opt,
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
        _ => Instruction::Label(new_label_instruction(src)),
        x @ _ => todo!("{x:?}"),
    }
}

#[derive(Debug, Clone)]
pub struct Beqz {
    register: Register,
    label: Label,
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

fn new_blt(src: &[char]) -> Blt {
    Blt {
        lhs: new_register(&src[..2]).unwrap(),
        rhs: new_register(&src[4..6]).unwrap(),
        label: new_label(&src[8..]),
    }
}

#[derive(Debug, Clone)]
pub struct Addi {
    pub out: Register,
    pub lhs: Register,
    pub rhs: Immediate,
}

fn new_addi(src: &[char]) -> Addi {
    Addi {
        out: new_register(&src[0..2]).unwrap(),
        lhs: new_register(&src[4..6]).unwrap(),
        rhs: new_immediate(&src[8..]).unwrap(),
    }
}

#[derive(Debug, Clone)]
pub struct Lw {
    pub to: Register,
    pub from: Register,
    pub offset: Offset,
}

fn new_lw(src: &[char]) -> Lw {
    let to = new_register(&src[..2]).unwrap();
    for i in 4..src.len() {
        if src[i] == '(' {
            return Lw {
                to,
                from: new_register(&src[i + 1..src.len() - 1]).unwrap(),
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

fn new_offset(src: &[char]) -> Result<Offset, <i64 as std::str::FromStr>::Err> {
    Ok(Offset {
        value: if src.len() == 0 {
            Immediate { value: 0 }
        } else {
            new_immediate(src)?
        },
    })
}

#[derive(Debug, Clone)]
pub struct Fail;

#[derive(Debug, Clone)]
pub struct Data;

#[derive(Clone)]
pub struct Ascii {
    string: Vec<u8>,
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
    assert_eq!(src[0], '"');
    assert_eq!(src[src.len() - 1], '"');
    Ascii {
        string: src[1..src.len() - 1].iter().map(|c| *c as u8).collect(),
    }
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

impl fmt::Debug for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::X0 => write!(f,"x0/zero"),
            Self::X1 => write!(f,"x1/ra"),
            Self::X2 => write!(f,"x2/sp"),
            Self::X3 => write!(f,"x3/gp"),
            Self::X4 => write!(f,"x4/tp"),
            Self::X5 => write!(f,"x5/t0"),
            Self::X6 => write!(f,"x6/t1"),
            Self::X7 => write!(f,"x7/t2"),
            Self::X8 => write!(f,"x8/s0/fp"),
            Self::X9 => write!(f,"x9/s1"),
            Self::X10 => write!(f,"x10/a0"),
            Self::X11 => write!(f,"x11/a1"),
            Self::X12 => write!(f,"x12/a2"),
            Self::X13 => write!(f,"x13/a3"),
            Self::X14 => write!(f,"x14/a4"),
            Self::X15 => write!(f,"x15/a5"),
            Self::X16 => write!(f,"x16/a6"),
            Self::X17 => write!(f,"x17/a7"),
            Self::X18 => write!(f,"x18/s2"),
            Self::X19 => write!(f,"x19/s3"),
            Self::X20 => write!(f,"x20/s4"),
            Self::X21 => write!(f,"x21/s5"),
            Self::X22 => write!(f,"x22/s6"),
            Self::X23 => write!(f,"x23/s7"),
            Self::X24 => write!(f,"x24/s8"),
            Self::X25 => write!(f,"x25/s9"),
            Self::X26 => write!(f,"x26/s10"),
            Self::X27 => write!(f,"x27/s11"),
            Self::X28 => write!(f,"x28/t3"),
            Self::X29 => write!(f,"x29/t4"),
            Self::X30 => write!(f,"x30/t5"),
            Self::X31 => write!(f,"x31/t6"),
            _ => todo!()
        }
    }
}

fn new_register(src: &[char]) -> Option<Register> {
    match src {
        ['t', '0'] => Some(Register::X5),
        ['t', '1'] => Some(Register::X6),
        ['t', '2'] => Some(Register::X7),
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

fn new_li(src: &[char]) -> Li {
    Li {
        register: new_register(&src[..2]).unwrap(),
        immediate: new_immediate(&src[4..]).unwrap(),
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Immediate {
    pub value: u64,
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
            [0, 0, 0, 0]
                .iter()
                .chain(word.iter())
                .copied()
                .collect::<Vec<_>>(),
        )
        .unwrap();
        Self {
            value: u64::from_be_bytes(bytes),
        }
    }
}

fn new_immediate(src: &[char]) -> Result<Immediate, <u64 as std::str::FromStr>::Err> {
    let value = match src {
        ['0', 'x', rem @ ..] => u64::from_str_radix(&rem.iter().collect::<String>(), 16).unwrap(),
        _ => src.iter().collect::<String>().parse()?,
    };

    Ok(Immediate { value })
}

#[derive(Debug, Clone)]
pub struct La {
    pub register: Register,
    pub label: Label,
}

fn new_la(src: &[char]) -> La {
    La {
        register: new_register(&src[..2]).unwrap(),
        label: new_label(&src[4..]),
    }
}

#[derive(Debug, Clone)]
pub struct LabelInstruction {
    pub tag: Label,
}

fn new_label_instruction(src: &[char]) -> LabelInstruction {
    assert_eq!(src[src.len() - 1], ':', "{src:?}");
    LabelInstruction {
        tag: new_label(&src[..src.len() - 1]),
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Label {
    pub tag: String,
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

fn new_csrr(src: &[char]) -> Csrr {
    Csrr {
        dest: new_register(&src[0..2]).unwrap(),
        src: new_csr(&src[4..]),
    }
}

/// Control and Status Register
#[derive(Debug, Clone)]
pub enum Csr {
    Mhartid,
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

fn new_bnez(src: &[char]) -> Bnez {
    Bnez {
        src: new_register(&src[0..2]).unwrap(),
        dest: new_label(&src[4..]),
    }
}

#[derive(Debug, Clone)]
pub struct J {
    dest: Label,
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

fn new_global(src: &[char]) -> Global {
    Global {
        tag: new_label(src),
    }
}

#[derive(Debug, Clone)]
pub struct Wfi;
