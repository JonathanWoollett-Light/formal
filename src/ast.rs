use std::alloc::{alloc, Layout};
use std::collections::HashMap;
use std::fmt;
use std::fs::read_to_string;
use std::path::PathBuf;
use std::ptr::{write, NonNull};

#[derive(Debug)]
pub struct AstNode {
    pub prev: Option<NonNull<AstNode>>,
    pub value: AstValue,
    pub next: Option<NonNull<AstNode>>,
}

#[derive(Debug, Clone)]
pub struct AstValue {
    pub span: Span,
    pub this: Instruction,
}

impl AsRef<AstValue> for AstNode {
    fn as_ref(&self) -> &AstValue {
        &self.value
    }
}

/// A stable, pointer-free identifier for an AST node: its position in program
/// order (the order `root -> next -> next -> ...` visits nodes). Because it is a
/// plain index rather than an address, it serializes and compares identically on
/// any process, which is what lets a `Continuation` (the parallel verifier's
/// frontier item) cross a thread or a cluster node, and what lets the verifier's
/// accumulators be keyed by something the determinism contract (DEVELOPMENT.md
/// §4.3: order by stable keys, never by pointer) permits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AstNodeId(pub u32);

/// A read-only view over a verified-program AST that maps between an
/// [`AstNodeId`] and the live node pointer. The AST is a `None`-terminated
/// linked list of [`AstNode`]s (built by [`new_ast`], optionally relaid-out by
/// [`crate::compress`]); this walks it once in program order so `id -> pointer`
/// is an array index and `pointer -> id` is a hash lookup.
///
/// It holds raw node pointers and so is neither `Send` nor `Sync`; in the
/// distributed design each process builds its own `Ast` from its own replica of
/// the (immutable) AST, and only the `AstNodeId`s ever travel between processes.
pub struct Ast {
    nodes: Vec<NonNull<AstNode>>,
    ids: HashMap<NonNull<AstNode>, AstNodeId>,
}

// SAFETY: `Ast` is a read-only view built once and never mutated; sharing `&Ast`
// across the verifier's worker threads only ever reads the (immutable) AST, so it
// is sound to send/share. The raw node pointers are dereferenced read-only and
// the AST outlives the parallel search (the caller guarantees this, as for
// `Explorerer::new`).
unsafe impl Send for Ast {}
unsafe impl Sync for Ast {}

impl Ast {
    /// Indexes the AST reachable from `root` in program order.
    pub fn index(root: Option<NonNull<AstNode>>) -> Self {
        let mut nodes = Vec::new();
        let mut ids = HashMap::new();
        let mut next = root;
        // SAFETY: `root` heads a valid `None`-terminated AST list (see
        // `new_ast`); every node is live for the duration of verification.
        unsafe {
            while let Some(node) = next {
                let id = AstNodeId(nodes.len() as u32);
                nodes.push(node);
                ids.insert(node, id);
                next = node.as_ref().next;
            }
        }
        Self { nodes, ids }
    }

    /// The node pointer for `id`, or `None` if `id` is out of range.
    pub fn resolve(&self, id: AstNodeId) -> Option<NonNull<AstNode>> {
        self.nodes.get(id.0 as usize).copied()
    }

    /// The id for `node`, or `None` if `node` is not part of this AST.
    pub fn id_of(&self, node: NonNull<AstNode>) -> Option<AstNodeId> {
        self.ids.get(&node).copied()
    }

    /// The first node in program order (the verifier's entry point), if any.
    pub fn head(&self) -> Option<NonNull<AstNode>> {
        self.nodes.first().copied()
    }

    /// The number of nodes in the AST.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the AST has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

// TODO It should really just be a `Range<usize>` with the starting byte and ending byte, `row` and `column` should then be calculated.
#[derive(Debug, Clone)]
pub struct Span {
    pub path: PathBuf,
    pub span: std::ops::Range<usize>,
}
impl Span {
    /// Returns starting row.
    fn row(&self) -> Result<usize, std::io::Error> {
        Ok(read_to_string(&self.path)?
            .chars()
            .take(self.span.start)
            .filter(|c| *c == '\n')
            .count()
            + 1)
    }
    /// Returns starting column.
    fn column(&self) -> Result<usize, std::io::Error> {
        Ok(read_to_string(&self.path)?
            .chars()
            .skip(self.span.start)
            .take_while(|c| *c != '\n')
            .count()
            + 1)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.path.display(),
            self.row().unwrap(),
            self.column().unwrap()
        )
    }
}

pub fn new_ast(src: &[char], path: PathBuf) -> Option<NonNull<AstNode>> {
    let mut front_opt = None;
    let mut a = 0;
    let mut b = 0;
    #[cfg(debug_assertions)]
    let mut check = (0..100_000).into_iter();
    while b < src.len() {
        debug_assert!(check.next().is_some());

        // See https://stackoverflow.com/questions/1761051/difference-between-n-and-r
        #[cfg(target_os = "windows")]
        let cond = matches!(src.get(b..=b + 1), Some(['\r', '\n']));

        #[cfg(target_os = "linux")]
        let cond = src[b] == '\n';

        if cond {
            alloc_node(
                &src[a..b],
                &mut front_opt,
                Span {
                    path: path.clone(),
                    span: a..b,
                },
            );
            a = b + 1;
            #[cfg(target_os = "windows")]
            {
                a += 1;
            }
        }
        b += 1;
    }
    alloc_node(&src[a..b], &mut front_opt, Span { path, span: a..b });

    let mut first = None;
    #[cfg(debug_assertions)]
    let mut inner_check = (0..1000).into_iter();
    while let Some(current) = front_opt {
        debug_assert!(inner_check.next().is_some());
        first = Some(current);
        front_opt = unsafe { current.as_ref().prev };
    }
    first
}

fn alloc_node(mut src: &[char], front_opt: &mut Option<NonNull<AstNode>>, span: Span) {
    let mut i = 0;
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    src = loop {
        debug_assert!(check.next().is_some());
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
        ['#', '&', ' ', rem @ ..] => Instruction::Lat(new_lat(rem)),
        ['#', '@', ' ', rem @ ..] => Instruction::Region(new_region(rem)),
        ['#', ..] => return,
        _ => {
            let mut out = None;
            // Get all characters until finding a comment
            'outer: for j in 0..src.len() {
                if src[j] == '#' {
                    // Skip all spaces that precede the comment seperator
                    for k in (0..j).rev() {
                        if src[k] != ' ' {
                            out = Some(new_instruction(&src[0..=k]));
                            break 'outer;
                        }
                    }
                    unreachable!();
                }
            }
            // Unwrap in case of comment or create new in case of no comment
            out.unwrap_or(new_instruction(&src[0..]))
        }
    };

    let nonnull = unsafe {
        let ptr = alloc(Layout::new::<AstNode>()).cast();
        write(
            ptr,
            AstNode {
                prev: *front_opt,
                value: AstValue { span, this: instr },
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
    Ecall(Ecall),
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
    Beq(Beq),
    Region(Region),
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
        ['e', 'c', 'a', 'l', 'l'] => Instruction::Ecall(Ecall),
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
            Ecall(ecall) => write!(f, "{ecall}"),
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
            Beq(beq) => write!(f, "{beq}"),
            Region(region) => write!(f, "{region}"),
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

    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    let label = loop {
        debug_assert!(check.next().is_some());
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

    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    let cast = loop {
        debug_assert!(check.next().is_some());
        match src.get(j) {
            None => {
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

/// Declares a memory region the program may access: `#@ <start> <end> <perms>`.
///
/// `start`/`end` bound the region's addresses (`end` exclusive, so a heap
/// allocator declares `#@ <base> <base + size> rw` for each allocation it makes)
/// and may be immediates or registers; a register bound takes the register's
/// (possibly under-determined, symbolic) value when the declaration executes.
/// `perms` is `r` (read), `w` (write) or `rw`. Every raw-address memory access
/// must fall within a declared region (or a section described by the system
/// configuration) to verify.
#[derive(Debug, Clone)]
pub struct Region {
    pub start: RegionBound,
    pub end: RegionBound,
    pub permissions: RegionPermissions,
}

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#@ {} {} {}", self.start, self.end, self.permissions)
    }
}

/// One bound of a [`Region`]: a literal address or a register holding one.
#[derive(Debug, Clone)]
pub enum RegionBound {
    Immediate(Immediate),
    Register(Register),
}

impl fmt::Display for RegionBound {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Immediate(immediate) => write!(f, "{immediate}"),
            Self::Register(register) => write!(f, "{register}"),
        }
    }
}

/// The access permissions a [`Region`] grants.
#[derive(Debug, Clone, Copy)]
pub enum RegionPermissions {
    Read,
    Write,
    ReadWrite,
}

impl fmt::Display for RegionPermissions {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Read => write!(f, "r"),
            Self::Write => write!(f, "w"),
            Self::ReadWrite => write!(f, "rw"),
        }
    }
}

fn new_region(src: &[char]) -> Region {
    // Three space-separated fields: `<start> <end> <perms>`.
    let mut fields = src.split(|c| *c == ' ').filter(|f| !f.is_empty());
    let start = new_region_bound(fields.next().unwrap());
    let end = new_region_bound(fields.next().unwrap());
    let permissions = match fields.next().unwrap() {
        ['r'] => RegionPermissions::Read,
        ['w'] => RegionPermissions::Write,
        ['r', 'w'] => RegionPermissions::ReadWrite,
        x => todo!("{x:?}"),
    };
    Region {
        start,
        end,
        permissions,
    }
}

fn new_region_bound(src: &[char]) -> RegionBound {
    // Registers start with a letter (`t0`…); immediates with a digit or `-`.
    match src.first() {
        Some(c) if c.is_ascii_alphabetic() => RegionBound::Register(new_register(src).unwrap()),
        _ => RegionBound::Immediate(new_immediate(src).unwrap()),
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
            let from = src
                .iter()
                .skip(i + 1)
                .take_while(|&&c| c != ')')
                .copied()
                .collect::<Vec<_>>();
            return Lb {
                to,
                from: new_register(&from).unwrap(),
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
    let (i, j) = parse_store(src);
    Sb {
        from,
        to: new_register(&src[i + 1..j]).unwrap(),
        offset: new_offset(&src[4..i]).unwrap(),
    }
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
    let (i, j) = parse_store(src);
    Sw {
        from,
        to: new_register(&src[i + 1..j]).unwrap(),
        offset: new_offset(&src[4..i]).unwrap(),
    }
}

fn parse_store(src: &[char]) -> (usize, usize) {
    for i in 4..src.len() {
        if src[i] == '(' {
            for j in i..src.len() {
                if src[j] == ')' {
                    return (i, j);
                }
            }
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
        write!(f, "{}", self.value)
    }
}

fn new_offset(src: &[char]) -> Result<Offset, <i64 as std::str::FromStr>::Err> {
    Ok(Offset {
        value: if src.is_empty() {
            Immediate {
                radix: 10,
                value: 0,
            }
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

fn new_ascii(_src: &[char]) -> Ascii {
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

fn new_register(src: &[char]) -> Result<Register, Vec<char>> {
    match src {
        ['t', '0'] => Ok(Register::X5),
        ['t', '1'] => Ok(Register::X6),
        ['t', '2'] => Ok(Register::X7),
        ['t', '3'] => Ok(Register::X28),
        ['t', '4'] => Ok(Register::X29),
        ['t', '5'] => Ok(Register::X30),
        ['a', '0'] => Ok(Register::X10),
        ['a', '1'] => Ok(Register::X11),
        ['a', '2'] => Ok(Register::X12),
        ['a', '3'] => Ok(Register::X13),
        ['a', '4'] => Ok(Register::X14),
        ['a', '5'] => Ok(Register::X15),
        ['a', '6'] => Ok(Register::X16),
        ['a', '7'] => Ok(Register::X17),
        _ => Err(Vec::from(src)),
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
        register: new_register(&src[..2]).expect(&format!("{:?} {src:?}", &src[..2])),
        immediate: new_immediate(&imm).expect(&format!("{imm:?} {src:?}")),
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Immediate {
    pub radix: u8,
    pub value: i64,
}

impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.radix {
            10 => write!(f, "{}", self.value),
            16 => write!(f, "0x{:x}", self.value),
            _ => unreachable!(),
        }
    }
}

impl Immediate {
    pub fn to_ne_bytes(&self) -> [u8; 8] {
        self.value.to_ne_bytes()
    }
}

fn new_immediate(src: &[char]) -> Result<Immediate, <i64 as std::str::FromStr>::Err> {
    let (radix, value) = match src {
        ['-', '0', 'x', rem @ ..] => (
            16,
            -i64::from_str_radix(&rem.iter().collect::<String>(), 16).unwrap(),
        ),
        ['0', 'x', rem @ ..] => (
            16,
            i64::from_str_radix(&rem.iter().collect::<String>(), 16).unwrap(),
        ),
        ['-', rem @ ..] => (10, -rem.iter().collect::<String>().parse::<i64>()?),
        _ => (10, src.iter().collect::<String>().parse()?),
    };

    Ok(Immediate { radix, value })
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
        write!(f, "#& {}, {}", self.register, self.label)
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
    pub dest: Label,
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

/// `ecall`: the RISC-V environment-call (system-call) instruction. The verifier
/// does not model the call's effect (it is the boundary to the host/OS), so it
/// treats `ecall` as a no-op for checking; the system-call ABI lives entirely
/// in the registers the surrounding code sets (`a7` = number, `a0`-`a5` = args).
#[derive(Debug, Clone)]
pub struct Ecall;

impl fmt::Display for Ecall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ecall")
    }
}
