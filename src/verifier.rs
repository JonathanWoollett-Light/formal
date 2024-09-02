use crate::ast::*;
use std::alloc::Layout;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::hash::Hash;
use std::iter::once;
use std::ops::Range;
use std::ops::RangeInclusive;
use std::ptr;
use std::{
    alloc::alloc,
    collections::{HashMap, VecDeque},
    ptr::NonNull,
};
use tracing::error;
use tracing::info;
use tracing::trace;

/// Compile time size
fn size(t: &Type) -> usize {
    use Type::*;
    match t {
        U8 => 1,
        I8 => 1,
        U16 => 2,
        I16 => 2,
        U32 => 4,
        I32 => 4,
        U64 => 8,
        I64 => 8,
        List(items) => items.iter().map(size).sum(),
        _ => todo!(),
    }
}

/// The type to explore in order from best to worst.
fn type_list() -> Vec<Type> {
    vec![
        Type::U8,
        Type::I8,
        Type::U16,
        Type::I16,
        Type::U32,
        Type::I32,
        Type::U64,
        Type::I64,
    ]
}

use std::alloc::dealloc;
pub struct VerifierHarts {
    pub harts: u8,
    pub next: NextVerifierNode,
}

type NextVerifierNode = Vec<NonNull<VerifierNode>>;

#[derive(Debug, Clone, Copy)]
enum VerifierPrevNode {
    Branch(NonNull<VerifierNode>),
    Root(NonNull<VerifierHarts>),
}

impl VerifierPrevNode {
    unsafe fn next(&mut self) -> &mut NextVerifierNode {
        match self {
            VerifierPrevNode::Branch(branch) => &mut branch.as_mut().next,
            VerifierPrevNode::Root(root) => &mut root.as_mut().next,
        }
    }
}

/// We use a tree to trace the execution of the program,
/// then when conditions are required it can resolve them
/// by looking back at the trace.
pub struct VerifierNode {
    pub prev: VerifierPrevNode,
    pub hart: u8,
    pub node: NonNull<AstNode>,
    pub next: NextVerifierNode,
}
use std::iter::Peekable;

/// Localites in order of best to worst
fn locality_list() -> Vec<Locality> {
    vec![Locality::Thread, Locality::Global]
}

#[derive(Debug)]
struct MemoryMap {
    map: HashMap<Label, MemoryValue>,
}

impl MemoryMap {
    fn get_u8(&self, MemoryLocation { tag, offset }: &MemoryLocation) -> Option<MemoryValueU8> {
        let value = self.map.get(tag)?;
        value.get_u8(offset)
    }
    fn get_u32(&self, MemoryLocation { tag, offset }: &MemoryLocation) -> Option<MemoryValueU32> {
        let value = self.map.get(tag)?;
        value.get_u32(offset)
    }
    fn get_u64(&self, MemoryLocation { tag, offset }: &MemoryLocation) -> Option<DoubleWordValue> {
        let value = self.map.get(tag)?;
        value.get_u64(offset)
    }
    fn set_u8(&mut self, MemoryLocation { tag, offset }: &MemoryLocation, value: u8) {
        let existing = self.map.get_mut(tag).unwrap();
        existing.set_u8(offset, value);
    }
    fn set_u32(&mut self, MemoryLocation { tag, offset }: &MemoryLocation, value: u32) {
        let existing = self.map.get_mut(tag).unwrap();
        match existing {
            MemoryValue::U32(word) => {
                if let Some(ord) = offset.compare(&MemoryValueI64::ZERO) {
                    if ord == Ordering::Equal {
                        word.start = value;
                        word.stop = value;
                    } else {
                        todo!();
                    }
                } else {
                    todo!();
                }
            }
            _ => todo!(),
        }
    }
    // TODO This should be improved, I'm pretty sure the current approach is bad.
    // In setting a type type we need to set many sublabels for the sub-types.
    fn set_type(
        &mut self,
        value: &Type,
        tag_iter: &mut Peekable<impl Iterator<Item = Label>>, // Iterator to generate unique tags.
    ) -> (Label, ProgramConfiguration) {
        let mut vec = Vec::new();
        vec.push((None, value.clone()));
        let mut right = 0;
        // Fill queue with all types
        while right < vec.len() {
            if let Type::List(list) = &vec[right].1 {
                for offset in 0..list.len() {
                    let t = vec[right].1.list_mut()[offset].clone();
                    vec.insert(right + offset + 1, (None, t));
                }
            }
            right += 1;
        }

        let mut left = right;
        let mut subtypes = ProgramConfiguration::new();
        while left > 0 {
            left -= 1;
            if let (None, Type::List(_)) = &vec[left] {
                let memory_types = vec
                    .drain(left + 1..right)
                    .map(|(addr, t)| MemoryValueType {
                        type_value: FlatType::from(&t),
                        addr,
                        length: if let Type::List(l) = &t { l.len() } else { 0 },
                        locality: Locality::Thread,
                    })
                    .collect::<Vec<_>>();
                let tag = tag_iter.next().unwrap();
                vec[left].0 = Some(tag.clone());

                // Insert collect subtypes types
                let subtypes_list = memory_types
                    .iter()
                    .map(|_| MemoryValueType::type_of())
                    .collect();
                subtypes.insert(tag.clone(), (Locality::Thread, Type::List(subtypes_list)));
                // Insert subtypes into memory.
                self.map
                    .insert(tag.clone(), MemoryValue::Types(memory_types));
                right = left;
            }
        }

        let final_tag = tag_iter.next().unwrap();
        match vec.remove(0) {
            (addr @ Some(_), Type::List(list)) => {
                self.map.insert(
                    final_tag.clone(),
                    MemoryValue::Type(MemoryValueType {
                        type_value: FlatType::List,
                        addr,
                        length: list.len(),
                        locality: Locality::Thread,
                    }),
                );
            }
            (None, t) => {
                self.map.insert(
                    final_tag.clone(),
                    MemoryValue::Type(MemoryValueType {
                        type_value: FlatType::from(t),
                        addr: None,
                        length: 0,
                        locality: Locality::Thread,
                    }),
                );
            }
            _ => unreachable!(),
        }

        (final_tag, subtypes)
    }
}

#[derive(Debug)]
struct State {
    // Each hart has its own registers.
    registers: Vec<HashMap<Register, RegisterValue>>,
    memory: MemoryMap,
    configuration: ProgramConfiguration,
}

impl State {
    fn new(harts: u8, configuration: &ProgramConfiguration) -> Self {
        let mut memory = MemoryMap {
            map: HashMap::new(),
        };

        // Initialize bss
        for (k, (_l, t)) in configuration.0.iter() {
            memory.map.insert(k.clone(), MemoryValue::from(t.clone()));
        }

        Self {
            registers: (0..harts).map(|_| HashMap::new()).collect(),
            memory,
            configuration: configuration.clone(),
        }
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
struct MemoryLocation {
    tag: Label,
    offset: MemoryValueI64,
}

impl From<Label> for MemoryLocation {
    fn from(tag: Label) -> Self {
        Self {
            tag,
            offset: MemoryValueI64::ZERO,
        }
    }
}

// It is possible to technically store a 4 byte virtual value (e.g. DATA_END)
// then edit 2 bytes of it. So we will need additional complexity to support this case
#[derive(Debug)]
enum MemoryValue {
    U8(MemoryValueU8),
    Type(MemoryValueType),
    Types(Vec<MemoryValueType>),
    U64(MemoryValueU64),
    U32(MemoryValueU32),
    List(Vec<MemoryValue>),
    I8(MemoryValueI8),
    I64(MemoryValueI64),
}

#[derive(Debug, Clone)]
struct MemoryValueI8 {
    start: i8,
    stop: i8,
}
impl From<i8> for MemoryValueI8 {
    fn from(x: i8) -> Self {
        Self { start: x, stop: x }
    }
}
impl Add for MemoryValueI8 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}

impl MemoryValueI8 {
    const ZERO: Self = Self { start: 0, stop: 0 };
    fn get_i8(&self, i: usize) -> Option<MemoryValueI8> {
        if i > 0 {
            return None;
        }
        Some(self.clone())
    }
    fn set_i8(&mut self, i: usize, n: i8) {
        assert!(i > 0);
        self.start = n;
        self.stop = n;
    }
    fn value(&self) -> Option<i8> {
        (self.start == self.stop).then_some(self.start)
    }
}
impl Compare for MemoryValueI8 {
    fn compare(&self, other: &Self) -> Option<Ordering> {
        match (self.start.cmp(&other.start), self.stop.cmp(&other.stop)) {
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            (Ordering::Greater, Ordering::Greater) => Some(Ordering::Greater),
            (Ordering::Less, Ordering::Less) => Some(Ordering::Less),
            _ => todo!(),
        }
    }
}

trait Compare {
    fn compare(&self, other: &Self) -> Option<Ordering>;
}

#[derive(Debug, Clone)]
struct MemoryValueU8 {
    start: u8,
    stop: u8,
}
impl From<u8> for MemoryValueU8 {
    fn from(x: u8) -> Self {
        Self { start: x, stop: x }
    }
}
impl Add for MemoryValueU8 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}
impl Compare for MemoryValueU8 {
    fn compare(&self, other: &Self) -> Option<Ordering> {
        match (self.start.cmp(&other.start), self.stop.cmp(&other.stop)) {
            (Ordering::Less, Ordering::Less) => Some(Ordering::Less),
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            (Ordering::Greater, Ordering::Greater) => Some(Ordering::Greater),
            _ => todo!(),
        }
    }
}
impl MemoryValueU8 {
    const ZERO: Self = Self { start: 0, stop: 0 };

    fn get_u8(&self, i: &MemoryValueI64) -> Option<MemoryValueU8> {
        if i.start == i.stop {
            let i = usize::try_from(i.start).unwrap();
            if i > 0 {
                return None;
            }
            Some(self.clone())
        } else {
            todo!()
        }
    }
    fn set_u8(&mut self, i: &MemoryValueI64, n: u8) {
        if let Some(ord) = i.compare(&MemoryValueI64::ZERO) {
            if ord == Ordering::Equal {
                self.start = n;
                self.stop = n;
            } else {
                todo!()
            }
        } else {
            todo!()
        }
    }
    fn value(&self) -> Option<u8> {
        (self.start == self.stop).then_some(self.start)
    }
}

impl From<&Immediate> for RegisterValue {
    fn from(immediate: &Immediate) -> Self {
        // Store as the smallest value that can contain `immediate`.
        let v = immediate.value as i128;
        const U8_MIN: i128 = u8::MIN as i128;
        const U8_MAX: i128 = u8::MAX as i128;
        const U32_MIN: i128 = u32::MIN as i128;
        const U32_MAX: i128 = u32::MAX as i128;
        match v {
            U8_MIN..=U8_MAX => RegisterValue::U8(MemoryValueU8::from(v as u8)),
            U32_MIN..=U32_MAX => RegisterValue::U32(MemoryValueU32::from(v as u32)),
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
struct MemoryValueU32 {
    start: u32,
    stop: u32,
}
impl From<u32> for MemoryValueU32 {
    fn from(x: u32) -> Self {
        Self { start: x, stop: x }
    }
}
impl Compare for MemoryValueU32 {
    fn compare(&self, other: &Self) -> Option<Ordering> {
        match (self.start.cmp(&other.start), self.stop.cmp(&other.stop)) {
            (Ordering::Less, Ordering::Less) => Some(Ordering::Less),
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            (Ordering::Greater, Ordering::Greater) => Some(Ordering::Greater),
            _ => todo!(),
        }
    }
}

impl MemoryValueU32 {
    fn get_u8(&self, i: &MemoryValueI64) -> Option<MemoryValueU8> {
        if i.start == i.stop {
            let i = usize::try_from(i.start).unwrap();
            assert!(i < 4);
            if i > 3 {
                return None;
            }
            if self.start == self.stop {
                let byte = self.start.to_ne_bytes()[i];
                return Some(MemoryValueU8 {
                    start: byte,
                    stop: byte,
                });
            }
            todo!()
        } else {
            todo!()
        }
    }
    fn get_u32(&self, i: &MemoryValueI64) -> Option<MemoryValueU32> {
        if i.start == i.stop {
            let i = usize::try_from(i.start).unwrap();
            assert!(i < 1);
            if i > 0 {
                return None;
            }
            if self.start == self.stop {
                let word = self.start;
                return Some(MemoryValueU32 {
                    start: word,
                    stop: word,
                });
            }
            todo!()
        } else {
            todo!()
        }
    }
    fn value(&self) -> Option<u32> {
        (self.start == self.stop).then_some(self.start)
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
struct MemoryValueU64 {
    start: u64,
    stop: u64,
}
impl Compare for MemoryValueU64 {
    fn compare(&self, other: &Self) -> Option<Ordering> {
        match (self.start.cmp(&other.start), self.stop.cmp(&other.stop)) {
            (Ordering::Less, Ordering::Less) => Some(Ordering::Less),
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            (Ordering::Greater, Ordering::Greater) => Some(Ordering::Greater),
            _ => todo!(),
        }
    }
}
impl From<usize> for MemoryValueU64 {
    fn from(x: usize) -> Self {
        let y = u64::try_from(x).unwrap();
        Self { start: y, stop: y }
    }
}
impl From<u64> for MemoryValueU64 {
    fn from(x: u64) -> Self {
        Self { start: x, stop: x }
    }
}
impl Add for MemoryValueU64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}
impl From<MemoryValueU8> for MemoryValueU64 {
    fn from(x: MemoryValueU8) -> Self {
        Self {
            start: x.start as u64,
            stop: x.stop as u64,
        }
    }
}

#[derive(Debug, Hash, Clone, Copy)]
struct MemoryValueI64 {
    start: i64,
    stop: i64,
}
use std::fmt;
use std::ops::Div;
impl Div for MemoryValueI64 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        if self.start == self.stop {
            let a = self.start;
            if rhs.start == rhs.stop {
                let b = rhs.start;
                Self {
                    start: a / b,
                    stop: a / b,
                }
            } else {
                todo!()
            }
        } else {
            todo!()
        }
    }
}
impl Compare for MemoryValueI64 {
    fn compare(&self, other: &Self) -> Option<Ordering> {
        match (self.start.cmp(&other.start), self.stop.cmp(&other.stop)) {
            (Ordering::Less, Ordering::Less) => Some(Ordering::Less),
            (Ordering::Greater, Ordering::Greater) => Some(Ordering::Greater),
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            _ => todo!(),
        }
    }
}
impl fmt::Display for MemoryValueI64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..={}", self.start, self.stop)
    }
}

impl From<i64> for MemoryValueI64 {
    fn from(x: i64) -> Self {
        Self { start: x, stop: x }
    }
}
use std::cmp::Ordering;
use std::ops::Sub;
type Offset = MemoryValueI64;

impl TryFrom<usize> for MemoryValueI64 {
    type Error = <i64 as TryFrom<usize>>::Error;
    fn try_from(x: usize) -> Result<Self, Self::Error> {
        let y = i64::try_from(x)?;
        Ok(Self { start: y, stop: y })
    }
}
impl Add for MemoryValueI64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}
impl Sub for MemoryValueI64 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start - rhs.start,
            stop: self.stop - rhs.stop,
        }
    }
}
impl From<MemoryValueI8> for MemoryValueI64 {
    fn from(x: MemoryValueI8) -> Self {
        Self {
            start: x.start as i64,
            stop: x.stop as i64,
        }
    }
}
impl From<MemoryValueU8> for MemoryValueI64 {
    fn from(x: MemoryValueU8) -> Self {
        Self {
            start: x.start as i64,
            stop: x.stop as i64,
        }
    }
}
impl MemoryValueI64 {
    const ZERO: Self = Self { start: 0, stop: 0 };
    fn value(&self) -> Option<i64> {
        (self.start == self.stop).then_some(self.start)
    }
}

impl MemoryValueU64 {
    const ZERO: Self = Self { start: 0, stop: 0 };
    fn get_u64(&self, i: &MemoryValueI64) -> Option<DoubleWordValue> {
        if i.start == i.stop {
            let i = usize::try_from(i.start).unwrap();
            if i > 0 {
                return None;
            }
            Some(DoubleWordValue::Literal(self.clone()))
        } else {
            todo!()
        }
    }
    fn get_u8(&self, i: &MemoryValueI64) -> Option<MemoryValueU8> {
        if i.start == i.stop {
            let i = usize::try_from(i.start).unwrap();
            assert!(i < 8);
            if i > 7 {
                return None;
            }
            if self.start == self.stop {
                let byte = self.start.to_ne_bytes()[i];
                return Some(MemoryValueU8 {
                    start: byte,
                    stop: byte,
                });
            } else {
                todo!()
            }
        } else {
            todo!()
        }
    }
    fn value(&self) -> Option<u64> {
        (self.start == self.stop).then_some(self.start)
    }
}

impl From<&MemoryValue> for Type {
    fn from(mv: &MemoryValue) -> Self {
        match mv {
            MemoryValue::U8(_) => Type::U8,
            _ => todo!(),
        }
    }
}

impl From<Type> for MemoryValue {
    fn from(base: Type) -> Self {
        match base {
            Type::U8 => MemoryValue::U8(MemoryValueU8 {
                start: u8::MIN,
                stop: u8::MAX,
            }),
            Type::List(list) => {
                MemoryValue::List(list.into_iter().map(MemoryValue::from).collect())
            }
            _ => todo!(),
        }
    }
}

impl MemoryValue {
    fn get_u64(&self, i: &MemoryValueI64) -> Option<DoubleWordValue> {
        match self {
            Self::U32(_) => None,
            Self::U8(_) => None,
            Self::List(list) => {
                if let Some(exact) = i.value() {
                    let i = usize::try_from(exact).unwrap();
                    let mut pos = 0;
                    for j in 0..list.len() {
                        pos += size(&Type::from(&list[j]));
                        if pos > i {
                            let type_offset = MemoryValueI64::try_from(pos - i).unwrap();
                            return list[j].get_u64(&type_offset);
                        }
                    }
                    None
                } else {
                    todo!()
                }
            }
            _ => todo!(),
        }
    }
    fn get_u8(&self, i: &MemoryValueI64) -> Option<MemoryValueU8> {
        match self {
            Self::U32(word) => word.get_u8(i),
            Self::U8(byte) => byte.get_u8(i),
            Self::List(list) => {
                if let Some(exact) = i.value() {
                    let i = usize::try_from(exact).unwrap();
                    let mut pos = 0;
                    for j in 0..list.len() {
                        pos += size(&Type::from(&list[j]));
                        if pos > i {
                            let type_offset = MemoryValueI64::try_from(pos - i).unwrap();
                            return list[j].get_u8(&type_offset);
                        }
                    }
                    None
                } else {
                    todo!()
                }
            }
            _ => todo!(),
        }
    }
    fn set_u8(&mut self, i: &MemoryValueI64, n: u8) {
        match self {
            Self::List(list) => {
                let mut pos = MemoryValueI64::from(0);
                for j in 0..list.len() {
                    pos = pos + MemoryValueI64::try_from(size(&Type::from(&list[j]))).unwrap();
                    if let Some(ord) = pos.compare(i) {
                        if ord == Ordering::Greater {
                            let type_offset = pos - *i;
                            list[j].set_u8(&type_offset, n);
                        }
                    } else {
                        todo!()
                    }
                }
            }
            Self::U8(byte) => byte.set_u8(i, n),
            _ => todo!(),
        }
    }
    fn get_u32(&self, i: &MemoryValueI64) -> Option<MemoryValueU32> {
        match self {
            Self::U32(x) => x.get_u32(i),
            _ => todo!(),
        }
    }
}

#[derive(Debug)]
struct MemoryValueType {
    type_value: FlatType,
    addr: Option<Label>,
    length: usize,
    locality: Locality,
}
impl MemoryValueType {
    fn get_u64(&self, offset: &MemoryValueI64) -> Option<DoubleWordValue> {
        if let Some(exact) = offset.value() {
            match exact {
                ..0 => None,
                0 => todo!(),
                1 => self
                    .addr
                    .as_ref()
                    .map(|l| DoubleWordValue::Address(MemoryLocation::from(l))),
                2..=8 => todo!(),
                9 => Some(DoubleWordValue::Literal(MemoryValueU64::from(self.length))),
                10.. => None,
            }
        } else {
            todo!()
        }
    }
    fn type_of() -> Type {
        Type::List(vec![Type::U8, Type::U64, Type::U64, Type::U8])
    }
}

#[derive(Debug, Clone)]
enum RegisterValue {
    Address(MemoryLocation),
    Csr(CsrValue),
    U8(MemoryValueU8),
    U32(MemoryValueU32),
    U64(MemoryValueU64),
    I8(MemoryValueI8),
    I64(MemoryValueI64),
}
impl Compare for RegisterValue {
    fn compare(&self, other: &Self) -> Option<Ordering> {
        use RegisterValue::*;
        match (self, other) {
            (U8(a), U8(b)) => a.compare(b),
            (U32(a), U32(b)) => a.compare(b),
            (U64(a), U64(b)) => a.compare(b),
            _ => todo!(),
        }
    }
}
use std::ops::Add;
impl From<DoubleWordValue> for RegisterValue {
    fn from(x: DoubleWordValue) -> Self {
        match x {
            DoubleWordValue::Literal(y) => Self::U64(y),
            DoubleWordValue::Address(y) => Self::Address(y),
        }
    }
}
impl Add for RegisterValue {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        use RegisterValue::*;
        match (self, rhs) {
            (U8(a), U8(b)) => RegisterValue::U8(a + b),
            (Address(mut a), U8(b)) => {
                let c = MemoryValueI64::from(b);
                a.offset = a.offset + c;
                Self::Address(a)
            }
            (Address(mut a), I8(b)) => {
                let c = MemoryValueI64::from(b);
                a.offset = a.offset + c;
                Self::Address(a)
            }
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
enum DoubleWordValue {
    Literal(MemoryValueU64),
    Address(MemoryLocation),
}
impl From<&Label> for MemoryLocation {
    fn from(label: &Label) -> Self {
        MemoryLocation {
            tag: label.clone(),
            offset: Offset::ZERO,
        }
    }
}
impl From<Label> for RegisterValue {
    fn from(label: Label) -> Self {
        Self::Address(MemoryLocation {
            tag: label,
            offset: Offset::ZERO,
        })
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
enum CsrValue {
    Mhartid,
}

#[derive(Debug, Clone)]
struct ImmediateRange(RangeInclusive<Immediate>);
impl ImmediateRange {
    pub fn value(&self) -> Option<Immediate> {
        if self.0.start() == self.0.end() {
            Some(*self.0.start())
        } else {
            None
        }
    }
}
impl std::ops::Add for ImmediateRange {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(*self.0.start() + *other.0.start()..=*self.0.end() + *other.0.end())
    }
}
impl std::ops::Add<Immediate> for ImmediateRange {
    type Output = Self;

    fn add(self, other: Immediate) -> Self {
        Self(*self.0.start() + other..=*self.0.end() + other)
    }
}

// `wfi` is less racy than instructions like `sw` or `lw` so we could treat it more precisely
// and allow a larger domain of possible programs. But for now, we treat it like `sw` or
// `lw` this means there exist some valid usecases that this will report as invalid, and
// for valid use cases it will be slower as it needs to explore and validate paths it
// doesn't need to theoritically do.

/// Each execution path is based on the initial types assumed for each variables encountered and the locality assumed for each variable encountered.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramConfiguration(BTreeMap<Label, (Locality, Type)>);

impl ProgramConfiguration {
    fn append(&mut self, other: ProgramConfiguration) {
        for (label, ttype) in other.0.into_iter() {
            self.insert(label, ttype);
        }
    }
    fn insert(&mut self, key: Label, value: (Locality, Type)) {
        let res = self.0.insert(key, value);
        assert!(res.is_none());
    }
    fn get(&self, key: &Label) -> Option<&(Locality, Type)> {
        self.0.get(key)
    }
    fn new() -> Self {
        Self(BTreeMap::new())
    }
}

pub struct Explorerer {
    pub harts_range: Range<u8>,
    pub excluded: BTreeSet<ProgramConfiguration>,
    pub second_ptr: NonNull<AstNode>,
    pub roots: Vec<NonNull<VerifierHarts>>,
}

impl Explorerer {
    #[tracing::instrument(skip_all)]
    pub unsafe fn new_path(&mut self) -> ExplorererPath<'_> {
        // Record the initial types used for variables in this verification path.
        // Different harts can treat the same variables as different types, they have
        // different inputs and often follow different execution paths (effectively having a different AST).
        let configuration = ProgramConfiguration::new();

        // To remove uneeded code (e.g. a branch might always be true so we remove the code it skips)
        // we record all the AST instructions that get touched.
        let touched = BTreeSet::<NonNull<AstNode>>::new();

        let queue = self
            .roots
            .iter()
            .enumerate()
            .map(|(harts, root)| {
                // All harts are intiailized as `_start`.
                let mut prev = VerifierPrevNode::Root(*root);
                for hart in (0..=harts as u8).rev() {
                    let nonull = {
                        let ptr = alloc(Layout::new::<VerifierNode>()).cast();
                        ptr::write(
                            ptr,
                            VerifierNode {
                                prev,
                                hart,
                                node: self.second_ptr,
                                next: Vec::new(),
                            },
                        );
                        NonNull::new(ptr).unwrap()
                    };

                    prev.next().push(nonull);
                    prev = VerifierPrevNode::Branch(nonull);
                }
                let VerifierPrevNode::Branch(branch) = prev else {
                    unreachable!()
                };
                branch
            })
            .collect::<VecDeque<_>>();

        ExplorererPath {
            explorerer: self,
            configuration,
            touched,
            queue,
        }
    }
    #[tracing::instrument(skip_all)]
    pub unsafe fn new(ast: Option<NonNull<AstNode>>, harts_range: Range<u8>) -> Self {
        // You cannot verify a program that starts running on 0 harts.
        assert!(harts_range.start > 0);

        // Intial misc stuff
        let first = ast.unwrap().as_ref();
        let second_ptr = first.next.unwrap();
        let second = second_ptr.as_ref();
        match &first.this {
            Instruction::Global(Global { tag: start_tag }) => match &second.this {
                Instruction::Label(LabelInstruction { tag }) => {
                    assert_eq!(start_tag, tag);
                }
                _ => panic!("The second node must be the start label"),
            },
            _ => panic!("The first node must be the global start label definition"),
        }

        // To avoid retracing paths we record type combinations that have been found to be invalid.
        let excluded = BTreeSet::new();

        // The queue of nodes to explore along this path.
        // When we have 1..=3 harts the initial queue will contain
        // `[(_start, hart 0), (_start, hart 0), (_start, hart 0)]`
        // where each entry has a number of predeccessors e.g. `(_start, hart 1)`
        // up to the number of harts for that path.
        let roots = harts_range
            .clone()
            .map(|harts| {
                let ptr = alloc(Layout::new::<VerifierHarts>()).cast();
                ptr::write(
                    ptr,
                    VerifierHarts {
                        harts,
                        next: Vec::new(),
                    },
                );
                NonNull::new(ptr).unwrap()
            })
            .collect::<Vec<_>>();

        Self {
            harts_range,
            roots,
            second_ptr,
            excluded,
        }
    }
}


/// Represents a set of assumptions that lead to a given execution path (e.g. intial types of variables before they are explictly cast).
pub struct ExplorererPath<'a> {
    pub explorerer: &'a mut Explorerer,

    pub configuration: ProgramConfiguration,

    pub touched: BTreeSet<NonNull<AstNode>>,
    pub queue: VecDeque<NonNull<VerifierNode>>,
}

use itertools::Itertools;

/// Attempts to modify initial types to include a new variable, if it cannot add it,
/// existing is added to excluded, then returns true.
///
/// # Returns
///
/// - `true` the path is valid.
/// - `false` the path is invalid.
fn load_label(
    label: &Label,
    configuration: &mut ProgramConfiguration,
    excluded: &mut BTreeSet<ProgramConfiguration>,
    ttype: Option<Type>,        // The type to use for the variable if `Some(_)`.
    locality: Option<Locality>, // The locality to use for the variable if `Some(_)`.
) -> bool {
    // If the variable is already define, the type and locality must match any given.
    // E.g.
    // ```
    // define x local u8
    // define x local u8
    // ```
    // is valid, but
    // ```
    // define x local u8
    // define x local u16
    // ```
    // isn't.
    if let Some((existing_locality, existing_type)) = configuration.get(label) {
        if let Some(given_type) = ttype {
            if given_type != *existing_type {
                return false;
            }
        }
        if let Some(given_locality) = locality {
            if given_locality != *existing_locality {
                return false;
            }
        }
        return true;
    }

    // If a locality is given restrict exploration to this locality.
    let liter = match locality {
        Some(given) => vec![given],
        None => locality_list(),
    };
    // If a type is given restrict exploration to this type.
    let titer = match ttype {
        Some(given) => vec![given],
        None => type_list(),
    };

    // Search for a type and locality it can be that hasn't yet been excluded.
    for locality in liter {
        for ttype in titer.iter().cloned() {
            let mut config = configuration.clone();
            config.insert(label.clone(), (locality, ttype));

            if !excluded.contains(&config) {
                *configuration = config;
                return true;
            }
        }
    }
    return false;
}

pub enum ExplorePathResult<'a> {
    Valid {
        configuration: ProgramConfiguration,
        touched: BTreeSet<NonNull<AstNode>>,
    },
    Invalid {
        complete: bool,
        path: String,
        explanation: InvalidExplanation,
    },
    Continue(ExplorererPath<'a>),
}
impl<'a> ExplorePathResult<'a> {
    pub fn continued(self) -> Option<ExplorererPath<'a>> {
        match self {
            Self::Continue(c) => Some(c),
            _ => None,
        }
    }
}

use itertools::intersperse;
use tracing::debug;
impl<'a> ExplorererPath<'a> {
    #[tracing::instrument(skip_all)]
    pub unsafe fn next_step(
        Self {
            explorerer,
            mut configuration,
            mut touched,
            mut queue,
        }: Self,
    ) -> ExplorePathResult<'a> {
        trace!("excluded: {:?}", explorerer.excluded);
        debug!("configuration: {configuration:?}");

        debug!(
            "queue: [{}]",
            intersperse(
                queue.iter().map(|item| {
                    let mut current = item.as_ref().prev;
                    while let VerifierPrevNode::Branch(prev) = current {
                        current = prev.as_ref().prev;
                    }
                    let VerifierPrevNode::Root(root) = current else {
                        unreachable!()
                    };

                    let item_ref = item.as_ref();
                    format!(
                        "{{ hart: {}/{}, instruction: \"{}\" }}",
                        item_ref.hart + 1,
                        root.as_ref().harts,
                        item_ref.node.as_ref().this
                    )
                }),
                String::from(", ")
            )
            .collect::<String>()
        );

        let Some(branch_ptr) = queue.pop_front() else {
            return ExplorePathResult::Valid {
                configuration,
                touched,
            };
        };

        // If a variable is used that has not yet been defined, add the cheapest
        // possible data type for this variable to `types`. To avoid retreading the
        // steps of the same types, when the end of a invalid path is reached the
        // type map is added to `excluded`, we then check all values in `excluded`
        // and reduce the sets, e.g. (assuming the only data types are u8, u16 and u32)
        // if `[a:u8,b:u8]`, `[a:u8,b:u8]` and `[a:u8,b:u8]` are present in `excluded` then `[a:u8]` is added.
        let branch = branch_ptr.as_ref();
        let ast = branch.node;
        let hart = branch.hart;

        let mut current = branch_ptr.as_ref().prev;
        while let VerifierPrevNode::Branch(prev) = current {
            current = prev.as_ref().prev;
        }
        let VerifierPrevNode::Root(root) = current else {
            unreachable!()
        };
        let harts = root.as_ref().harts;
        debug!(
            "current: {{ hart: {}/{}, instruction: \"{}\" }}",
            hart + 1,
            harts,
            branch_ptr.as_ref().node.as_ref().this
        );

        // Record all the AST node that are reachable.
        touched.insert(ast);

        // Check the instruction is valid and make typing decisions.
        match &branch.node.as_ref().this {
            // Instructions which cannot be invalid and do not affect type exploration.
            Instruction::Unreachable(_)
            | Instruction::Li(_)
            | Instruction::Label(_)
            | Instruction::Addi(_)
            | Instruction::Blt(_)
            | Instruction::Csrr(_)
            | Instruction::Bne(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_)
            | Instruction::Wfi(_)
            | Instruction::Branch(_)
            | Instruction::Beq(_) => {}
            Instruction::Define(Define {
                label,
                locality,
                cast,
            }) => {
                if !load_label(
                    label,
                    &mut configuration,
                    &mut explorerer.excluded,
                    cast.clone(),
                    locality.clone(),
                ) {
                    return invalid_path(
                        explorerer,
                        configuration,
                        harts,
                        InvalidExplanation::La(label.clone()),
                    );
                }
            }
            Instruction::Lat(Lat { register: _, label }) => {
                if !load_label(
                    label,
                    &mut configuration,
                    &mut explorerer.excluded,
                    None,
                    None,
                ) {
                    return invalid_path(
                        explorerer,
                        configuration,
                        harts,
                        InvalidExplanation::Lat(label.clone()),
                    );
                }
            }
            Instruction::La(La { register: _, label }) => {
                if !load_label(
                    label,
                    &mut configuration,
                    &mut explorerer.excluded,
                    None,
                    None,
                ) {
                    return invalid_path(
                        explorerer,
                        configuration,
                        harts,
                        InvalidExplanation::La(label.clone()),
                    );
                }
            }
            // For any store we need to validate the destination is valid.
            Instruction::Sw(Sw {
                to,
                from: _,
                offset,
            }) => {
                // Collect the state.
                let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                let state = find_state(&record, root, harts, first_step, &configuration);

                // Check the destination is valid.
                match state.registers[hart as usize].get(to) {
                    Some(RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    })) => {
                        let (_locality, ttype) = state.configuration.get(&from_label).unwrap();
                        // If attempting to access outside the memory space for the label.
                        let full_offset = MemoryValueI64::from(4)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        let size = MemoryValueI64::try_from(size(ttype)).unwrap();
                        if let Some(ord) = size.compare(&full_offset) {
                            if ord == Ordering::Less {
                                return invalid_path(
                                    explorerer,
                                    configuration,
                                    harts,
                                    InvalidExplanation::Sw,
                                );
                            }
                            // Else we found the label and we can validate that the loading
                            // of a word with the given offset is within the address space.
                            // So we continue exploration.
                            // The path is invalid, so we add the current types to the
                            // excluded list and restart exploration.
                        } else {
                            todo!()
                        }
                    }
                    x => todo!("{x:?}"),
                }
            }
            Instruction::Sb(Sb {
                to,
                from: _,
                offset,
            }) => {
                // Collect the state.
                let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                let state = find_state(&record, root, harts, first_step, &configuration);

                // Check the destination is valid.
                match state.registers[hart as usize].get(to) {
                    Some(RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    })) => {
                        let (_locality, ttype) = state.configuration.get(&from_label).unwrap();
                        // If attempting to access outside the memory space for the label.
                        let full_offset = MemoryValueI64::from(1)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        let size = MemoryValueI64::try_from(size(ttype)).unwrap();
                        if let Some(ord) = size.compare(&full_offset) {
                            if ord == Ordering::Less {
                                return invalid_path(
                                    explorerer,
                                    configuration,
                                    harts,
                                    InvalidExplanation::Sw,
                                );
                            }
                            // Else we found the label and we can validate that the loading
                            // of a word with the given offset is within the address space.
                            // So we continue exploration.
                            // The path is invalid, so we add the current types to the
                            // excluded list and restart exploration.
                        } else {
                            todo!()
                        }
                    }
                    x => todo!("{x:?}"),
                }
            }
            // For any load we need to validate the destination is valid.
            Instruction::Ld(Ld {
                to: _,
                from,
                offset,
            }) => {
                // Collect the state.
                let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                let state = find_state(&record, root, harts, first_step, &configuration);

                // Check the destination is valid.
                match state.registers[branch.hart as usize].get(from) {
                    Some(RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    })) => {
                        let (_locality, ttype) = state.configuration.get(from_label).unwrap();
                        // If attempting to access outside the memory space for the label.
                        let full_offset = MemoryValueI64::from(8)
                            + MemoryValueI64::from(offset.value.value)
                            + *from_offset;
                        let size = MemoryValueI64::try_from(size(ttype)).unwrap();
                        if let Some(ord) = size.compare(&full_offset) {
                            if ord == Ordering::Less {
                                // The path is invalid, so we add the current types to the
                                // excluded list and restart exploration.
                                return invalid_path(
                                    explorerer,
                                    configuration,
                                    harts,
                                    InvalidExplanation::Lb,
                                );
                            }
                            // Else, we found the label and we can validate that the loading
                            // of a word with the given offset is within the address space.
                            // So we continue exploration.
                        } else {
                            todo!()
                        }
                    }
                    x => todo!("{x:?}"),
                }
            }
            Instruction::Lw(Lw {
                to: _,
                from,
                offset,
            }) => {
                // Collect the state.
                let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                let state = find_state(&record, root, harts, first_step, &configuration);

                // Check the destination is valid.
                match state.registers[branch.hart as usize].get(from) {
                    Some(RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    })) => {
                        let (_locality, ttype) = state.configuration.get(from_label).unwrap();
                        // If attempting to access outside the memory space for the label.
                        let full_offset = MemoryValueI64::from(4)
                            + MemoryValueI64::from(offset.value.value)
                            + *from_offset;
                        let size = MemoryValueI64::try_from(size(ttype)).unwrap();
                        if let Some(ord) = size.compare(&full_offset) {
                            if ord == Ordering::Less {
                                // The path is invalid, so we add the current types to the
                                // excluded list and restart exploration.
                                return invalid_path(
                                    explorerer,
                                    configuration,
                                    harts,
                                    InvalidExplanation::Lb,
                                );
                            }
                            // Else, we found the label and we can validate that the loading
                            // of a word with the given offset is within the address space.
                            // So we continue exploration.
                        } else {
                            todo!()
                        }
                    }
                    x => todo!("{x:?}"),
                }
            }
            Instruction::Lb(Lb {
                to: _,
                from,
                offset,
            }) => {
                // Collect the state.
                let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                let state = find_state(&record, root, harts, first_step, &configuration);

                // Check the destination is valid.
                match state.registers[branch.hart as usize].get(from) {
                    Some(RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    })) => {
                        let (_locality, ttype) = state.configuration.get(from_label).unwrap();
                        // If attempting to access outside the memory space for the label.
                        let full_offset = MemoryValueI64::from(1)
                            + MemoryValueI64::from(offset.value.value)
                            + *from_offset;
                        let size = MemoryValueI64::try_from(size(ttype)).unwrap();
                        if let Some(ord) = size.compare(&full_offset) {
                            if ord == Ordering::Less {
                                // The path is invalid, so we add the current types to the
                                // excluded list and restart exploration.
                                return invalid_path(
                                    explorerer,
                                    configuration,
                                    harts,
                                    InvalidExplanation::Lb,
                                );
                            }
                            // Else, we found the label and we can validate that the loading
                            // of a word with the given offset is within the address space.
                            // So we continue exploration.
                        } else {
                            todo!()
                        }
                    }
                    x => todo!("{x:?}"),
                }
            }
            // If any fail is encountered then the path is invalid.
            Instruction::Fail(_) => {
                return invalid_path(explorerer, configuration, harts, InvalidExplanation::Fail)
            }
            x => todo!("{x:?}"),
        }
        queue_up(branch_ptr, &mut queue, &configuration);

        return ExplorePathResult::Continue(Self {
            explorerer,
            configuration,
            touched,
            queue,
        });
    }
}

#[derive(Debug, Error)]
pub enum InvalidExplanation {
    #[error("Could not allocate non-excluded type for {0} for `lat`.")]
    Lat(Label),
    #[error("Could not allocate non-excluded type for {0} for `la`.")]
    La(Label),
    #[error("todo")]
    Sw,
    #[error(
        "Could not load as offset ({0}) is greater than the size ({1}) of the type ({2}) for `ld`."
    )]
    Ld(MemoryValueI64, usize, Type),
    #[error("todo")]
    Lw,
    #[error("todo")]
    Lb,
    #[error("todo")]
    Fail,
}

#[tracing::instrument(skip_all)]
unsafe fn invalid_path(
    explorerer: &mut Explorerer,
    configuration: ProgramConfiguration,
    harts: u8,
    explanation: InvalidExplanation,
) -> ExplorePathResult<'_> {
    // We need to track covered ground so we don't retread it.
    explorerer.excluded.insert(configuration.clone());

    trace!("excluded: {:?}", explorerer.excluded);

    let harts_root = explorerer
        .roots
        .iter()
        .find(|root| root.as_ref().harts == harts)
        .unwrap();
    let [hart_root] = harts_root.as_ref().next.as_slice() else {
        unreachable!()
    };
    let path = crate::draw::draw_tree(*hart_root, 2, |n| {
        let r = n.as_ref();
        format!("{}, {}", r.hart + 1, r.node.as_ref().this)
    });

    // Dealloc the current tree so we can restart.
    for mut root in explorerer.roots.iter().copied() {
        let stack = &mut root.as_mut().next;
        while let Some(next) = stack.pop() {
            stack.extend(next.as_ref().next.iter());
            dealloc(next.as_ptr().cast(), Layout::new::<VerifierNode>());
        }
    }

    // TODO Make this path better and doublecheck if this is actually correct behaviour.
    // This case only occurs when all types are excluded thus it continually breaks out
    // of the exploration loop with empty `initial_types`. This case means there is no
    // valid type combination and thus no valid path.
    ExplorePathResult::Invalid {
        complete: configuration.0.is_empty(),
        path,
        explanation,
    }
}

use thiserror::Error;


// Get the number of harts of this sub-tree and record the path.
#[tracing::instrument(skip_all)]
unsafe fn get_backpath_harts(
    prev: NonNull<VerifierNode>,
) -> (Vec<usize>, NonNull<VerifierHarts>, u8, usize) {
    let mut current = prev;
    let mut record = Vec::new();
    while let VerifierPrevNode::Branch(branch) = current.as_ref().prev {
        let r = branch
            .as_ref()
            .next
            .iter()
            .position(|&x| x == current)
            .unwrap();
        record.push(r);
        current = branch
    }
    let VerifierPrevNode::Root(root) = current.as_ref().prev else {
        unreachable!()
    };
    let harts = root.as_ref().harts;
    let first_step = root
        .as_ref()
        .next
        .iter()
        .position(|&x| x == current)
        .unwrap();
    (record, root, harts, first_step)
}

/// Queues up the next node to evaluate.
///
/// We look at the next node for the 1st hart and queue this up if its not racy,
/// if its racy, we look at the 2nd hart and queue it up if its not racy,
/// if its racy we look at the 3rd hart etc. If all next nodes are racy, we queue
/// up all racy instructions (since we need to evaluate all the possible ordering of them).
#[tracing::instrument(skip_all)]
unsafe fn queue_up(
    prev: NonNull<VerifierNode>,
    queue: &mut VecDeque<NonNull<VerifierNode>>,
    configuration: &ProgramConfiguration,
) {
    let (record, root, harts, first_step) = get_backpath_harts(prev);
    // TOOD We duplicate so much work doing `find_state` in a bunch of places and
    // multiple times when the state hasn't change, we should avoid doing this call
    // here (and remove the it in other places).
    let state = find_state(&record, root, harts, first_step, &configuration);

    // Search the verifier tree for the fronts of all harts.
    let mut fronts = BTreeMap::new();
    let mut current = prev.as_ref();
    fronts.insert(current.hart, current.node);
    while fronts.len() < harts as usize {
        let VerifierPrevNode::Branch(branch) = current.prev else {
            unreachable!()
        };
        current = branch.as_ref();
        fronts.entry(current.hart).or_insert(current.node);
    }

    trace!(
        "fronts: {:?}",
        fronts
            .iter()
            .map(|(hart, ast)| (hart, ast.as_ref().this.to_string()))
            .collect::<BTreeMap<_, _>>()
    );

    let followup = |node: NonNull<AstNode>,
                    hart: u8|
     -> Option<Result<(u8, NonNull<AstNode>), (u8, NonNull<AstNode>)>> {
        match &node.as_ref().this {
            // Non-racy.
            Instruction::Label(_)
            | Instruction::La(_)
            | Instruction::Lat(_)
            | Instruction::Li(_)
            | Instruction::Addi(_)
            | Instruction::Csrr(_)
            | Instruction::Define(_)
            | Instruction::Blt(_)
            | Instruction::Bne(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_)
            | Instruction::Fail(_)
            | Instruction::Branch(_)
            | Instruction::Beq(_) => Some(Err((hart, node))),
            // Possibly racy.
            // If the label is thread local its not racy.
            Instruction::Sb(Sb { to: register, .. })
            | Instruction::Sw(Sw { to: register, .. })
            | Instruction::Ld(Ld { from: register, .. })
            | Instruction::Lw(Lw { from: register, .. })
            | Instruction::Lb(Lb { from: register, .. }) => {
                let value = state.registers[hart as usize].get(register).unwrap();
                if let RegisterValue::Address(MemoryLocation { tag, offset: _ }) = value {
                    let (locality, _ttype) = state.configuration.get(tag).unwrap();
                    match locality {
                        Locality::Global => Some(Ok((hart, node))),  // Racy
                        Locality::Thread => Some(Err((hart, node))), // Non-racy
                    }
                } else {
                    todo!()
                }
            }
            // See note on `wfi`.
            Instruction::Wfi(_) => Some(Ok((hart, node))),
            x @ _ => todo!("{x:?}"),
        }
    };

    // The lowest hart non-racy node is enqueued.
    // (or possibly multiples nodes in the case of a conditional jump where
    // we cannot deteremine the condition).

    let next_nodes = fronts
        .iter()
        .rev()
        .filter_map(|(&hart, &node)| {
            let node_ref = node.as_ref();
            match &node_ref.this {
                // Conditional.
                Instruction::Blt(Blt { rhs, lhs, label }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    let lhs = state.registers[hart as usize].get(lhs);
                    let rhs = state.registers[hart as usize].get(rhs);
                    match (lhs, rhs) {
                        (Some(l), Some(r)) => {
                            if let Some(ord) = l.compare(r) {
                                if ord == Ordering::Less {
                                    let label_node = find_label(node, label).unwrap();
                                    followup(label_node, hart)
                                } else {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        _ => todo!(),
                    }
                }
                Instruction::Beq(Beq { rhs, lhs, out }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    // error!("state.memory: {:?}",state.memory);
                    // error!("state.registers: {:?}",state.registers);

                    let lhs = state.registers[hart as usize].get(lhs);
                    let rhs = state.registers[hart as usize].get(rhs);
                    match (lhs, rhs) {
                        (Some(l), Some(r)) => {
                            if let Some(ord) = l.compare(r) {
                                if ord == Ordering::Equal {
                                    let label_node = find_label(node, out).unwrap();
                                    followup(label_node, hart)
                                } else {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        x @ _ => todo!("{x:?}"),
                    }
                }
                Instruction::Bne(Bne { rhs, lhs, out }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    // error!("state.memory: {:?}",state.memory);
                    // error!("state.registers: {:?}",state.registers);

                    let lhs = state.registers[hart as usize].get(lhs);
                    let rhs = state.registers[hart as usize].get(rhs);
                    match (lhs, rhs) {
                        (Some(l), Some(r)) => {
                            if let Some(ord) = l.compare(r) {
                                if ord == Ordering::Equal {
                                    followup(node_ref.next.unwrap(), hart)
                                } else {
                                    let label_node = find_label(node, out).unwrap();
                                    followup(label_node, hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        x @ _ => todo!("{x:?}"),
                    }
                }
                Instruction::Bnez(Bnez { src, dest }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    let src = state.registers[hart as usize].get(src);

                    // In the case the path is determinate, we either queue up the label
                    // or the next ast node and don't need to actually visit/evaluate
                    // the branch at runtime.
                    match src {
                        Some(RegisterValue::I8(imm)) => {
                            if let Some(eq) = imm.compare(&MemoryValueI8::ZERO) {
                                if eq == Ordering::Equal {
                                    followup(node_ref.next.unwrap(), hart)
                                } else {
                                    let label_node = find_label(node, dest).unwrap();
                                    followup(label_node, hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        Some(RegisterValue::U8(imm)) => {
                            if let Some(eq) = imm.compare(&MemoryValueU8::ZERO) {
                                if eq == Ordering::Equal {
                                    followup(node_ref.next.unwrap(), hart)
                                } else {
                                    let label_node = find_label(node, dest).unwrap();
                                    followup(label_node, hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        Some(RegisterValue::Csr(CsrValue::Mhartid)) => {
                            if hart != 0 {
                                let label_node = find_label(node, dest).unwrap();
                                followup(label_node, hart)
                            } else {
                                followup(node_ref.next.unwrap(), hart)
                            }
                        }
                        x => todo!("{x:?}"),
                    }
                }
                Instruction::Beqz(Beqz { register, label }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    let src = state.registers[hart as usize].get(register);

                    // In the case the path is determinate, we either queue up the label
                    // or the next ast node and don't need to actually visit/evaluate
                    // the branch at runtime.
                    match src {
                        Some(RegisterValue::U8(imm)) => {
                            if let Some(eq) = imm.compare(&MemoryValueU8::ZERO) {
                                if eq == Ordering::Equal {
                                    let label_node = find_label(node, label).unwrap();
                                    followup(label_node, hart)
                                } else {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        Some(RegisterValue::I8(imm)) => {
                            if let Some(eq) = imm.compare(&MemoryValueI8::ZERO) {
                                if eq == Ordering::Equal {
                                    let label_node = find_label(node, label).unwrap();
                                    followup(label_node, hart)
                                } else {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        Some(RegisterValue::Csr(CsrValue::Mhartid)) => {
                            if hart == 0 {
                                let label_node = find_label(node, label).unwrap();
                                followup(label_node, hart)
                            } else {
                                followup(node_ref.next.unwrap(), hart)
                            }
                        }
                        x => todo!("{x:?}"),
                    }
                }
                Instruction::Bge(Bge { lhs, rhs, out }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    let lhs = state.registers[hart as usize].get(lhs);
                    let rhs = state.registers[hart as usize].get(rhs);
                    match (lhs, rhs) {
                        (Some(l), Some(r)) => {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if let Some(cmp) = l.compare(r) {
                                match cmp {
                                    Ordering::Greater => {
                                        let label_node = find_label(node, out).unwrap();
                                        followup(label_node, hart)
                                    }
                                    _ => followup(node_ref.next.unwrap(), hart),
                                }
                            } else {
                                todo!()
                            }
                        }
                        _ => todo!(),
                    }
                }
                // Non-conditional
                Instruction::Label(_)
                | Instruction::La(_)
                | Instruction::Lat(_)
                | Instruction::Li(_)
                | Instruction::Addi(_)
                | Instruction::Csrr(_)
                | Instruction::Define(_)
                | Instruction::Sw(_)
                | Instruction::Sb(_)
                | Instruction::Ld(_)
                | Instruction::Lw(_)
                | Instruction::Lb(_)
                | Instruction::Fail(_) => followup(node_ref.next.unwrap(), hart),
                Instruction::Branch(Branch { out }) => {
                    let label_node = find_label(node, out).unwrap();
                    followup(label_node, hart)
                }
                // See note on `wfi`.
                Instruction::Wfi(_) => Some(Ok((hart, node_ref.next.unwrap()))),
                // Blocking.
                Instruction::Unreachable(_) => None,
                x @ _ => todo!("{x:?}"),
            }
        })
        .collect::<Result<Vec<_>, _>>();

    debug!("racy: {}", next_nodes.is_ok());

    match next_nodes {
        // If there was a non-racy node, enqueue this single node.
        Err((hart, non_racy_next)) => {
            queue.push_back(simple_nonnull(prev, non_racy_next, hart));
        }
        // If all nodes where racy, enqueue these nodes.
        Ok(racy_nodes) => {
            for (hart, node) in racy_nodes {
                queue.push_back(simple_nonnull(prev, node, hart));
            }
        }
    }
}

unsafe fn simple_nonnull(
    mut prev: NonNull<VerifierNode>,
    node: NonNull<AstNode>,
    hart: u8,
) -> NonNull<VerifierNode> {
    let ptr = alloc(Layout::new::<VerifierNode>()).cast();
    ptr::write(
        ptr,
        VerifierNode {
            prev: VerifierPrevNode::Branch(prev),
            hart,
            node,
            next: Vec::new(),
        },
    );
    let nonull = NonNull::new(ptr).unwrap();
    prev.as_mut().next.push(nonull);
    nonull
}

unsafe fn find_label(node: NonNull<AstNode>, label: &Label) -> Option<NonNull<AstNode>> {
    // Check start
    if let Instruction::Label(LabelInstruction { tag }) = &node.as_ref().this {
        if tag == label {
            return Some(node);
        }
    }

    // Trace backwards.
    let mut back = node;
    while let Some(prev) = back.as_ref().prev {
        if let Instruction::Label(LabelInstruction { tag }) = &prev.as_ref().this {
            if tag == label {
                return Some(prev);
            }
        }
        back = prev;
    }

    // Trace forward.
    let mut front = node;
    while let Some(next) = front.as_ref().next {
        if let Instruction::Label(LabelInstruction { tag }) = &next.as_ref().this {
            if tag == label {
                return Some(next);
            }
        }
        front = next;
    }

    None
}

unsafe fn find_state(
    record: &[usize], // The record of which children to follow from the root to reach the current position.
    root: NonNull<VerifierHarts>, // The root of the verification tree.
    harts: u8,        // The number of hardware threads in the current path.
    first_step: usize, // The child node of the root which forms the current path (will correlate with `harts`).
    configuration: &ProgramConfiguration,
) -> State {
    // Iterator to generate unique labels.
    const N: u8 = b'z' - b'a';
    let mut tag_iter = (0..)
        .map(|index| Label {
            tag: once('_')
                .chain((0..index / N).map(|_| 'z'))
                .chain(once(char::from_u32(((index % N) + b'a') as u32).unwrap()))
                .collect::<String>(),
        })
        .peekable();

    // Iterate forward to find the values.
    let mut state = State::new(harts, configuration);
    let mut current = root.as_ref().next[first_step];
    for next in record.iter().rev() {
        let vnode = current.as_ref();
        let hart = vnode.hart;
        let hartu = hart as usize;
        match &vnode.node.as_ref().this {
            // Instructions with no side affects.
            Instruction::Label(_)
            | Instruction::Blt(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_)
            | Instruction::Bne(_)
            | Instruction::Branch(_)
            | Instruction::Beq(_) => {}
            // No side affects, but worth double checking.
            Instruction::Define(Define {
                label,
                locality,
                cast,
            }) => {
                let (found_locality, found_type) = state.configuration.get(label).unwrap();
                if let Some(defined_locality) = locality {
                    assert_eq!(found_locality, defined_locality);
                }
                if let Some(defined_cast) = cast {
                    assert_eq!(found_type, defined_cast);
                }
            }
            Instruction::Li(Li {
                register,
                immediate,
            }) => {
                let register_value = RegisterValue::from(immediate);
                state.registers[hartu].insert(*register, register_value);
            }
            // TOOD This is the only place where in finding state we need to modify `state.configuration`
            // is this the best way to do this? Could these types not be defined in `next_step` (like `la`)?
            Instruction::Lat(Lat { register, label }) => {
                let (locality, typeof_type) = state.configuration.get(label).unwrap();
                let (loc, subtypes) = state.memory.set_type(typeof_type, &mut tag_iter);
                state.registers[hartu].insert(*register, RegisterValue::from(loc.clone()));

                // Each type type is thread local and unique between `lat` instructions.
                let hart_type_state = &mut state.configuration;
                let existing =
                    hart_type_state.insert(loc, (Locality::Thread, MemoryValueType::type_of()));
                // Extend with subtypes.
                hart_type_state.append(subtypes);
            }
            Instruction::La(La { register, label }) => {
                state.registers[hartu].insert(*register, RegisterValue::from(label.clone()));
            }
            Instruction::Sw(Sw { to, from, offset }) => {
                let Some(to_value) = state.registers[hartu].get(to) else {
                    todo!()
                };
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match to_value {
                    RegisterValue::Address(MemoryLocation {
                        tag: to_label,
                        offset: to_offset,
                    }) => {
                        let (locality, to_type) = state.configuration.get(to_label).unwrap();
                        // We should have already checked the type is large enough for the store.
                        debug_assert!(size(to_type) >= 4);
                        match from_value {
                            RegisterValue::U32(from_imm) => {
                                if let Some(imm) = from_imm.value() {
                                    let tag = match locality {
                                        Locality::Global => to_label.clone(),
                                        Locality::Thread => to_label.thread_local(hart),
                                    };
                                    let memloc = MemoryLocation {
                                        tag,
                                        offset: *to_offset
                                            + MemoryValueI64::from(offset.value.value),
                                    };
                                    state.memory.set_u32(&memloc, imm);
                                } else {
                                    todo!()
                                }
                            }
                            _ => todo!(),
                        }
                    }
                    _ => todo!(),
                }
            }
            Instruction::Sb(Sb { to, from, offset }) => {
                let Some(to_value) = state.registers[hartu].get(to) else {
                    todo!()
                };
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match to_value {
                    RegisterValue::Address(MemoryLocation {
                        tag: to_label,
                        offset: to_offset,
                    }) => {
                        let (locality, to_type) = state.configuration.get(to_label).unwrap();
                        // We should have already checked the type is large enough for the store.
                        let sizeof = MemoryValueI64::try_from(size(to_type)).unwrap();
                        let final_offset = MemoryValueI64::from(1)
                            + *to_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            Some(Ordering::Greater | Ordering::Equal)
                        ));
                        match from_value {
                            RegisterValue::U8(from_imm) => {
                                if let Some(imm) = from_imm.value() {
                                    let tag = match locality {
                                        Locality::Global => to_label.clone(),
                                        Locality::Thread => to_label.thread_local(hart),
                                    };
                                    let memloc = MemoryLocation {
                                        tag,
                                        offset: *to_offset
                                            + MemoryValueI64::from(offset.value.value),
                                    };
                                    state.memory.set_u8(&memloc, imm);
                                } else {
                                    todo!()
                                }
                            }
                            _ => todo!(),
                        }
                    }
                    _ => todo!(),
                }
            }
            Instruction::Ld(Ld { to, from, offset }) => {
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    }) => {
                        let (locality, from_type) = state.configuration.get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        let sizeof = MemoryValueI64::try_from(size(from_type)).unwrap();
                        let final_offset = MemoryValueI64::from(8)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            Some(Ordering::Greater | Ordering::Equal)
                        ));
                        let tag = match locality {
                            Locality::Global => from_label.clone(),
                            Locality::Thread => from_label.thread_local(hart),
                        };
                        let memloc = MemoryLocation {
                            tag,
                            offset: *from_offset + MemoryValueI64::from(offset.value.value),
                        };
                        let doubleword =
                            state.memory.get_u64(&memloc).expect(&format!("{memloc:?}"));
                        state.registers[hartu].insert(*to, RegisterValue::from(doubleword));
                    }
                    x @ _ => todo!("{x:?}"),
                }
            }
            Instruction::Lw(Lw { to, from, offset }) => {
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    }) => {
                        let (locality, from_type) = state.configuration.get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        let sizeof = MemoryValueI64::try_from(size(from_type)).unwrap();
                        let final_offset = MemoryValueI64::from(4)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            Some(Ordering::Greater | Ordering::Equal)
                        ));
                        let tag = match locality {
                            Locality::Global => from_label.clone(),
                            Locality::Thread => from_label.thread_local(hart),
                        };
                        let memloc = MemoryLocation {
                            tag,
                            offset: *from_offset + MemoryValueI64::from(offset.value.value),
                        };
                        let Some(word) = state.memory.get_u32(&memloc) else {
                            todo!("{memloc:?}");
                        };
                        state.registers[hartu].insert(*to, RegisterValue::U32(word));
                    }
                    _ => todo!(),
                }
            }
            Instruction::Lb(Lb { to, from, offset }) => {
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(MemoryLocation {
                        tag: from_label,
                        offset: from_offset,
                    }) => {
                        let (locality, from_type) = state.configuration.get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        let sizeof = MemoryValueI64::try_from(size(from_type)).unwrap();
                        let final_offset = MemoryValueI64::from(1)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            Some(Ordering::Greater | Ordering::Equal)
                        ));
                        let tag = match locality {
                            Locality::Global => from_label.clone(),
                            Locality::Thread => from_label.thread_local(hart),
                        };
                        let memloc = MemoryLocation {
                            tag,
                            offset: *from_offset + MemoryValueI64::from(offset.value.value),
                        };
                        let Some(byte) = state.memory.get_u8(&memloc) else {
                            todo!("{memloc:?}")
                        };
                        state.registers[hartu].insert(*to, RegisterValue::U8(byte));
                    }
                    _ => todo!(),
                }
            }
            Instruction::Addi(Addi { out, lhs, rhs }) => {
                let lhs_value = state.registers[hartu].get(lhs).cloned().unwrap();
                state.registers[hartu].insert(*out, lhs_value + RegisterValue::from(rhs));
            }
            Instruction::Csrr(Csrr { dest, src }) => match src {
                Csr::Mhartid => {
                    state.registers[hartu].insert(*dest, RegisterValue::Csr(CsrValue::Mhartid));
                }
                _ => todo!(),
            },
            // TODO Some interrupt state is likely affected here so this needs to be added.
            Instruction::Wfi(_) => {}
            Instruction::Unreachable(_) => {}
            x => todo!("{x:?}"),
        }
        current = current.as_ref().next[*next];
    }
    state
}
