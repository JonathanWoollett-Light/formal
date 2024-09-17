use crate::ast::*;
use std::alloc::Layout;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::hash::Hash;
use std::iter::once;
use std::ops::Add;
use std::ops::Range;
use std::ops::Sub;
use std::ptr;
use std::rc::Rc;
use std::{
    alloc::alloc,
    collections::{HashMap, VecDeque},
    ptr::NonNull,
};
use thiserror::Error;
use tracing::error;
use tracing::trace;

/// Compile time size
fn size(t: &Type) -> u64 {
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
    map: HashMap<MemoryLabel, MemoryValue>,
}

/// Repreresents memory `mem[base+offset..base+offset+len]``
#[derive(Debug)]
struct Slice {
    base: MemoryLabel,
    offset: MemoryValueI64,
    len: MemoryValueU64,
}

#[derive(Debug)]
struct SubSlice {
    offset: MemoryValueI64,
    len: MemoryValueU64,
}

#[derive(Debug, Error)]
enum GetMemoryMapError {
    #[error("Failed to find the label in the memory map.")]
    Missing,
    #[error("Failed to get the value: {0}")]
    Value(MemoryValueGetError),
}

#[derive(Debug, Error)]
enum SetMemoryMapError {
    #[error("Attempted to set null ptr.")]
    NullPtr,
    #[error("Failed to find the label in the memory map.")]
    Missing,
    #[error("Failed to set the value: {0}")]
    Value(MemoryValueSetError),
}

impl MemoryMap {
    fn get(&self, Slice { base, offset, len }: &Slice) -> Result<MemoryValue, GetMemoryMapError> {
        self.map
            .get(base)
            .ok_or(GetMemoryMapError::Missing)?
            .get(&SubSlice {
                offset: *offset,
                len: len.clone(),
            })
            .map_err(GetMemoryMapError::Value)
    }

    fn set(
        &mut self,
        // Memory location.
        key: &MemoryPtr,
        // Register position.
        slice: &SubSlice,
        // Register value.
        value: MemoryValue
    ) -> Result<(), SetMemoryMapError> {
        let MemoryPtr(Some(NonNullMemoryPtr { tag, offset })) = key else {
            return Err(SetMemoryMapError::NullPtr);
        };
        let existing = self.map.get_mut(tag).ok_or(SetMemoryMapError::Missing)?;
        existing
            .set(offset, slice,value)
            .map_err(SetMemoryMapError::Value)
    }

    // TODO This should be improved, I'm pretty sure the current approach is bad.
    // In setting a type type we need to set many sublabels for the sub-types.
    fn set_type(
        &mut self,
        value: &Type,
        tag_iter: &mut Peekable<impl Iterator<Item = Label>>, // Iterator to generate unique tags.
        hart: u8,
    ) -> (MemoryLabel, ProgramConfiguration) {
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
                    .map(|(addr, t)| {
                        MemoryValue::List(vec![
                            MemoryValue::U64(MemoryValueU64::from(FlatType::from(&t) as u64)),
                            MemoryValue::Ptr(MemoryPtr(addr.map(|tag| NonNullMemoryPtr {
                                tag,
                                offset: MemoryValueI64::ZERO,
                            }))),
                            MemoryValue::U64(MemoryValueU64::from(if let Type::List(l) = &t {
                                l.len()
                            } else {
                                0
                            })),
                            MemoryValue::U8(MemoryValueU8::from(Locality::Thread as u8)),
                        ])
                    })
                    .collect::<Vec<_>>();
                let tag = tag_iter.next().unwrap();
                let mem_tag = MemoryLabel::Thread {
                    label: tag.clone(),
                    hart,
                };
                vec[left].0 = Some(mem_tag.clone());

                // Insert collect subtypes types
                let subtypes_list = memory_types
                    .iter()
                    .map(|_| MemoryValueType::type_of())
                    .collect();
                subtypes.insert(
                    tag.into(),
                    hart,
                    (Locality::Thread, Type::List(subtypes_list)),
                );
                // Insert subtypes into memory.
                self.map.insert(mem_tag, MemoryValue::List(memory_types));
                right = left;
            }
        }

        let final_tag = MemoryLabel::Thread {
            label: tag_iter.next().unwrap(),
            hart,
        };
        match vec.remove(0) {
            (addr @ Some(_), Type::List(list)) => {
                self.map.insert(
                    final_tag.clone(),
                    MemoryValue::List(vec![
                        MemoryValue::U64(MemoryValueU64::from(FlatType::List as u64)),
                        MemoryValue::Ptr(MemoryPtr(addr.map(|tag| NonNullMemoryPtr {
                            tag,
                            offset: MemoryValueI64::ZERO,
                        }))),
                        MemoryValue::U64(MemoryValueU64::from(list.len())),
                        MemoryValue::U8(MemoryValueU8::from(Locality::Thread as u8)),
                    ]),
                );
            }
            (None, t) => {
                self.map.insert(
                    final_tag.clone(),
                    MemoryValue::List(vec![
                        MemoryValue::U64(MemoryValueU64::from(FlatType::from(&t) as u64)),
                        MemoryValue::Ptr(MemoryPtr(None)),
                        MemoryValue::U64(MemoryValueU64::ZERO),
                        MemoryValue::U8(MemoryValueU8::from(Locality::Thread as u8)),
                    ]),
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
    registers: Vec<RegisterValues>,
    memory: MemoryMap,
    configuration: ProgramConfiguration,
}
#[derive(Debug)]
struct RegisterValues(HashMap<Register, MemoryValue>);
impl RegisterValues {
    fn insert(&mut self, key: Register, value: MemoryValue) -> Result<Option<MemoryValue>, ()> {
        // Attempting to store a list that is larger than 64 bits into a 64 bit register will fail.
        if let MemoryValue::List(_) = value {
            todo!()
        }
        Ok(self.0.insert(key, value))
    }
    fn get(&self, key: &Register) -> Option<&MemoryValue> {
        self.0.get(key)
    }
}

impl State {
    fn new(harts: u8, configuration: &ProgramConfiguration) -> Self {
        let mut memory = MemoryMap {
            map: HashMap::new(),
        };

        // Initialize bss
        for (k, (l, t)) in configuration.0.iter() {
            match l {
                // Create an entry in bss for a copy of the value in each thread in which its touched.
                LabelLocality::Thread(threads) => {
                    for thread in threads {
                        memory.map.insert(
                            MemoryLabel::Thread {
                                label: k.clone(),
                                hart: *thread,
                            },
                            MemoryValue::from(t.clone()),
                        );
                    }
                }
                LabelLocality::Global => {
                    memory.map.insert(
                        MemoryLabel::Global { label: k.clone() },
                        MemoryValue::from(t.clone()),
                    );
                }
            }
        }

        Self {
            registers: (0..harts).map(|_| RegisterValues(HashMap::new())).collect(),
            memory,
            configuration: configuration.clone(),
        }
    }
}

#[derive(Debug, Clone)]
struct MemoryPtr(Option<NonNullMemoryPtr>);
#[derive(Debug, Clone)]
struct NonNullMemoryPtr {
    tag: MemoryLabel,
    offset: MemoryValueI64,
}

#[derive(Debug, Error)]
enum MemoryValuePtrGetError {
    #[error("Potentially access outside type with {0}")]
    Outside(MemoryValueI64),
}

impl MemoryPtr {
    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValuePtrGetError> {
        let end = *offset + MemoryValueI64::try_from(len.clone()).unwrap();

        match end.compare(&MemoryValueI64::from(size(&Type::U32) as i64)) {
            RangeOrdering::Less | RangeOrdering::Greater | RangeOrdering::Cover => {
                Err(MemoryValuePtrGetError::Outside(end))
            }
            RangeOrdering::Equal => match offset.exact() {
                Some(0) => Ok(MemoryValue::Ptr(self.clone())),
                _ => todo!(),
            },
            RangeOrdering::Within => match (offset.exact(), len.exact()) {
                (Some(o), Some(l)) if l == size(&Type::U64) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::Ptr(self.clone()))
                }
                x => todo!("{x:?}"),
            },
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum MemoryLabel {
    Global { label: Label },
    Thread { label: Label, hart: u8 },
}

impl<'a> From<&'a MemoryLabel> for &'a Label {
    fn from(m: &'a MemoryLabel) -> &'a Label {
        match m {
            MemoryLabel::Global { label } => label,
            MemoryLabel::Thread { label, .. } => label,
        }
    }
}
impl From<MemoryLabel> for Label {
    fn from(m: MemoryLabel) -> Label {
        match m {
            MemoryLabel::Global { label } => label,
            MemoryLabel::Thread { label, .. } => label,
        }
    }
}
impl<'a> From<&'a MemoryLabel> for &'a Locality {
    fn from(m: &'a MemoryLabel) -> &'a Locality {
        match m {
            MemoryLabel::Global { .. } => &Locality::Global,
            MemoryLabel::Thread { .. } => &Locality::Thread,
        }
    }
}

// It is possible to technically store a 4 byte virtual value (e.g. DATA_END)
// then edit 2 bytes of it. So we will need additional complexity to support this case
#[derive(Debug, Clone)]
enum MemoryValue {
    U64(MemoryValueU64),
    U32(MemoryValueU32),
    U16(MemoryValueU16),
    U8(MemoryValueU8),
    List(Vec<MemoryValue>),
    I8(MemoryValueI8),
    I64(MemoryValueI64),
    I16(MemoryValueI16),
    Ptr(MemoryPtr),
    Csr(CsrValue),
}

impl From<Immediate> for MemoryValue {
    fn from(imm: Immediate) -> Self {
        Self::I64(MemoryValueI64::from(imm.value))
    }
}

impl From<&MemoryValue> for Type {
    fn from(mv: &MemoryValue) -> Self {
        match mv {
            MemoryValue::U8(_) => Type::U8,
            x @ _ => todo!("{x:?}"),
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
            Type::I8 => MemoryValue::I8(MemoryValueI8 {
                start: i8::MIN,
                stop: i8::MAX,
            }),
            Type::U16 => MemoryValue::U16(MemoryValueU16 {
                start: u16::MIN,
                stop: u16::MAX,
            }),
            Type::I16 => MemoryValue::I16(MemoryValueI16 {
                start: i16::MIN,
                stop: i16::MAX,
            }),
            Type::U32 => MemoryValue::U32(MemoryValueU32 {
                start: u32::MIN,
                stop: u32::MAX,
            }),
            _ => todo!(),
        }
    }
}

#[derive(Debug, Error)]
enum MemoryValueGetError {
    #[error("Failed to get u8: {0}")]
    U8(MemoryValueU8GetError),
    #[error("Failed to get u32: {0}")]
    U32(MemoryValueU32GetError),
    #[error("Failed to get u64: {0}")]
    U64(MemoryValueU64GetError),
    #[error("Failed to get ptr: {0}")]
    Ptr(MemoryValuePtrGetError),
    #[error("This would get multiple items from a list, this is currently not supported.")]
    ListMultiple,
}

#[derive(Debug, Error)]
enum MemoryValueSetError {
    #[error("Potentially access outside type with {0}")]
    Outside(MemoryValueI64),
    #[error("Attempting to set too large value.")]
    TooLarge,
    #[error("This would set multiple items from in the list, this is currently not supported.")]
    ListMultiple,
}

fn memory_range(offset: &MemoryValueI64, len: &MemoryValueI64) -> MemoryValueI64 {
    MemoryValueI64 {
        start: offset.start,
        stop: offset.stop + len.stop,
    }
}

impl MemoryValue {
    fn get(&self, subslice: &SubSlice) -> Result<MemoryValue, MemoryValueGetError> {
        use MemoryValue::*;
        match self {
            U8(x) => x.get(subslice).map_err(MemoryValueGetError::U8),
            U32(x) => x.get(subslice).map_err(MemoryValueGetError::U32),
            U64(x) => x.get(subslice).map_err(MemoryValueGetError::U64),
            Ptr(x) => x.get(subslice).map_err(MemoryValueGetError::Ptr),
            List(list) => {
                let SubSlice { offset, len } = subslice;
                let memrange =
                    memory_range(offset, &MemoryValueI64::try_from(len.clone()).unwrap());
                let mut previous = 0;
                let mut covers = Vec::new();
                let mut iter = list.iter().enumerate();

                // Iterate items before.
                loop {
                    let Some((i, item)) = iter.next() else { break };
                    let next = previous + size(&Type::from(item)) as i64;
                    let current = MemoryValueI64 {
                        start: previous,
                        stop: next,
                    };
                    match memrange.compare(&current) {
                        // Gets all bytes of this item.
                        RangeOrdering::Matches => return Ok(item.clone()),
                        // Gets some bytes within this item.
                        RangeOrdering::Within => {
                            return item.get(&SubSlice {
                                offset: (*offset - current),
                                len: len.clone(),
                            });
                        }
                        RangeOrdering::Cover => {
                            covers.push(i);
                            previous = next;
                            break;
                        }
                        RangeOrdering::Less => unreachable!(),
                        RangeOrdering::Greater => {
                            previous = next;
                        }
                        x => todo!("{x:?}"),
                    }
                }
                // Iterate items within
                loop {
                    let Some((i, item)) = iter.next() else { break };
                    let next = previous + size(&Type::from(item)) as i64;
                    let current = MemoryValueI64 {
                        start: previous,
                        stop: next,
                    };
                    match memrange.compare(&current) {
                        RangeOrdering::Matches => unreachable!(),
                        RangeOrdering::Within => unreachable!(),
                        RangeOrdering::Cover => {
                            covers.push(i);
                            previous = next;
                        }
                        RangeOrdering::Less => break,
                        RangeOrdering::Greater => unreachable!(),
                        x => todo!("{x:?}"),
                    }
                }

                // Use `covers` to apply the change.
                Err(MemoryValueGetError::ListMultiple)
            }
            _ => todo!(),
        }
    }

    fn set(
        &mut self,
        // Offset in memory.
        offset: &MemoryValueI64,
        // Register position.
        // The `len` should always be exact since it matches to instruction e.g. `sw` has `len=4`.
        // I don't know if the `offset` can be dynamic.
        subslice: &SubSlice,
        // Register value.
        value: MemoryValue,
    ) -> Result<(), MemoryValueSetError> {
        let size_of_existing = MemoryValueI64::from(size(&Type::from(self.clone())) as i64);
        let diff = size_of_existing - *offset;
        let size_of_value = subslice.len;

        // we can't use recursion for lists since it may affect multiple items in a list.

        // Compare the size of the value we are attempting to store to the space within the memory type with the offset.
        match MemoryValueI64::try_from(subslice.len).unwrap().compare(&diff) {
            // Setting bytes from the offset reaching the end of the type.
            RangeOrdering::Equal => {
                // In the case of setting all bytes, its very simple.
                if let Some(0) = offset.exact() {
                    *self = value;
                    return Ok(());
                }
                match self {
                    MemoryValue::U8(_) => unreachable!(),
                    // If we are setting bytes that reach the end, we know this will be the last element.
                    // We can also reach this case where we are setting an empty list to an empty list,
                    // both have equal sizes, but both are 0 and contain no elements.
                    MemoryValue::List(list) => {
                        let Some(item) = list.last_mut() else {
                            // In the case of empty list setting we don't need to do anything.
                            return Ok(());
                        };
                        let size_of_item = size(&Type::from(item.clone()));
                        // Compare the size of the list item with the size of the value we are trying to set,
                        match size_of_item.cmp(&size_of_value) {
                            // if the size is equal it fully covers the last item in the list.
                            Ordering::Equal => {
                                *item = value;
                                Ok(())
                            }
                            // if the size of the value is larger it will leak into earlier
                            // items in the list.
                            Ordering::Greater => todo!(),
                            // if the size of the value is smaller it will only cover the
                            // later bytes of the last item in the list.
                            Ordering::Less => todo!(),
                        }
                    }
                    _ => todo!(),
                }
            }
            // Setting bytes from the offset not reaching the end of the type.
            RangeOrdering::Less => match self {
                MemoryValue::List(list) => {
                    let memrange = memory_range(
                        offset,
                        &MemoryValueI64::from(size(&Type::from(value.clone())) as i64),
                    );
                    let mut previous = 0;
                    let mut covers = Vec::new();
                    let mut iter = list.iter_mut().enumerate();

                    // Iterate items before.
                    loop {
                        let Some((i, item)) = iter.next() else { break };
                        let next = previous + size(&Type::from(item.clone())) as i64;
                        let current = MemoryValueI64 {
                            start: previous,
                            stop: next,
                        };
                        match memrange.compare(&current) {
                            // Sets all bytes of this item.
                            RangeOrdering::Matches => {
                                *item = value;
                                return Ok(());
                            }
                            // Sets some bytes within this item.
                            RangeOrdering::Within => todo!(),
                            RangeOrdering::Cover => {
                                covers.push(i);
                                previous = next;
                                break;
                            }
                            RangeOrdering::Less => unreachable!(),
                            RangeOrdering::Greater => {
                                previous = next;
                            }
                            x => todo!("{x:?}"),
                        }
                    }
                    // Iterate items within
                    loop {
                        let Some((i, item)) = iter.next() else { break };
                        let next = previous + size(&Type::from(item.clone())) as i64;
                        let current = MemoryValueI64 {
                            start: previous,
                            stop: next,
                        };
                        match memrange.compare(&current) {
                            RangeOrdering::Matches => unreachable!(),
                            RangeOrdering::Within => unreachable!(),
                            RangeOrdering::Cover => {
                                covers.push(i);
                                previous = next;
                            }
                            RangeOrdering::Less => break,
                            RangeOrdering::Greater => unreachable!(),
                            x => todo!("{x:?}"),
                        }
                    }

                    // Use `covers` to apply the change.
                    Err(MemoryValueSetError::ListMultiple)
                }
                _ => todo!(),
            },
            // Setting bytes after the end of the type.
            RangeOrdering::Greater => Err(MemoryValueSetError::TooLarge),
            RangeOrdering::Within | RangeOrdering::Cover => todo!(),
            x => todo!("{x:?}"),
        }
    }

    fn compare(&self, other: &Self) -> Option<RangeOrdering> {
        use MemoryValue::*;
        match (self, other) {
            (U8(a), U8(b)) => Some(a.compare(b)),
            (I8(a), I8(b)) => Some(a.compare(b)),
            (U16(a), U16(b)) => Some(a.compare(b)),
            (I16(a), I16(b)) => Some(a.compare(b)),
            (U32(a), U32(b)) => Some(a.compare(b)),
            (U64(a), U64(b)) => Some(a.compare(b)),
            (I64(a), I64(b)) => Some(a.compare(b)),
            (U32(a), U8(b)) => Some(a.compare(&MemoryValueU32::from(b.clone()))),
            (U64(a), U8(b)) => Some(a.compare(&MemoryValueU64::from(b.clone()))),
            _ => todo!(),
        }
    }

    fn set_u8(&mut self, i: &MemoryValueI64, n: u8) {
        match self {
            Self::List(list) => {
                set_into_list(list, i, |item, offset, value| item.set_u8(offset, value), n).unwrap()
            }
            Self::U8(byte) => byte.set_u8(i, n),
            _ => todo!(),
        }
    }
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
    fn exact(&self) -> Option<i8> {
        (self.start == self.stop).then_some(self.start)
    }
}
impl RangeType for MemoryValueI8 {
    type Base = i8;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Clone)]
struct MemoryValueU16 {
    start: u16,
    stop: u16,
}
impl From<u16> for MemoryValueU16 {
    fn from(x: u16) -> Self {
        Self { start: x, stop: x }
    }
}
impl Add for MemoryValueU16 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}

impl MemoryValueU16 {
    const ZERO: Self = Self { start: 0, stop: 0 };
    fn get_i8(&self, i: usize) -> Option<MemoryValueU16> {
        if i > 0 {
            return None;
        }
        Some(self.clone())
    }
    fn set_i8(&mut self, i: usize, n: u16) {
        assert!(i > 0);
        self.start = n;
        self.stop = n;
    }
    fn exact(&self) -> Option<u16> {
        (self.start == self.stop).then_some(self.start)
    }
}
impl RangeType for MemoryValueU16 {
    type Base = u16;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Clone)]
struct MemoryValueI16 {
    start: i16,
    stop: i16,
}
impl From<i16> for MemoryValueI16 {
    fn from(x: i16) -> Self {
        Self { start: x, stop: x }
    }
}
impl Add for MemoryValueI16 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}

impl MemoryValueI16 {
    const ZERO: Self = Self { start: 0, stop: 0 };
    fn get_i8(&self, i: usize) -> Option<MemoryValueI16> {
        if i > 0 {
            return None;
        }
        Some(self.clone())
    }
    fn set_i8(&mut self, i: usize, n: i16) {
        assert!(i > 0);
        self.start = n;
        self.stop = n;
    }
    fn exact(&self) -> Option<i16> {
        (self.start == self.stop).then_some(self.start)
    }
}
impl RangeType for MemoryValueI16 {
    type Base = i16;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
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
impl RangeType for MemoryValueU8 {
    type Base = u8;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Error)]
enum MemoryValueU8GetError {
    #[error("Potentially access outside type with {0}")]
    Outside(MemoryValueI64),
}

impl MemoryValueU8 {
    const ZERO: Self = Self { start: 0, stop: 0 };

    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueU8GetError> {
        let end = *offset + MemoryValueI64::try_from(len.clone()).unwrap();
        let size = MemoryValueI64::from(size(&Type::U8) as i64);

        match end.compare(&size) {
            RangeOrdering::Less | RangeOrdering::Greater | RangeOrdering::Cover => {
                Err(MemoryValueU8GetError::Outside(end))
            }
            RangeOrdering::Equal => match offset.exact() {
                Some(0) => Ok(MemoryValue::U8(self.clone())),
                x => todo!("{x:?}"),
            },
            RangeOrdering::Within => match (offset.exact(), len.exact(), self.exact()) {
                (Some(o), Some(l), _) if l == size(&Type::U8) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::U8(self.clone()))
                }
                x => todo!("{x:?}"),
            },
            x => todo!("{x:?}"),
        }
    }

    fn exact(&self) -> Option<u8> {
        (self.start == self.stop).then_some(self.start)
    }
}

impl From<&Immediate> for RegisterValue {
    fn from(immediate: &Immediate) -> Self {
        // Store as the smallest value that can contain `immediate`.
        let v = immediate.value as i128;
        const I8_MIN: i128 = i8::MIN as i128;
        const U8_MIN: i128 = u8::MIN as i128;
        const U8_MAX: i128 = u8::MAX as i128;
        const U32_MIN: i128 = u32::MIN as i128;
        const U32_MAX: i128 = u32::MAX as i128;
        match v {
            I8_MIN..U8_MIN => RegisterValue::I8(MemoryValueI8::from(v as i8)),
            U8_MIN..=U8_MAX => RegisterValue::U8(MemoryValueU8::from(v as u8)),
            U32_MIN..=U32_MAX => RegisterValue::U32(MemoryValueU32::from(v as u32)),
            x @ _ => todo!("{x:?}"),
        }
    }
}

#[derive(Debug, Clone)]
struct MemoryValueU32 {
    start: u32,
    stop: u32,
}
impl From<MemoryValueU8> for MemoryValueU32 {
    fn from(MemoryValueU8 { start, stop }: MemoryValueU8) -> Self {
        MemoryValueU32 {
            start: u32::from(start),
            stop: u32::from(stop),
        }
    }
}
impl Add for MemoryValueU32 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            start: self.start + rhs.start,
            stop: self.stop + rhs.stop,
        }
    }
}
impl From<u32> for MemoryValueU32 {
    fn from(x: u32) -> Self {
        Self { start: x, stop: x }
    }
}
impl RangeType for MemoryValueU32 {
    type Base = u32;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

impl From<MemoryValue> for Type {
    fn from(mv: MemoryValue) -> Type {
        use MemoryValue::*;
        match mv {
            U64(_) => Type::U64,
            U32(_) => Type::U32,
            U16(_) => Type::U16,
            U8(_) => Type::U8,
            List(x) => Type::List(x.into_iter().map(Type::from).collect()),
            I8(_) => Type::I8,
            I64(_) => Type::I64,
            I16(_) => Type::I16,
            Ptr(_) => Type::I64,
            Csr(_) => todo!(),
        }
    }
}

#[derive(Debug, Error)]
enum MemoryValueU32GetError {
    #[error("Potentially access outside type with {0}")]
    Outside(MemoryValueI64),
}

impl MemoryValueU32 {
    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueU32GetError> {
        let end = *offset + MemoryValueI64::try_from(len.clone()).unwrap();

        match end.compare(&MemoryValueI64::from(size(&Type::U32) as i64)) {
            RangeOrdering::Less | RangeOrdering::Greater | RangeOrdering::Cover => {
                Err(MemoryValueU32GetError::Outside(end))
            }
            RangeOrdering::Equal => match offset.exact() {
                Some(0) => Ok(MemoryValue::U32(self.clone())),
                _ => todo!(),
            },
            RangeOrdering::Within => match (offset.exact(), len.exact(), self.exact()) {
                (Some(o), Some(l), Some(v)) if l == size(&Type::U8) => {
                    let byte = v.to_ne_bytes()[o as usize];
                    Ok(MemoryValue::U8(MemoryValueU8 {
                        start: byte,
                        stop: byte,
                    }))
                }
                (Some(o), Some(l), _) if l == size(&Type::U32) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::U32(self.clone()))
                }
                x => todo!("{x:?}"),
            },
            _ => todo!(),
        }
    }

    fn exact(&self) -> Option<u32> {
        (self.start == self.stop).then_some(self.start)
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
struct MemoryValueU64 {
    start: u64,
    stop: u64,
}
impl RangeType for MemoryValueU64 {
    type Base = u64;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
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

#[derive(Debug, Error)]
enum MemoryValueU64GetError {
    #[error("Potentially access outside type with {0}")]
    Outside(MemoryValueI64),
}

impl MemoryValueU64 {
    const ZERO: Self = Self { start: 0, stop: 0 };

    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueU64GetError> {
        let end = *offset + MemoryValueI64::try_from(len.clone()).unwrap();

        match end.compare(&MemoryValueI64::from(size(&Type::U64) as i64)) {
            RangeOrdering::Less | RangeOrdering::Greater | RangeOrdering::Cover => {
                Err(MemoryValueU64GetError::Outside(end))
            }
            RangeOrdering::Equal => match offset.exact() {
                Some(0) => Ok(MemoryValue::U64(self.clone())),
                _ => todo!(),
            },
            RangeOrdering::Within => match (offset.exact(), len.exact(), self.exact()) {
                (Some(o), Some(l), Some(v)) if l == size(&Type::U8) => {
                    let byte = v.to_ne_bytes()[o as usize];
                    Ok(MemoryValue::U8(MemoryValueU8 {
                        start: byte,
                        stop: byte,
                    }))
                }
                (Some(o), Some(l), _) if l == size(&Type::U64) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::U64(self.clone()))
                }
                x => todo!("{x:?}"),
            },
            _ => todo!(),
        }
    }
    fn exact(&self) -> Option<u64> {
        (self.start == self.stop).then_some(self.start)
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
trait RangeType {
    type Base: Eq + PartialEq + Ord + PartialOrd;
    fn start(&self) -> Self::Base;
    fn stop(&self) -> Self::Base;
    fn compare(&self, other: &Self) -> RangeOrdering {
        match (
            self.start().cmp(&other.start()),
            self.stop().cmp(&other.stop()),
        ) {
            (Ordering::Less, Ordering::Less) => RangeOrdering::Less,
            (Ordering::Greater, Ordering::Greater) => RangeOrdering::Greater,
            (Ordering::Equal, Ordering::Equal) => {
                if self.start() == self.stop() {
                    RangeOrdering::Equal
                } else {
                    RangeOrdering::Matches
                }
            }
            (Ordering::Less, Ordering::Greater) => RangeOrdering::Cover,
            (Ordering::Equal, Ordering::Greater) => RangeOrdering::Cover,
            (Ordering::Less, Ordering::Equal) => RangeOrdering::Cover,
            (Ordering::Greater, Ordering::Less) => RangeOrdering::Within,
            (Ordering::Equal, Ordering::Less) => RangeOrdering::Within,
            (Ordering::Greater, Ordering::Equal) => RangeOrdering::Within,
        }
    }
}
impl RangeType for MemoryValueI64 {
    type Base = i64;
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}
impl TryFrom<MemoryValueU64> for MemoryValueI64 {
    type Error = <i64 as TryFrom<u64>>::Error;
    fn try_from(MemoryValueU64 { start, stop }: MemoryValueU64) -> Result<Self, Self::Error> {
        Ok(Self {
            start: i64::try_from(start)?,
            stop: i64::try_from(stop)?,
        })
    }
}

/// The `Equal` variant is handled like this since if you have a value `x` in the
/// range 1..3 and a value `y` in the range 1..3 it would not be correct to say these
/// values are equal.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
enum RangeOrdering {
    /// 1..3 is less than 4..7
    Less,
    /// 4..7 is greater than 1..3
    Greater,
    /// 2..=2 equals 2..=2
    Equal,
    /// 1..7 covers 2..6
    Cover,
    /// 2..6 is within 1..7
    Within,
    /// 1..3 matches 1..3
    Matches,
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
    fn exact(&self) -> Option<i64> {
        (self.start == self.stop).then_some(self.start)
    }
}

fn set_into_list<T>(
    list: &mut [MemoryValue],
    i: &MemoryValueI64,
    closure: fn(&mut MemoryValue, &MemoryValueI64, T),
    n: T,
) -> Result<(), ()> {
    let mut iter = list.iter_mut();
    if let Some(item) = iter.next() {
        let mut current = MemoryValueI64 {
            start: 0,
            stop: size(&Type::from(&*item)) as i64,
        };

        for item in iter {
            // While the offset is less than an entry in the list iterate.
            let next = current + MemoryValueI64::from(size(&Type::from(&*item)) as i64);
            match i.compare(&current) {
                RangeOrdering::Equal => return Ok(closure(item, &MemoryValueI64::ZERO, n)),
                RangeOrdering::Within | RangeOrdering::Matches => {
                    return Ok(closure(item, &(*i - current), n))
                }
                RangeOrdering::Less => {}
                x => todo!("{x:?}"),
            }
            current = next;
        }
    }
    Err(())
}

// TODO Remove this, it should just be a list.
#[derive(Debug)]
struct MemoryValueType {
    type_value: FlatType,
    addr: Option<MemoryLabel>,
    length: usize,
    locality: Locality,
}

#[derive(Debug, Error)]
enum MemoryValueTypeGetU64Error {
    #[error("Address is below type.")]
    TooLow,
    #[error("Address is above type.")]
    TooHigh,
    #[error("Type doesn't have an address.")]
    NoAddress,
    #[error("todo: {0}")]
    Todo(MemoryValueI64),
}

impl MemoryValueType {
    fn get_u64(
        &self,
        offset: &MemoryValueI64,
    ) -> Result<DoubleWordValue, MemoryValueTypeGetU64Error> {
        if let Some(exact) = offset.exact() {
            match exact {
                ..0 => Err(MemoryValueTypeGetU64Error::TooLow),
                0 => Ok(DoubleWordValue::Literal(MemoryValueU64::from(
                    self.type_value as u64,
                ))),
                1..8 => Err(MemoryValueTypeGetU64Error::Todo(*offset)),
                8 => self
                    .addr
                    .as_ref()
                    .map(|l| {
                        DoubleWordValue::Address(MemoryPtr(Some(NonNullMemoryPtr {
                            tag: l.clone(),
                            offset: MemoryValueI64::ZERO,
                        })))
                    })
                    .ok_or(MemoryValueTypeGetU64Error::NoAddress),
                9..16 => Err(MemoryValueTypeGetU64Error::Todo(*offset)),
                16 => Ok(DoubleWordValue::Literal(MemoryValueU64::from(self.length))),
                17 => Err(MemoryValueTypeGetU64Error::Todo(*offset)),
                18.. => Err(MemoryValueTypeGetU64Error::TooHigh),
            }
        } else {
            Err(MemoryValueTypeGetU64Error::Todo(*offset))
        }
    }
    fn type_of() -> Type {
        Type::List(vec![Type::U64, Type::U64, Type::U64, Type::U8])
    }
}

#[derive(Debug, Clone)]
enum RegisterValue {
    U64(MemoryValueU64),
    U32(MemoryValueU32),
    U16(MemoryValueU16),
    U8(MemoryValueU8),
    List(Vec<RegisterValue>),
    I8(MemoryValueI8),
    I64(MemoryValueI64),
    I16(MemoryValueI16),
    Address(MemoryPtr),
    Csr(CsrValue),
}

impl From<DoubleWordValue> for RegisterValue {
    fn from(x: DoubleWordValue) -> Self {
        match x {
            DoubleWordValue::Literal(y) => Self::U64(y),
            DoubleWordValue::Address(y) => Self::Address(y),
        }
    }
}
impl Add for MemoryValue {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        use MemoryValue::*;
        match (self, rhs) {
            (U8(a), U8(b)) => U8(a + b),
            (Ptr(MemoryPtr(None)), _) => Ptr(MemoryPtr(None)),
            (Ptr(MemoryPtr(Some(mut a))), U8(b)) => {
                let c = MemoryValueI64::from(b);
                a.offset = a.offset + c;
                Ptr(MemoryPtr(Some(a)))
            }
            (Ptr(MemoryPtr(Some(mut a))), I8(b)) => {
                let c = MemoryValueI64::from(b);
                a.offset = a.offset + c;
                Ptr(MemoryPtr(Some(a)))
            }
            (U32(a), U8(b)) => U32(a + MemoryValueU32::from(b)),
            x => todo!("{x:?}"),
        }
    }
}

#[derive(Debug, Clone)]
enum DoubleWordValue {
    Literal(MemoryValueU64),
    Address(MemoryPtr),
}

#[derive(Debug, Clone)]
#[non_exhaustive]
enum CsrValue {
    Mhartid,
}

// `wfi` is less racy than instructions like `sw` or `lw` so we could treat it more precisely
// and allow a larger domain of possible programs. But for now, we treat it like `sw` or
// `lw` this means there exist some valid usecases that this will report as invalid, and
// for valid use cases it will be slower as it needs to explore and validate paths it
// doesn't need to theoritically do.

/// Each execution path is based on the initial types assumed for each variables encountered and the locality assumed for each variable encountered.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramConfiguration(BTreeMap<Label, (LabelLocality, Type)>);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum LabelLocality {
    // If the locality is thread, we want to record which threads need a copy.
    Thread(BTreeSet<u8>),
    Global,
}
impl<'a> From<&'a LabelLocality> for &'a Locality {
    fn from(ll: &'a LabelLocality) -> &'a Locality {
        match ll {
            LabelLocality::Thread(_) => &Locality::Thread,
            LabelLocality::Global => &Locality::Global,
        }
    }
}

impl From<Locality> for LabelLocality {
    fn from(locality: Locality) -> Self {
        match locality {
            Locality::Global => Self::Global,
            Locality::Thread => Self::Thread(BTreeSet::new()),
        }
    }
}

impl ProgramConfiguration {
    fn append(&mut self, other: ProgramConfiguration) {
        for (label, (locality, ttype)) in other.0.into_iter() {
            match locality {
                LabelLocality::Global => {
                    assert!(!self.0.contains_key(&label));
                    self.0.insert(label, (LabelLocality::Global, ttype));
                }
                LabelLocality::Thread(harts) => {
                    for hart in harts {
                        self.insert(label.clone(), hart, (Locality::Thread, ttype.clone()));
                    }
                }
            }
        }
    }
    fn insert(&mut self, key: Label, hart: u8, (locality, ttype): (Locality, Type)) {
        match locality {
            Locality::Global => {
                let res = self.0.insert(key, (LabelLocality::Global, ttype));
                assert!(res.is_none());
            }
            Locality::Thread => {
                if let Some((existing_locality, existing_ttype)) = self.0.get_mut(&key) {
                    assert_eq!(*existing_ttype, ttype);
                    let LabelLocality::Thread(threads) = existing_locality else {
                        panic!()
                    };
                    threads.insert(hart);
                } else {
                    let mut set = BTreeSet::new();
                    set.insert(hart);
                    self.0.insert(key, (LabelLocality::Thread(set), ttype));
                }
            }
        }
    }
    fn get(&self, key: &Label) -> Option<(&Locality, &Type)> {
        self.0.get(key).map(|(l, t)| (l.into(), t))
    }
    fn new() -> Self {
        Self(BTreeMap::new())
    }
}

pub struct Explorerer {
    pub harts_range: Range<u8>,
    pub excluded: BTreeSet<ProgramConfiguration>,
    /// Pointer to the 2nd element in the AST (e.g. it skips the 1st which is `.global _start`).
    pub second_ptr: NonNull<AstNode>,
    pub roots: Vec<NonNull<VerifierHarts>>,
}

impl Explorerer {
    pub unsafe fn new_path(this: Rc<RefCell<Self>>) -> ExplorererPath {
        let this_ref = this.borrow_mut();
        // Record the initial types used for variables in this verification path.
        // Different harts can treat the same variables as different types, they have
        // different inputs and often follow different execution paths (effectively having a different AST).
        let configuration = ProgramConfiguration::new();

        // To remove uneeded code (e.g. a branch might always be true so we remove the code it skips)
        // we record all the AST instructions that get touched.
        let touched = BTreeSet::<NonNull<AstNode>>::new();

        let queue = this_ref
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
                                node: this_ref.second_ptr,
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
        drop(this_ref);

        ExplorererPath {
            explorerer: this,
            configuration,
            touched,
            queue,
        }
    }

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
pub struct ExplorererPath {
    // This could be a mutable reference. Its a `Rc<RefCell<_>>` becuase the borrow checker can't
    // figure out its safe and I don't want to rework the code right now to help it.
    pub explorerer: Rc<RefCell<Explorerer>>,

    pub configuration: ProgramConfiguration,

    pub touched: BTreeSet<NonNull<AstNode>>,
    pub queue: VecDeque<NonNull<VerifierNode>>,
}

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
    hart: u8,
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
            config.insert(label.clone(), hart, (locality, ttype));

            if !excluded.contains(&config) {
                *configuration = config;
                return true;
            }
        }
    }
    false
}

pub enum ExplorePathResult {
    Valid {
        configuration: ProgramConfiguration,
        touched: BTreeSet<NonNull<AstNode>>,
    },
    Invalid {
        complete: bool,
        path: String,
        explanation: InvalidExplanation,
    },
    Continue(ExplorererPath),
}
impl ExplorePathResult {
    pub fn continued(self) -> Option<ExplorererPath> {
        match self {
            Self::Continue(c) => Some(c),
            _ => None,
        }
    }
}

use itertools::intersperse;
use tracing::debug;
impl ExplorererPath {
    pub unsafe fn next_step(
        Self {
            explorerer,
            mut configuration,
            mut touched,
            mut queue,
        }: Self,
    ) -> ExplorePathResult {
        trace!("excluded: {:?}", explorerer.borrow().excluded);
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
                        item_ref.node.as_ref().span
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
            branch_ptr.as_ref().node.as_ref().span
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
                    &mut explorerer.borrow_mut().excluded,
                    cast.clone(),
                    *locality,
                    hart,
                ) {
                    return invalid_path(
                        explorerer.clone(),
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
                    &mut explorerer.borrow_mut().excluded,
                    None,
                    None,
                    hart,
                ) {
                    return invalid_path(
                        explorerer.clone(),
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
                    &mut explorerer.borrow_mut().excluded,
                    None,
                    None,
                    hart,
                ) {
                    return invalid_path(
                        explorerer.clone(),
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
                if let Some(res) = check_store(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    to,
                    offset,
                    4,
                    InvalidExplanation::Sw,
                ) {
                    return res;
                }
            }
            Instruction::Sb(Sb {
                to,
                from: _,
                offset,
            }) => {
                if let Some(res) = check_store(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    to,
                    offset,
                    1,
                    InvalidExplanation::Sb,
                ) {
                    return res;
                }
            }
            // TODO A lot of the checking loads code is duplicated, reduce this duplication.
            // For any load we need to validate the destination is valid.
            Instruction::Ld(Ld {
                to: _,
                from,
                offset,
            }) => {
                if let Some(res) = check_load(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    from,
                    offset,
                    8,
                    InvalidExplanation::Ld,
                ) {
                    return res;
                }
            }
            Instruction::Lw(Lw {
                to: _,
                from,
                offset,
            }) => {
                if let Some(res) = check_load(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    from,
                    offset,
                    4,
                    InvalidExplanation::Lw,
                ) {
                    return res;
                }
            }
            Instruction::Lb(Lb {
                to: _,
                from,
                offset,
            }) => {
                let opt = check_load(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    from,
                    offset,
                    1,
                    InvalidExplanation::Lb,
                );
                if let Some(res) = opt {
                    return res;
                }
            }
            // If any fail is encountered then the path is invalid.
            Instruction::Fail(_) => {
                return invalid_path(
                    explorerer.clone(),
                    configuration,
                    harts,
                    InvalidExplanation::Fail,
                )
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

unsafe fn check_store(
    explorerer: Rc<RefCell<Explorerer>>,
    branch_ptr: NonNull<VerifierNode>,
    branch: &VerifierNode,
    configuration: &ProgramConfiguration,
    to: &Register,
    offset: &crate::ast::Offset,
    type_size: i64,
    invalid: InvalidExplanation,
) -> Option<ExplorePathResult> {
    // Collect the state.
    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
    let state = find_state(&record, root, harts, first_step, &configuration);

    // Check the destination is valid.
    match state.registers[branch.hart as usize].get(to) {
        Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
            tag: from_label,
            offset: from_offset,
        })))) => {
            let (_locality, ttype) = state.configuration.get(from_label.into()).unwrap();
            // If attempting to access outside the memory space for the label.
            let full_offset = MemoryValueI64::from(type_size)
                + *from_offset
                + MemoryValueI64::from(offset.value.value);
            let size = MemoryValueI64::try_from(size(ttype) as i64).unwrap();
            match size.compare(&full_offset) {
                RangeOrdering::Less | RangeOrdering::Within => {
                    // The path is invalid, so we add the current types to the
                    // excluded list and restart exploration.
                    return Some(invalid_path(
                        explorerer.clone(),
                        configuration.clone(),
                        harts,
                        invalid,
                    ));
                }
                RangeOrdering::Greater | RangeOrdering::Matches | RangeOrdering::Equal => {
                    // Else we found the label and we can validate that the loading
                    // of a word with the given offset is within the address space.
                    // So we continue exploration.
                    None
                }
                RangeOrdering::Cover => unreachable!(),
            }
        }
        x => todo!("{x:?}"),
    }
}

use std::cell::RefCell;

/// Verifies a load is valid for a given configuration.
unsafe fn check_load(
    explorerer: Rc<RefCell<Explorerer>>,
    branch_ptr: NonNull<VerifierNode>,
    branch: &VerifierNode,
    configuration: &ProgramConfiguration,
    from: &Register,
    offset: &crate::ast::Offset,
    type_size: i64,
    invalid: InvalidExplanation,
) -> Option<ExplorePathResult> {
    // Collect the state.
    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
    let state = find_state(&record, root, harts, first_step, &configuration);

    // Check the destination is valid.
    match state.registers[branch.hart as usize].get(from) {
        Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
            tag: from_label,
            offset: from_offset,
        })))) => {
            let (_locality, ttype) = state.configuration.get(from_label.into()).unwrap();

            // If attempting to access outside the memory space for the label.
            let full_offset = MemoryValueI64::from(type_size)
                + MemoryValueI64::from(offset.value.value)
                + *from_offset;
            let size = MemoryValueI64::try_from(size(ttype) as i64).unwrap();
            match size.compare(&full_offset) {
                RangeOrdering::Less | RangeOrdering::Within => {
                    // The path is invalid, so we add the current types to the
                    // excluded list and restart exploration.
                    return Some(invalid_path(
                        explorerer.clone(),
                        configuration.clone(),
                        harts,
                        invalid,
                    ));
                }
                RangeOrdering::Greater | RangeOrdering::Matches | RangeOrdering::Equal => {
                    // Else, we found the label and we can validate that the loading
                    // of a word with the given offset is within the address space.
                    // So we continue exploration.
                    None
                }
                RangeOrdering::Cover => unreachable!(),
            }
        }
        x => todo!("{x:?}"),
    }
}

impl From<&LabelLocality> for Locality {
    fn from(ll: &LabelLocality) -> Locality {
        match ll {
            LabelLocality::Thread(_) => Locality::Thread,
            LabelLocality::Global => Locality::Global,
        }
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
    #[error("todo")]
    Sb,
    #[error("todo")]
    Ld,
    #[error("todo")]
    Lw,
    #[error("todo")]
    Lb,
    #[error("todo")]
    Fail,
}

unsafe fn invalid_path(
    explorerer: Rc<RefCell<Explorerer>>,
    configuration: ProgramConfiguration,
    harts: u8,
    explanation: InvalidExplanation,
) -> ExplorePathResult {
    let mut explorer_ref = explorerer.borrow_mut();
    // We need to track covered ground so we don't retread it.
    explorer_ref.excluded.insert(configuration.clone());

    trace!("excluded: {:?}", explorer_ref.excluded);

    let harts_root = explorer_ref
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
    for mut root in explorer_ref.roots.iter().copied() {
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

// Get the number of harts of this sub-tree and record the path.
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

unsafe fn queue_up(
    prev: NonNull<VerifierNode>,
    queue: &mut VecDeque<NonNull<VerifierNode>>,
    configuration: &ProgramConfiguration,
) {
    let (record, root, harts, first_step) = get_backpath_harts(prev);
    // TOOD We duplicate so much work doing `find_state` in a bunch of places and
    // multiple times when the state hasn't change, we should avoid doing this call
    // here (and remove the it in other places).
    let state = find_state(&record, root, harts, first_step, configuration);

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
                if let MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr { tag, offset: _ }))) =
                    value
                {
                    match tag {
                        // Racy
                        MemoryLabel::Global { label: _ } => Some(Ok((hart, node))),
                        // Non-racy
                        MemoryLabel::Thread {
                            label: _,
                            hart: thart,
                        } => {
                            assert_eq!(*thart, hart);
                            Some(Err((hart, node)))
                        }
                    }
                } else {
                    todo!()
                }
            }
            // See note on `wfi`.
            Instruction::Wfi(_) => Some(Ok((hart, node))),
            x => todo!("{x:?}"),
        }
    };

    // The lowest hart non-racy node is enqueued.
    // (or possibly multiples nodes in the case of a conditional jump where
    // we cannot deteremine the condition).

    let next_nodes = fronts
        .iter()
        // TODO Document why reverse order is important here.
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
                                if ord == RangeOrdering::Less {
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
                                if ord == RangeOrdering::Equal {
                                    let label_node = find_label(node, out).unwrap();
                                    followup(label_node, hart)
                                } else {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        x => todo!("{x:?}"),
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
                                if ord == RangeOrdering::Equal {
                                    followup(node_ref.next.unwrap(), hart)
                                } else {
                                    let label_node = find_label(node, out).unwrap();
                                    followup(label_node, hart)
                                }
                            } else {
                                todo!()
                            }
                        }
                        x => todo!("{x:?}"),
                    }
                }
                Instruction::Bnez(Bnez { src, dest }) => {
                    let state = find_state(&record, root, harts, first_step, configuration);

                    let src = state.registers[hart as usize].get(src);

                    // In the case the path is determinate, we either queue up the label
                    // or the next ast node and don't need to actually visit/evaluate
                    // the branch at runtime.
                    match src {
                        Some(MemoryValue::I8(imm)) => match imm.compare(&MemoryValueI8::ZERO) {
                            RangeOrdering::Less | RangeOrdering::Greater => {
                                let label_node = find_label(node, dest).unwrap();
                                followup(label_node, hart)
                            }
                            RangeOrdering::Equal => followup(node_ref.next.unwrap(), hart),
                            _ => todo!(),
                        },
                        Some(MemoryValue::U8(imm)) => match imm.compare(&MemoryValueU8::ZERO) {
                            RangeOrdering::Less | RangeOrdering::Greater => {
                                let label_node = find_label(node, dest).unwrap();
                                followup(label_node, hart)
                            }
                            RangeOrdering::Equal => followup(node_ref.next.unwrap(), hart),
                            _ => todo!(),
                        },
                        Some(MemoryValue::Csr(CsrValue::Mhartid)) => {
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
                        Some(MemoryValue::U8(imm)) => match imm.compare(&MemoryValueU8::ZERO) {
                            RangeOrdering::Equal => {
                                let label_node = find_label(node, label).unwrap();
                                followup(label_node, hart)
                            }
                            RangeOrdering::Less | RangeOrdering::Greater => {
                                followup(node_ref.next.unwrap(), hart)
                            }
                            _ => todo!(),
                        },
                        Some(MemoryValue::I8(imm)) => match imm.compare(&MemoryValueI8::ZERO) {
                            RangeOrdering::Equal => {
                                let label_node = find_label(node, label).unwrap();
                                followup(label_node, hart)
                            }
                            RangeOrdering::Less | RangeOrdering::Greater => {
                                followup(node_ref.next.unwrap(), hart)
                            }
                            _ => todo!(),
                        },
                        Some(MemoryValue::Csr(CsrValue::Mhartid)) => {
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
                                    RangeOrdering::Greater => {
                                        let label_node = find_label(node, out).unwrap();
                                        followup(label_node, hart)
                                    }
                                    RangeOrdering::Less => followup(node_ref.next.unwrap(), hart),
                                    _ => todo!(),
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
                x => todo!("{x:?}"),
            }
        })
        .collect::<Result<Vec<_>, _>>();

    debug!("racy: {}", next_nodes.is_ok());

    debug!(
        "next: {:?}",
        next_nodes
            .as_ref()
            .map(|racy| racy
                .iter()
                .map(|(h, n)| format!(
                    "{{ hart: {h}, instruction: {} }}",
                    n.as_ref().this.to_string()
                ))
                .collect::<Vec<_>>())
            .map_err(|(h, n)| format!(
                "{{ hart: {h}, instruction: {} }}",
                n.as_ref().this.to_string()
            ))
    );
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
                let mem_value = MemoryValue::from(*immediate);
                state.registers[hartu].insert(*register, mem_value);
            }
            // TOOD This is the only place where in finding state we need to modify `state.configuration`
            // is this the best way to do this? Could these types not be defined in `next_step` (like `la`)?
            Instruction::Lat(Lat { register, label }) => {
                let (_locality, typeof_type) = state.configuration.get(label).unwrap();
                let (loc, subtypes) = state.memory.set_type(typeof_type, &mut tag_iter, hart);
                state.registers[hartu].insert(
                    *register,
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: loc.clone(),
                        offset: MemoryValueI64::ZERO,
                    }))),
                );

                // Each type type is thread local and unique between `lat` instructions.
                let hart_type_state = &mut state.configuration;
                hart_type_state.insert(
                    loc.into(),
                    hart,
                    (Locality::Thread, MemoryValueType::type_of()),
                );
                // Extend with subtypes.
                hart_type_state.append(subtypes);
            }
            Instruction::La(La { register, label }) => {
                let (locality, _to_type) = state.configuration.get(label).unwrap();
                state.registers[hartu].insert(
                    *register,
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: match locality {
                            Locality::Global => MemoryLabel::Global {
                                label: label.clone(),
                            },
                            Locality::Thread => MemoryLabel::Thread {
                                label: label.clone(),
                                hart,
                            },
                        },
                        offset: MemoryValueI64::ZERO,
                    }))),
                );
            }
            Instruction::Sw(Sw { to, from, offset }) => {
                let Some(to_value) = state.registers[hartu].get(to) else {
                    todo!()
                };
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match to_value {
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: to_label,
                        offset: to_offset,
                    }))) => {
                        let (locality, to_type) = state.configuration.get(to_label.into()).unwrap();
                        // We should have already checked the type is large enough for the store.
                        let sizeof = MemoryValueI64::from(size(to_type) as i64);
                        let final_offset = MemoryValueI64::from(4)
                            + *to_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            RangeOrdering::Greater | RangeOrdering::Equal
                        ));
                        debug_assert_eq!(locality, <&Locality>::from(to_label));
                        match from_value {
                            MemoryValue::U32(from_imm) => {
                                if let Some(imm) = from_imm.exact() {
                                    let memloc = MemoryPtr(Some(NonNullMemoryPtr {
                                        tag: to_label.clone(),
                                        offset: *to_offset
                                            + MemoryValueI64::from(offset.value.value),
                                    }));
                                    state.memory.set_u32(&memloc, imm);
                                } else {
                                    todo!()
                                }
                            }
                            MemoryValue::U8(from_imm) => {
                                if let Some(imm) = from_imm.exact() {
                                    let memloc = MemoryPtr(Some(NonNullMemoryPtr {
                                        tag: to_label.clone(),
                                        offset: *to_offset
                                            + MemoryValueI64::from(offset.value.value),
                                    }));
                                    state.memory.set_u32(&memloc, u32::from(imm));
                                } else {
                                    todo!()
                                }
                            }
                            x @ _ => todo!("{x:?}"),
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
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: to_label,
                        offset: to_offset,
                    }))) => {
                        let (locality, to_type) = state.configuration.get(to_label.into()).unwrap();
                        // We should have already checked the type is large enough for the store.
                        let sizeof = MemoryValueI64::from(size(to_type) as i64);
                        let final_offset = MemoryValueI64::from(1)
                            + *to_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            RangeOrdering::Greater | RangeOrdering::Equal
                        ));
                        debug_assert_eq!(locality, <&Locality>::from(to_label));
                        match from_value {
                            MemoryValue::U8(from_imm) => {
                                let memloc = MemoryPtr(Some(NonNullMemoryPtr {
                                    tag: to_label.clone(),
                                    offset: *to_offset
                                        + MemoryValueI64::from(offset.value.value),
                                }));
                                state.memory.set(&memloc, MemoryValue::U8(from_imm.clone()));
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
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: from_label,
                        offset: from_offset,
                    }))) => {
                        let (locality, from_type) =
                            state.configuration.get(from_label.into()).unwrap();
                        // We should have already checked the type is large enough for the load.
                        let sizeof = MemoryValueI64::from(size(from_type) as i64);
                        let final_offset = MemoryValueI64::from(8)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);

                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            RangeOrdering::Greater | RangeOrdering::Equal
                        ));
                        debug_assert_eq!(locality, <&Locality>::from(from_label));

                        let memloc = Slice {
                            base: from_label.clone(),
                            offset: *from_offset + MemoryValueI64::from(offset.value.value),
                            len: MemoryValueU64::from(size(&Type::U64)),
                        };
                        let value = state.memory.get(&memloc).unwrap();
                        state.registers[hartu].insert(*to, value);
                    }
                    x => todo!("{x:?}"),
                }
            }
            Instruction::Lw(Lw { to, from, offset }) => {
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: from_label,
                        offset: from_offset,
                    }))) => {
                        let (locality, from_type) =
                            state.configuration.get(from_label.into()).unwrap();
                        // We should have already checked the type is large enough for the load.
                        let sizeof = MemoryValueI64::from(size(from_type) as i64);
                        let final_offset = MemoryValueI64::from(4)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            RangeOrdering::Greater | RangeOrdering::Equal
                        ));
                        debug_assert_eq!(locality, <&Locality>::from(from_label));
                        let memloc = Slice {
                            base: from_label.clone(),
                            offset: *from_offset + MemoryValueI64::from(offset.value.value),
                            len: MemoryValueU64::from(size(&Type::U32)),
                        };
                        let mem_value = state.memory.get(&memloc).unwrap();
                        state.registers[hartu].insert(*to, mem_value);
                    }
                    _ => todo!(),
                }
            }
            Instruction::Lb(Lb { to, from, offset }) => {
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag: from_label,
                        offset: from_offset,
                    }))) => {
                        let (locality, from_type) =
                            state.configuration.get(from_label.into()).unwrap();
                        // We should have already checked the type is large enough for the load.
                        let sizeof = MemoryValueI64::from(size(from_type) as i64);
                        let final_offset = MemoryValueI64::from(1)
                            + *from_offset
                            + MemoryValueI64::from(offset.value.value);
                        debug_assert!(matches!(
                            sizeof.compare(&final_offset),
                            RangeOrdering::Greater | RangeOrdering::Equal
                        ));
                        debug_assert_eq!(locality, <&Locality>::from(from_label));
                        let memloc = Slice {
                            base: from_label.clone(),
                            offset: *from_offset + MemoryValueI64::from(offset.value.value),
                            len: MemoryValueU64::from(size(&Type::U8)),
                        };
                        let mem_value = state.memory.get(&memloc).unwrap();
                        state.registers[hartu].insert(*to, mem_value);
                    }
                    _ => todo!(),
                }
            }
            Instruction::Addi(Addi { out, lhs, rhs }) => {
                let lhs_value = state.registers[hartu].get(lhs).cloned().unwrap();
                let rhs_value = MemoryValue::from(*rhs);
                dbg!(&lhs_value);
                dbg!(&rhs_value);
                let out_value = lhs_value + rhs_value;
                dbg!(&out_value);
                state.registers[hartu].insert(*out, out_value);
            }
            #[allow(unreachable_patterns)]
            Instruction::Csrr(Csrr { dest, src }) => match src {
                Csr::Mhartid => {
                    state.registers[hartu].insert(*dest, MemoryValue::Csr(CsrValue::Mhartid));
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
