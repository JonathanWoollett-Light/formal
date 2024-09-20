use crate::ast::*;
use num::traits::ToBytes;
use num::CheckedAdd;
use num::CheckedSub;
use std::alloc::Layout;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::hash::Hash;
use std::iter::once;
use std::iter::Peekable;
use std::ops::Add;
use std::ops::Range;
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

#[derive(Debug, Clone)]
pub struct MemoryValueI8 {
    pub start: i8,
    pub stop: i8,
}
impl From<i8> for MemoryValueI8 {
    fn from(x: i8) -> Self {
        Self { start: x, stop: x }
    }
}

impl MemoryValueI8 {
    const ZERO: Self = Self { start: 0, stop: 0 };
}
impl RangeType for MemoryValueI8 {
    type Base = i8;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Clone)]
pub struct MemoryValueU16 {
    pub start: u16,
    pub stop: u16,
}
impl From<u16> for MemoryValueU16 {
    fn from(x: u16) -> Self {
        Self { start: x, stop: x }
    }
}

impl MemoryValueU16 {
    const ZERO: Self = Self { start: 0, stop: 0 };
}
impl RangeType for MemoryValueU16 {
    type Base = u16;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Clone)]
pub struct MemoryValueI16 {
    pub start: i16,
    pub stop: i16,
}
impl From<i16> for MemoryValueI16 {
    fn from(x: i16) -> Self {
        Self { start: x, stop: x }
    }
}

impl MemoryValueI16 {
    const ZERO: Self = Self { start: 0, stop: 0 };
}
impl RangeType for MemoryValueI16 {
    type Base = i16;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Clone)]
pub struct MemoryValueU8 {
    pub start: u8,
    pub stop: u8,
}
impl From<u8> for MemoryValueU8 {
    fn from(x: u8) -> Self {
        Self { start: x, stop: x }
    }
}
impl RangeType for MemoryValueU8 {
    type Base = u8;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

#[derive(Debug, Error)]
pub enum MemoryValueU8GetError {
    #[error("Potentially access outside type with {0:?}")]
    Outside(MemoryValueU64),
}

impl MemoryValueU8 {
    const ZERO: Self = Self { start: 0, stop: 0 };

    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueU8GetError> {
        let end = offset
            .clone()
            .add(&MemoryValueU64::from(len.clone()))
            .unwrap();
        let value_size = size(&Type::U8);
        match end.lte(&value_size) {
            false => Err(MemoryValueU8GetError::Outside(end)),
            true => match (offset.exact(), self.exact()) {
                (Some(o), _) if *len == size(&Type::U8) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::U8(self.clone()))
                }
                x => todo!("{x:?}"),
            },
        }
    }
}
impl MemoryValueU32 {
    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueU32GetError> {
        let end = offset.clone().add(&MemoryValueU64::from(*len)).unwrap();
        let value_size = size(&Type::U32);

        match end.lte(&value_size) {
            false => Err(MemoryValueU32GetError::Outside(end)),
            true => match (offset.exact(), self.exact()) {
                (Some(o), Some(v)) if *len == size(&Type::U8) => {
                    let byte = v.to_ne_bytes()[o as usize];
                    Ok(MemoryValue::U8(MemoryValueU8 {
                        start: byte,
                        stop: byte,
                    }))
                }
                (Some(o), _) if *len == size(&Type::U32) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::U32(self.clone()))
                }
                x => todo!("{x:?}"),
            },
        }
    }
}

impl RangeType for MemoryValueU32 {
    type Base = u32;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

impl RangeType for MemoryValueI64 {
    type Base = i64;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
    fn start(&self) -> Self::Base {
        self.start
    }
    fn stop(&self) -> Self::Base {
        self.stop
    }
}

pub trait RangeType {
    type Base: Eq + Copy+PartialEq + Ord + PartialOrd + num::CheckedAdd + num::CheckedSub + num::traits::ToBytes + num::traits::FromBytes;
    fn start(&self) -> Self::Base;
    fn stop(&self) -> Self::Base;
    /// Returns if the given scalar is greater than, less than or within `self`.
    fn compare_scalar(&self, other: &Self::Base) -> RangeScalarOrdering {
        match (other.cmp(&self.start()), other.cmp(&self.stop())) {
            (Ordering::Greater, Ordering::Greater) => RangeScalarOrdering::Greater,
            (Ordering::Less, Ordering::Less) => RangeScalarOrdering::Less,
            (Ordering::Greater, Ordering::Less) => RangeScalarOrdering::Within,
            (Ordering::Equal, Ordering::Equal) => RangeScalarOrdering::Within,
            (Ordering::Greater, Ordering::Equal) => RangeScalarOrdering::Within,
            (Ordering::Equal, Ordering::Less) => RangeScalarOrdering::Within,
            _ => unreachable!(),
        }
    }
    /// Less than or equal to a given scalar.
    fn lte(&self, other: &Self::Base) -> bool {
        match self.stop().cmp(other) {
            Ordering::Less | Ordering::Equal => true,
            Ordering::Greater => false,
        }
    }
    /// Equal to a given scalar.
    fn eq(&self, other: &Self::Base) -> bool {
        match (self.start().cmp(other), self.stop().cmp(other)) {
            (Ordering::Equal, Ordering::Equal) => true,
            _ => false,
        }
    }
    fn new_exact(exact: Self::Base) -> Self
    where
        Self: Sized,
    {
        Self::new(exact,exact).unwrap()
    }
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self>
    where
        Self: Sized;
    /// 4..8 + 2..4 = 6..12
    fn add(&self, other: &Self) -> Option<Self>
    where
        Self: Sized,
    {
        let start = self.start().checked_add(&other.start())?;
        let stop = self.stop().checked_add(&other.stop())?;
        Self::new(start, stop)
    }
    /// 4..8 - 2..4 = 0..6
    fn sub(&self, other: &Self) -> Option<Self>
    where
        Self: Sized,
    {
        let start = self.start().checked_sub(&other.stop())?;
        let stop = self.stop().checked_sub(&other.start())?;
        Self::new(start, stop)
    }
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
    fn exact(&self) -> Option<Self::Base> {
        (self.start() == self.stop()).then_some(self.start())
    }
    fn to_bytes(&self) -> Option<<Self::Base as num::traits::ToBytes>::Bytes> {
        self.exact().map(|e|e.to_ne_bytes())
    }
    fn from_bytes(bytes: &<Self::Base as num::traits::FromBytes>::Bytes) -> Self where
        Self: Sized, {
        Self::new_exact(<Self::Base as num::traits::FromBytes>::from_ne_bytes(&bytes))
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

impl TryFrom<usize> for MemoryValueI64 {
    type Error = <i64 as TryFrom<usize>>::Error;
    fn try_from(x: usize) -> Result<Self, Self::Error> {
        let y = i64::try_from(x)?;
        Ok(Self { start: y, stop: y })
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

#[derive(Debug, Error)]
pub enum MemoryValueI64GetError {
    #[error("Potentially access outside type with {0:?}")]
    Outside(MemoryValueU64),
}

impl MemoryValueI64 {
    pub const ZERO: Self = Self { start: 0, stop: 0 };
    pub fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueI64GetError> {
        let end = offset.clone().add(&MemoryValueU64::from(*len)).unwrap();
        let value_size = size(&Type::I64);

        match end.lte(&value_size) {
            false => Err(MemoryValueI64GetError::Outside(end)),
            true => match (offset.exact(), self.exact()) {
                (Some(o), Some(v)) if *len == size(&Type::U8).into() => {
                    let byte = v.to_ne_bytes()[o as usize];
                    Ok(MemoryValue::U8(MemoryValueU8 {
                        start: byte,
                        stop: byte,
                    }))
                }
                (Some(o), Some(v)) if *len == size(&Type::U32).into() => {
                    let a = o as usize;
                    let b = a + *len as usize;
                    let bytes = <[u8; 4]>::try_from(&v.to_ne_bytes()[a..b]).unwrap();
                    let integer = u32::from_ne_bytes(bytes);
                    Ok(MemoryValue::U32(MemoryValueU32 {
                        start: integer,
                        stop: integer,
                    }))
                }
                (Some(o), _) if *len == size(&Type::U64).into() => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::I64(self.clone()))
                }
                x => todo!("{x:?}"),
            },
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub enum RangeScalarOrdering {
    /// 3 is less than 4..7
    Less,
    /// 8 is greater than 4..7
    Greater,
    /// 5 is within 4..7
    Within,
}

/// The `Equal` variant is handled like this since if you have a value `x` in the
/// range 1..3 and a value `y` in the range 1..3 it would not be correct to say these
/// values are equal.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub enum RangeOrdering {
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

#[derive(Debug, Error)]
pub enum MemoryValueU32GetError {
    #[error("Potentially access outside type with {0:?}")]
    Outside(MemoryValueU64),
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct MemoryValueU64 {
    pub start: u64,
    pub stop: u64,
}
impl RangeType for MemoryValueU64 {
    type Base = u64;
    fn new(start: Self::Base, stop: Self::Base) -> Option<Self> {
        match start.cmp(&stop) {
            Ordering::Less => None,
            Ordering::Equal | Ordering::Greater => Some(Self { start, stop }),
        }
    }
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
impl From<MemoryValueU8> for MemoryValueU64 {
    fn from(x: MemoryValueU8) -> Self {
        Self {
            start: x.start as u64,
            stop: x.stop as u64,
        }
    }
}
impl TryFrom<MemoryValueI64> for MemoryValueU64 {
    type Error = <u64 as TryFrom<i64>>::Error;
    fn try_from(other: MemoryValueI64) -> Result<Self, Self::Error> {
        Ok(Self {
            start: u64::try_from(other.start)?,
            stop: u64::try_from(other.stop)?,
        })
    }
}

#[derive(Debug, Error)]
pub enum MemoryValueU64GetError {
    #[error("Potentially access outside type with {0:?}")]
    Outside(MemoryValueU64),
}

impl MemoryValueU64 {
    pub const ZERO: Self = Self { start: 0, stop: 0 };

    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValueU64GetError> {
        let end = offset.clone().add(&MemoryValueU64::from(*len)).unwrap();
        let value_size = size(&Type::U64);

        match end.lte(&value_size) {
            false => Err(MemoryValueU64GetError::Outside(end)),
            true => match (offset.exact(), self.exact()) {
                (Some(o), Some(v)) if *len == size(&Type::U8) => {
                    let byte = v.to_ne_bytes()[o as usize];
                    Ok(MemoryValue::U8(MemoryValueU8 {
                        start: byte,
                        stop: byte,
                    }))
                }
                (Some(o), _) if *len == size(&Type::U64) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::U64(self.clone()))
                }
                x => todo!("{x:?}"),
            },
        }
    }
}

#[derive(Debug, Hash, Clone, Copy)]
pub struct MemoryValueI64 {
    pub start: i64,
    pub stop: i64,
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
impl From<MemoryValueU32> for MemoryValueI64 {
    fn from(MemoryValueU32 { start, stop }: MemoryValueU32) -> Self {
        Self {
            start: i64::from(start),
            stop: i64::from(stop),
        }
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

#[derive(Debug, Clone)]
pub struct MemoryValueU32 {
    pub start: u32,
    pub stop: u32,
}
impl From<MemoryValueU8> for MemoryValueU32 {
    fn from(MemoryValueU8 { start, stop }: MemoryValueU8) -> Self {
        MemoryValueU32 {
            start: u32::from(start),
            stop: u32::from(stop),
        }
    }
}
impl TryFrom<MemoryValueI64> for MemoryValueU32 {
    type Error = <u32 as TryFrom<i64>>::Error;
    fn try_from(MemoryValueI64 { start, stop }: MemoryValueI64) -> Result<Self, Self::Error> {
        Ok(Self {
            start: u32::try_from(start)?,
            stop: u32::try_from(stop)?,
        })
    }
}
impl From<u32> for MemoryValueU32 {
    fn from(x: u32) -> Self {
        Self { start: x, stop: x }
    }
}

#[derive(Debug, Error)]
pub enum MemoryValueSetError {
    #[error("Potentially access outside type with {0}")]
    Outside(MemoryValueI64),
    #[error("Attempting to set too large value.")]
    TooLarge,
    #[error("This would set multiple items from in the list, this is currently not supported.")]
    ListMultiple,
    #[error("The offset may be larger than the size of the type: {0}")]
    Offset(<MemoryValueU64 as TryFrom<MemoryValueI64>>::Error),
}
#[derive(Debug, Error)]
pub enum MemoryValueGetError {
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
    #[error("Failed to get i64: {0}")]
    I64(MemoryValueI64GetError),
}
// It is possible to technically store a 4 byte virtual value (e.g. DATA_END)
// then edit 2 bytes of it. So we will need additional complexity to support this case
#[derive(Debug, Clone)]
pub enum MemoryValue {
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
impl From<Immediate> for MemoryValue {
    fn from(imm: Immediate) -> Self {
        Self::I64(MemoryValueI64::from(imm.value))
    }
}
impl From<&MemoryValue> for Type {
    fn from(mv: &MemoryValue) -> Self {
        match mv {
            MemoryValue::U8(_) => Type::U8,
            MemoryValue::U64(_) => Type::U64,
            MemoryValue::Ptr(_) => Type::U64,
            MemoryValue::List(x) => Type::List(x.iter().map(Type::from).collect()),
            MemoryValue::I64(_) => Type::I64,
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
impl Add for MemoryValue {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        use MemoryValue::*;
        match (self, rhs) {
            (U8(a), U8(b)) => U8(a.add(&b).unwrap()),
            (Ptr(MemoryPtr(None)), _) => Ptr(MemoryPtr(None)),
            (Ptr(MemoryPtr(Some(mut a))), U8(b)) => {
                let c = MemoryValueU64::from(b);
                a.offset = a.offset.add(&c).unwrap();
                Ptr(MemoryPtr(Some(a)))
            }
            (Ptr(MemoryPtr(Some(mut a))), I8(b)) => {
                let c = MemoryValueI64::from(b);
                a.offset = MemoryValueU64::try_from(
                    MemoryValueI64::try_from(a.offset).unwrap().sub(&c).unwrap(),
                )
                .unwrap();
                Ptr(MemoryPtr(Some(a)))
            }
            (U32(a), U8(b)) => U32(a.add(&MemoryValueU32::from(b)).unwrap()),
            (U32(a), I64(b)) => U32(a.add(&MemoryValueU32::try_from(b).unwrap()).unwrap()),
            (Ptr(MemoryPtr(Some(mut a))), I64(b)) => {
                // dbg!(&b);
                let c = MemoryValueI64::try_from(a.offset).unwrap();
                a.offset = MemoryValueU64::try_from(c.add(&b).unwrap()).unwrap();
                MemoryValue::Ptr(MemoryPtr(Some(a)))
            }
            (I64(a), I64(b)) => I64(a.add(&b).unwrap()),
            x => todo!("{x:?}"),
        }
    }
}
impl MemoryValue {
    fn get(&self, subslice: &SubSlice) -> Result<MemoryValue, MemoryValueGetError> {
        use MemoryValue::*;
        match self {
            U8(x) => x.get(subslice).map_err(MemoryValueGetError::U8),
            U32(x) => x.get(subslice).map_err(MemoryValueGetError::U32),
            U64(x) => x.get(subslice).map_err(MemoryValueGetError::U64),
            I64(x) => x.get(subslice).map_err(MemoryValueGetError::I64),
            Ptr(x) => x.get(subslice).map_err(MemoryValueGetError::Ptr),
            List(list) => {
                let SubSlice { offset, len } = subslice;
                let memrange = memory_range(offset, len);
                let mut previous = 0;
                let mut covers = Vec::new();
                let mut iter = list.iter().enumerate();

                // Iterate items before.
                loop {
                    let Some((i, item)) = iter.next() else { break };
                    let next = previous + size(&Type::from(item));
                    let current = MemoryValueU64 {
                        start: previous,
                        stop: next,
                    };
                    match memrange.compare(&current) {
                        // Gets all bytes of this item.
                        RangeOrdering::Matches => return Ok(item.clone()),
                        // Gets some bytes within this item.
                        RangeOrdering::Within => {
                            return item.get(&SubSlice {
                                offset: (offset
                                    .clone()
                                    .sub(&MemoryValueU64::from(previous))
                                    .unwrap()),
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
                    let next = previous + size(&Type::from(item));
                    let current = MemoryValueU64 {
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
        offset: &MemoryValueU64,
        // Register position.
        // The `len` should always be exact since it matches to instruction e.g. `sw` has `len=4`.
        // I don't know if there is `offset` can be dynamic.
        len: &u64,
        // Register value.
        value: MemoryValue,
    ) -> Result<(), MemoryValueSetError> {
        let size_of_existing = size(&Type::from(self.clone()));
        let diff = MemoryValueU64::from(size_of_existing).sub(offset).unwrap();

        // we can't use recursion for lists since it may affect multiple items in a list.

        // Compare the size of the value we are attempting to store with the size of the type minus the offset.
        // Essentially asks "does storing `value` store it up to the last address in `self`?"
        match diff.compare_scalar(len) {
            // Setting bytes from the offset reaching the end of the type.
            RangeScalarOrdering::Within => {
                match self {
                    MemoryValue::U32(_) => match value {
                        MemoryValue::I64(from) => {
                            let new_value = from
                                .get(&SubSlice {
                                    offset: offset.clone(),
                                    len: 4,
                                })
                                .unwrap();
                            debug_assert_eq!(
                                size(&Type::from(new_value.clone())),
                                size_of_existing
                            );
                            *self = new_value;
                            Ok(())
                        }
                        MemoryValue::U32(_) => {
                            *self = value;
                            Ok(())
                        }
                        x => todo!("{x:?}"),
                    },
                    MemoryValue::U8(_) => unreachable!(),
                    // If we are setting bytes that reach the end, we know this will be the last element.
                    // We can also reach this case where we are setting an empty list to an empty list,
                    // both have equal sizes, but both are 0 and contain no elements.
                    MemoryValue::List(list) => {
                        let Some(item) = list.last_mut() else {
                            // In the case of empty list setting we don't need to do anything.
                            return Ok(());
                        };
                        let size_of_item = u64::from(size(&Type::from(item.clone())));
                        // Compare the size of the list item with the size of the value we are trying to set,
                        match size_of_item.cmp(&len) {
                            // if the size is equal it fully covers the last item in the list.
                            Ordering::Equal => {
                                *item = value;
                                return Ok(());
                            }
                            // if the size of the value is larger it will leak into earlier
                            // items in the list.
                            Ordering::Greater => todo!(),
                            // if the size of the value is smaller it will only cover the
                            // later bytes of the last item in the list.
                            Ordering::Less => todo!(),
                        }
                    }
                    x => todo!("{x:?}"),
                }
            }
            // Setting bytes from the offset not reaching the end of the type.
            RangeScalarOrdering::Less => match self {
                MemoryValue::List(list) => {
                    let memrange = memory_range(offset, &len);
                    let mut previous = 0;
                    let mut covers = Vec::new();
                    let mut iter = list.iter_mut().enumerate();

                    // Iterate items before.
                    loop {
                        let Some((i, item)) = iter.next() else { break };
                        let size_of_item = size(&Type::from(item.clone()));
                        let next = previous + size_of_item;
                        let current = MemoryValueU64 {
                            start: previous,
                            stop: next,
                        };
                        match memrange.compare(&current) {
                            // Sets all bytes of this item.
                            RangeOrdering::Matches => {
                                use MemoryValue::*;
                                debug_assert_eq!(*len,size_of_item);
                                let size_of_value = size(&Type::from(&value));

                                match (&value, item) {
                                    (_,to) if size_of_value == *len => {
                                        debug_assert_eq!(size_of_value, size_of_item);
                                        *to = value;
                                        return Ok(());
                                    }
                                    (I64(from),U8(to)) => {
                                        if let Some(from_bytes) = from.to_bytes() {
                                            let to_bytes = from_bytes[0..*len as usize].try_into().unwrap();
                                            *to = MemoryValueU8::from_bytes(&to_bytes);
                                        }
                                        else {
                                            todo!()
                                        }
                                    },
                                    _ => todo!()
                                }
                                
                            }
                            // This case is likely to be a pain since the sub-type might itself be a list, so we need some
                            // stack based recursion.
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
                        let next = previous + size(&Type::from(item.clone()));
                        let current = MemoryValueU64 {
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
                    println!("size_of_existing: {size_of_existing:?}");
                    println!("offset: {offset:?}");
                    println!("diff: {diff:?}");
                    println!("memrange: {memrange:?}");
                    println!("len: {len:?}");
                    Err(MemoryValueSetError::ListMultiple)
                }
                _ => todo!(),
            },
            // Setting bytes after the end of the type.
            RangeScalarOrdering::Greater => Err(MemoryValueSetError::TooLarge),
        }
    }

    pub fn compare(&self, other: &Self) -> Option<RangeOrdering> {
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
            (U32(a), I64(b)) => Some(MemoryValueI64::from(a.clone()).compare(b)),
            (U64(a), I64(b)) => {
                let Ok(c) = MemoryValueI64::try_from(a.clone()) else {
                    todo!()
                };
                Some(c.compare(b))
            }
            x => todo!("{x:?}"),
        }
    }
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

#[derive(Debug, Clone)]
pub struct MemoryPtr(pub Option<NonNullMemoryPtr>);
#[derive(Debug, Clone)]
pub struct NonNullMemoryPtr {
    pub tag: MemoryLabel,
    pub offset: MemoryValueU64,
}

#[derive(Debug, Error)]
pub enum MemoryValuePtrGetError {
    #[error("Potentially access outside type with {0:?}")]
    Outside(MemoryValueU64),
}

impl MemoryPtr {
    fn get(
        &self,
        SubSlice { offset, len }: &SubSlice,
    ) -> Result<MemoryValue, MemoryValuePtrGetError> {
        let end = offset.clone().add(&MemoryValueU64::from(*len)).unwrap();
        let value_size = size(&Type::U32);

        match end.compare_scalar(&value_size) {
            RangeScalarOrdering::Less => Err(MemoryValuePtrGetError::Outside(end)),
            // It will probably never be valid to grab a couple bytes from a pointer.
            // But in this case it should be supported by simply returning a range that is from min to max.
            RangeScalarOrdering::Greater => match *len {
                ..8 => {
                    // TODO This can be narrowed. If a ptr has an offset of 4, we know it is atleast >4.
                    // Return unknown bytes.
                    Ok(MemoryValue::from(Type::List(
                        (0..*len).map(|_| Type::U8).collect(),
                    )))
                }
                _ => unreachable!(),
            },
            RangeScalarOrdering::Within => match offset.exact() {
                Some(o) if *len == u64::from(size(&Type::U64)) => {
                    debug_assert_eq!(o, 0);
                    Ok(MemoryValue::Ptr(self.clone()))
                }
                x => todo!("{x:?}"),
            },
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MemoryLabel {
    Global { label: Label },
    Thread { label: Label, hart: u8 },
}

#[derive(Debug, Error)]
pub enum GetMemoryMapError {
    #[error("Failed to find the label in the memory map.")]
    Missing,
    #[error("Failed to get the value: {0}")]
    Value(MemoryValueGetError),
}
#[derive(Debug, Error)]
pub enum SetMemoryMapError {
    #[error("Attempted to set null ptr.")]
    NullPtr,
    #[error("Failed to find the label in the memory map.")]
    Missing,
    #[error("Failed to set the value: {0}")]
    Value(MemoryValueSetError),
}
#[derive(Debug)]
pub struct MemoryMap {
    pub map: HashMap<MemoryLabel, MemoryValue>,
}
impl MemoryMap {
    pub fn get(
        &self,
        Slice { base, offset, len }: &Slice,
    ) -> Result<MemoryValue, GetMemoryMapError> {
        self.map
            .get(base)
            .ok_or(GetMemoryMapError::Missing)?
            .get(&SubSlice {
                offset: offset.clone(),
                len: len.clone(),
            })
            .map_err(GetMemoryMapError::Value)
    }

    pub fn set(
        &mut self,
        // Memory location.
        key: &MemoryPtr,
        // Register length.
        len: &u64,
        // Register value.
        value: MemoryValue,
    ) -> Result<(), SetMemoryMapError> {
        let MemoryPtr(Some(NonNullMemoryPtr { tag, offset })) = key else {
            return Err(SetMemoryMapError::NullPtr);
        };
        let existing = self.map.get_mut(tag).ok_or(SetMemoryMapError::Missing)?;
        existing
            .set(offset, len, value)
            .map_err(SetMemoryMapError::Value)
    }

    // TODO This should be improved, I'm pretty sure the current approach is bad.
    // In setting a type type we need to set many sublabels for the sub-types.
    pub fn set_type(
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
                                offset: MemoryValueU64::ZERO,
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
                    .map(|_| memory_value_type_of())
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
                            offset: MemoryValueU64::ZERO,
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

/// Repreresents memory `mem[base+offset..base+offset+len]``
#[derive(Debug)]
pub struct Slice {
    pub base: MemoryLabel,
    pub offset: MemoryValueU64,
    pub len: u64,
}

#[derive(Debug)]
pub struct SubSlice {
    pub offset: MemoryValueU64,
    pub len: u64,
}

#[derive(Debug)]
pub struct State {
    // Each hart has its own registers.
    pub registers: Vec<RegisterValues>,
    pub memory: MemoryMap,
    pub configuration: ProgramConfiguration,
}
impl State {
    pub fn new(harts: u8, configuration: &ProgramConfiguration) -> Self {
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

#[derive(Debug)]
pub struct RegisterValues(HashMap<Register, MemoryValue>);
impl RegisterValues {
    pub fn insert(&mut self, key: Register, value: MemoryValue) -> Result<Option<MemoryValue>, ()> {
        // Attempting to store a list that is larger than 64 bits into a 64 bit register will fail.
        if let MemoryValue::List(_) = value {
            todo!()
        }
        Ok(self.0.insert(key, value))
    }
    pub fn get(&self, key: &Register) -> Option<&MemoryValue> {
        self.0.get(key)
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CsrValue {
    Mhartid,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LabelLocality {
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

/// Each execution path is based on the initial types assumed for each variables encountered and the locality assumed for each variable encountered.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramConfiguration(pub BTreeMap<Label, (LabelLocality, Type)>);
impl ProgramConfiguration {
    pub fn append(&mut self, other: ProgramConfiguration) {
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
    pub fn insert(&mut self, key: Label, hart: u8, (locality, ttype): (Locality, Type)) {
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
    pub fn get(&self, key: &Label) -> Option<(&Locality, &Type)> {
        self.0.get(key).map(|(l, t)| (l.into(), t))
    }
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }
}

pub fn memory_range(offset: &MemoryValueU64, len: &u64) -> MemoryValueU64 {
    MemoryValueU64 {
        start: offset.start,
        stop: offset.stop + *len,
    }
}

/// Compile time size
pub fn size(t: &Type) -> u64 {
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

pub fn memory_value_type_of() -> Type {
    Type::List(vec![Type::U64, Type::U64, Type::U64, Type::U8])
}
