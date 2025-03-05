use std::fmt::Debug;

use num_traits::{PrimInt, Unsigned};

/// Generic trait for integers to be used as set members in [crate::BitSet] and
/// as keys in [crate::Map].
///
/// Based on [num_traits].
pub trait Integer: Debug + PrimInt + Unsigned {}

impl Integer for usize {}
impl Integer for u8 {}
impl Integer for u16 {}
impl Integer for u32 {}
