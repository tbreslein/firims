use std::fmt::Debug;

use num_traits::{PrimInt, Unsigned};

pub trait Integer: Debug + PrimInt + Unsigned {}

impl Integer for usize {}
impl Integer for u8 {}
impl Integer for u16 {}
impl Integer for u32 {}
