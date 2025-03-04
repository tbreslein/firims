use std::fmt::Debug;

use num_traits::PrimInt;

pub trait Integer:
    //Debug + Clone + Copy + Send + Sync + PartialEq + Eq + Into<usize> + From<usize> + PartialOrd<usize>
    Debug + PrimInt
{
}

impl Integer for usize {}
impl Integer for u8 {}
impl Integer for u16 {}
impl Integer for u32 {}
impl Integer for u64 {}
