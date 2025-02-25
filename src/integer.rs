use std::fmt::Debug;

pub trait Integer:
    Debug + Clone + Copy + Send + Sync + PartialEq + Eq + Into<usize> + From<usize> + PartialOrd<usize>
{
    const BIT_WIDTH: usize;
}

impl Integer for usize {
    const BIT_WIDTH: usize = Self::BITS as usize;
}
