use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{BitAnd, BitOr, BitXor, Sub},
    panic::{RefUnwindSafe, UnwindSafe},
};

use crate::{integer::Integer, BackingType};

#[derive(Debug, Clone)]
pub struct BitSet<const MIN: usize, const MAX: usize, T = usize> {
    data: Vec<BackingType>,
    len: usize,
    phantom: PhantomData<T>,
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> Default for BitSet<LOWER, UPPER, T> {
    fn default() -> Self {
        Self {
            data: vec![0; (UPPER - LOWER).div_ceil(T::BIT_WIDTH) + 1],
            len: 0,
            phantom: PhantomData::<T>,
        }
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> BitSet<LOWER, UPPER, T> {
    /// Construct a new [BitSet<LOWER, UPPER, T>], where [LOWER] and [UPPER] are
    /// [usize] integers that denote the boundaries of the [BitSet], and [T] is
    /// a type implementing the [Integer] trait
    ///
    /// ```
    /// use firms::BitSet;
    /// let foo = BitSet::<10, 20>::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of elements in the set.
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(1);
    /// foo.insert(10);
    /// foo.insert(5);
    ///
    /// assert_eq!(foo.len(), 3);
    ///
    /// foo.remove(1);
    /// assert_eq!(foo.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        debug_assert_eq!(
            self.data.iter().map(|x| x.count_ones()).sum::<u32>(),
            self.len as u32
        );
        self.len
    }

    /// Checks whether the set is empty.
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(1);
    /// assert_eq!(foo.len(), 1);
    /// assert!(!foo.is_empty());
    ///
    /// foo.remove(1);
    /// assert!(foo.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all items from set.
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(1);
    /// foo.insert(10);
    /// foo.insert(5);
    ///
    /// assert_eq!(foo.len(), 3);
    /// assert!(!foo.is_empty());
    ///
    /// foo.clear();
    /// assert_eq!(foo.len(), 0);
    /// assert!(foo.is_empty());
    /// ```
    pub fn clear(&mut self) {
        // TODO: can I make sure this is vectorized?
        for x in self.data.iter_mut() {
            *x = 0_u64;
        }
        debug_assert_eq!(self.data.iter().map(|x| x.count_ones()).sum::<u32>(), 0);
        self.len = 0;
    }

    const LOWER_DIV_BIT_WIDTH: usize = LOWER / T::BIT_WIDTH;
    const LOWER_REM_BIT_WIDTH: usize = LOWER % T::BIT_WIDTH;

    /// Returns the array index and bit position for an element x.
    fn position(x: T) -> (usize, usize) {
        let x: usize = x.into();
        (
            x / T::BIT_WIDTH - Self::LOWER_DIV_BIT_WIDTH,
            x % T::BIT_WIDTH - Self::LOWER_REM_BIT_WIDTH,
        )
    }

    /// Return whether an item is part of the set.
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<3, 32>::new();
    /// foo.insert(3);
    /// foo.insert(10);
    /// foo.insert(5);
    ///
    /// assert_eq!(foo.len(), 3);
    /// assert!(foo.contains(3));
    /// assert!(foo.contains(10));
    /// assert!(foo.contains(5));
    /// ```
    pub fn contains(&self, x: T) -> bool {
        let (idx, bit) = Self::position(x);
        self.is_bit_set(idx, bit)
    }

    fn is_bit_set(&self, idx: usize, bit: usize) -> bool {
        self.data[idx] & (1 << bit) != 0
    }

    /// Insert an item into the set.
    ///
    /// This item `x` has to be constrained to `LOWER <= x <= UPPER`
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(0);
    /// foo.insert(10);
    /// foo.insert(32);
    /// assert!(foo.contains(0));
    /// assert!(foo.contains(10));
    /// assert!(foo.contains(32));
    /// assert!(!foo.contains(2));
    ///
    /// foo.remove(0);
    /// foo.remove(10);
    /// foo.remove(32);
    /// assert!(!foo.contains(0));
    /// assert!(!foo.contains(10));
    /// assert!(!foo.contains(32));
    /// ```
    pub fn insert(&mut self, x: T) {
        assert!(x >= LOWER);
        assert!(x <= UPPER);
        let (idx, bit) = Self::position(x);
        self.data[idx] |= 1 << bit;
        self.len += 1;
    }

    /// Removes an item from the set.
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(1);
    /// assert!(foo.contains(1));
    ///
    /// foo.remove(1);
    /// assert!(!foo.contains(1));
    /// ```
    pub fn remove(&mut self, x: T) {
        let (idx, bit) = Self::position(x);
        self.len = self.len.saturating_sub(self.is_bit_set(idx, bit).into());
        self.data[idx] ^= 1 << bit;
    }

    /// Using the predicate `f` passed to this method, filter the set such that
    /// it only retains elements fulfilling the predicate.
    ///
    /// ```
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(1);
    /// foo.insert(2);
    /// foo.insert(3);
    ///
    /// foo.retain(|x| x % 2 == 0);
    ///
    /// assert!(foo.contains(2));
    /// assert!(!foo.contains(1));
    /// assert!(!foo.contains(3));
    /// ```
    pub fn retain(&mut self, f: impl Fn(usize) -> bool) {
        for x in LOWER..=UPPER {
            if !f(x) {
                self.remove(x.into());
            }
        }
    }

    pub fn iter(&self) -> Iter<'_, LOWER, UPPER, T> {
        Iter {
            set: self,
            index: 0,
        }
    }

    /// Visits the values representing the difference, i.e., the values that are in self but not in other.
    pub fn difference(&self, _other: &Self) -> Difference {
        todo!()
    }

    /// Visits the values representing the symmetric difference, i.e., the values that are in self or in other but not in both.
    pub fn symmetric_difference(&self, _other: &Self) -> SymmetricDifference {
        todo!()
    }

    /// Visits the values representing the intersection, i.e., the values that are both in self and other.
    ///
    /// When an equal element is present in self and other then the resulting Intersection may yield references to one or the other. This can be relevant if T contains fields which are not compared by its Eq implementation, and may hold different value between the two equal copies of T in the two sets.
    pub fn intersection(&self, _other: &Self) -> Intersection {
        todo!()
    }

    /// Visits the values representing the union, i.e., all the values in self or other, without duplicates.
    pub fn union(&self, _other: &Self) -> Union {
        todo!()
    }

    /// Returns true of `self` and `other` do not share any elements.
    ///
    /// ```should_panic
    /// use firms::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32>::new();
    /// foo.insert(1);
    /// foo.insert(2);
    /// foo.insert(3);
    ///
    /// let mut bar = BitSet::<0, 32>::new();
    /// bar.insert(4);
    /// bar.insert(5);
    /// bar.insert(6);
    ///
    /// assert!(foo.is_disjoint(&bar));
    ///
    /// foo.insert(4);
    /// assert!(!foo.is_disjoint(&bar));
    /// ```
    pub fn is_disjoint(&self, other: &Self) -> bool {
        for x in self.into_iter() {
            if other.contains(x) {
                return false;
            }
        }
        true
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        for x in self.into_iter() {
            if !other.contains(x) {
                return false;
            }
        }
        true
    }

    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
}

impl<const LOWER: usize, const UPPER: usize, T> BitAnd for BitSet<LOWER, UPPER, T> {
    type Output = Self;
    fn bitand(self, _rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<const LOWER: usize, const UPPER: usize, T> BitOr for BitSet<LOWER, UPPER, T> {
    type Output = Self;
    fn bitor(self, _rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<const LOWER: usize, const UPPER: usize, T> BitXor for BitSet<LOWER, UPPER, T> {
    type Output = Self;
    fn bitxor(self, _rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<const LOWER: usize, const UPPER: usize, T> Extend<T> for BitSet<LOWER, UPPER, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, _iter: I) {
        todo!()
    }
}

impl<const LOWER: usize, const UPPER: usize, const M: usize, T: Integer> From<[T; M]>
    for BitSet<LOWER, UPPER, T>
{
    fn from(value: [T; M]) -> Self {
        Self::from_iter(value)
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> FromIterator<T>
    for BitSet<LOWER, UPPER, T>
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut s = Self::new();
        for x in iter {
            s.insert(x);
        }
        s
    }
}

impl<const LOWER: usize, const UPPER: usize, T> IntoIterator for BitSet<LOWER, UPPER, T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

impl<const LOWER: usize, const UPPER: usize, T> IntoIterator for &BitSet<LOWER, UPPER, T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

impl<const LOWER: usize, const UPPER: usize, T: PartialEq> PartialEq for BitSet<LOWER, UPPER, T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        for (x, y) in self.into_iter().zip(other) {
            if x != y {
                return false;
            }
        }
        true
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Eq> Eq for &BitSet<LOWER, UPPER, T> {}

impl<const LOWER: usize, const UPPER: usize, T> Sub for &BitSet<LOWER, UPPER, T> {
    type Output = Self;
    fn sub(self, _rhs: Self) -> Self::Output {
        // basically just the difference but as a new Set
        todo!()
    }
}

unsafe impl<const LOWER: usize, const UPPER: usize, T> Send for BitSet<LOWER, UPPER, T> {}
unsafe impl<const LOWER: usize, const UPPER: usize, T> Sync for BitSet<LOWER, UPPER, T> {}
impl<const LOWER: usize, const UPPER: usize, T> RefUnwindSafe for BitSet<LOWER, UPPER, T> {}
impl<const LOWER: usize, const UPPER: usize, T> UnwindSafe for BitSet<LOWER, UPPER, T> {}

pub struct Difference {}
pub struct SymmetricDifference {}
pub struct Intersection {}
pub struct Union {}
pub struct IntoIter<T> {
    phantom: PhantomData<T>,
}
pub struct Iter<'a, const LOWER: usize, const UPPER: usize, T> {
    set: &'a BitSet<LOWER, UPPER, T>,
    index: usize,
}

impl<'a, const LOWER: usize, const UPPER: usize, T> Iterator for Iter<'a, LOWER, UPPER, T> {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.set.len {
            self.index += 1;
            Some(self.index + LOWER)
        } else {
            None
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
