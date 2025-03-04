use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{BitAnd, BitOr, BitXor, Sub},
    panic::{RefUnwindSafe, UnwindSafe},
};

use num_traits::NumCast;

use crate::{integer::Integer, BackingType, BIT_WIDTH};

#[derive(Clone)]
pub struct BitSet<const MIN: usize, const MAX: usize, T> {
    data: Vec<BackingType>,
    len: usize,
    phantom: PhantomData<T>,
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> Debug for BitSet<LOWER, UPPER, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> Default for BitSet<LOWER, UPPER, T> {
    fn default() -> Self {
        Self {
            data: vec![0; (UPPER - LOWER).div_ceil(BIT_WIDTH) + 1],
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
    /// use firims::BitSet;
    /// let foo = BitSet::<10, 20, usize>::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of elements in the set.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1, 10, 5]);
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
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1]);
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
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1, 10, 5]);
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

    /// Returns the array index and bit position for an element x.
    fn position(x: T) -> (usize, usize) {
        let y: usize = <usize as NumCast>::from(x).unwrap() - LOWER;
        (y / BIT_WIDTH, y % BIT_WIDTH)
    }

    /// Return whether an item is part of the set.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<3, 32, usize>::from([3, 10, 5]);
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
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::new();
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
        debug_assert!(x >= NumCast::from(LOWER).unwrap());
        debug_assert!(x <= NumCast::from(UPPER).unwrap());

        let (idx, bit) = Self::position(x);
        self.len += Into::<usize>::into(!self.is_bit_set(idx, bit));
        self.data[idx] |= 1 << bit;
    }

    /// Removes an item from the set.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1]);
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
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1, 2, 3]);
    ///
    /// foo.retain(|x| x % 2 == 0);
    ///
    /// assert!(foo.contains(2));
    /// assert!(!foo.contains(1));
    /// assert!(!foo.contains(3));
    /// ```
    pub fn retain(&mut self, f: impl Fn(T) -> bool) {
        for x in LOWER..=UPPER {
            let x = NumCast::from(x).unwrap();
            if !f(x) {
                self.remove(x);
            }
        }
    }

    /// Removes and returns the value in the set, if any, that is equal to the
    /// given one.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1, 2, 3]);
    ///
    /// assert_eq!(foo.len(), 3);
    /// assert!(foo.contains(2));
    /// assert_eq!(foo.take(2), Some(2));
    /// assert_eq!(foo.len(), 2);
    /// assert_eq!(foo.take(2), None);
    /// ```
    pub fn take(&mut self, v: T) -> Option<T> {
        if self.contains(v) {
            self.remove(v);
            Some(v)
        } else {
            None
        }
    }

    /// An iterator visiting all values of the set in ascending order.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<2, 5, usize>::from([2, 4, 5]);
    ///
    /// let mut iter = foo.iter();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, LOWER, UPPER, T> {
        Iter::new(self)
    }

    /// A consuming iterator visiting all values of the set in ascending order.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<2, 5, usize>::from([2, 4, 5]);
    ///
    /// let mut iter = foo.into_iter();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), None);
    /// ```
    //pub fn into_iter(self) -> IntoIter<LOWER, UPPER, T> {}

    /// A draining iterator visiting all values of the set in ascending order,
    /// each iteration removing that value from the set.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<2, 5, usize>::from([2, 4, 5]);
    ///
    /// assert!(!foo.is_empty());
    /// {
    ///     let mut iter = foo.drain();
    ///     assert_eq!(iter.next(), Some(2));
    ///     assert_eq!(iter.next(), Some(4));
    ///     assert_eq!(iter.next(), Some(5));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// assert!(foo.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_, LOWER, UPPER, T> {
        Drain::new(self)
    }

    /// Visits the values representing the difference, i.e., the values that are
    /// in self but not in other.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let foo = BitSet::<1, 10, usize>::from([1, 2, 3]);
    /// let bar = BitSet::<1, 10, usize>::from([4, 2, 3, 4]);
    ///
    /// let diff: BitSet::<1, 10, usize> = foo.difference(&bar).collect();
    /// assert_eq!(diff, [1].iter().collect());
    /// assert_eq!(diff.len(), 1);
    ///
    /// let diff: BitSet::<1, 10, usize> = bar.difference(&foo).collect();
    /// assert_eq!(diff, [4].iter().collect());
    /// assert_eq!(diff.len(), 1);
    /// ```
    pub fn difference<'a>(&'a self, rhs: &'a Self) -> Difference<'a, LOWER, UPPER, T> {
        Difference::new(self, rhs)
    }

    /// Visits the values representing the symmetric difference, i.e., the
    /// values that are in self or in other but not in both.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let foo = BitSet::<1, 10, usize>::from([1, 2, 3]);
    /// let bar = BitSet::<1, 10, usize>::from([4, 2, 3, 4]);
    ///
    /// let diff1: BitSet::<1, 10, usize> = foo.symmetric_difference(&bar).collect();
    /// let diff2: BitSet::<1, 10, usize> = bar.symmetric_difference(&foo).collect();
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, [1, 4].iter().collect());
    /// ```
    pub fn symmetric_difference<'a>(
        &'a self,
        rhs: &'a Self,
    ) -> SymmetricDifference<'a, LOWER, UPPER, T> {
        SymmetricDifference::new(self, rhs)
    }

    /// Visits the values representing the intersection, i.e., the values that
    /// are both in self and other.
    ///
    /// When an equal element is present in self and other then the resulting
    /// [Intersection] may yield copies of one or the other. This can be
    /// relevant if [T] contains fields which are not compared by its [Eq]
    /// implementation, and may hold different value between the two equal
    /// copies of [T] in the two sets.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let foo = BitSet::<1, 10, usize>::from([1, 2, 3]);
    /// let bar = BitSet::<1, 10, usize>::from([4, 2, 3, 4]);
    ///
    /// let intersect: BitSet::<1, 10, usize> = foo.intersection(&bar).collect();
    /// assert_eq!(intersect, [2, 3].iter().collect());
    /// ```
    pub fn intersection<'a>(&'a self, rhs: &'a Self) -> Intersection<'a, LOWER, UPPER, T> {
        Intersection::new(self, rhs)
    }

    /// Visits the values representing the union, i.e., all the values in self or other, without duplicates.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let foo = BitSet::<1, 10, usize>::from([1, 2, 3]);
    /// let bar = BitSet::<1, 10, usize>::from([4, 2, 3, 4]);
    ///
    /// let un: BitSet::<1, 10, usize> = foo.union(&bar).collect();
    /// assert_eq!(un, [1, 2, 3, 4].iter().collect());
    /// ```
    pub fn union<'a>(&'a self, rhs: &'a Self) -> Union<'a, LOWER, UPPER, T> {
        Union::new(self, rhs)
    }

    /// Returns true of `self` and `other` do not share any elements.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<0, 32, usize>::from([1, 2, 3]);
    /// let mut bar = BitSet::<0, 32, usize>::from([4, 5, 6]);
    ///
    /// assert!(foo.is_disjoint(&bar));
    ///
    /// foo.insert(4);
    /// assert!(!foo.is_disjoint(&bar));
    /// ```
    pub fn is_disjoint(&self, other: &Self) -> bool {
        Intersection::new(self, other).count() == 0
    }

    /// Returns true if the set is a subset of another, i.e., other contains at
    /// least all the values in self.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let foo = BitSet::<0, 5, usize>::from([1, 2, 3]);
    /// let mut bar = BitSet::<0, 5, usize>::new();
    ///
    /// assert_eq!(bar.is_subset(&foo), true);
    /// bar.insert(2);
    /// assert_eq!(bar.is_subset(&foo), true);
    /// bar.insert(4);
    /// assert_eq!(bar.is_subset(&foo), false);
    /// ```
    pub fn is_subset(&self, other: &Self) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(v))
        } else {
            false
        }
    }

    /// Returns true if the set is a superset of another, i.e., self contains at
    /// least all the values in other.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let foo = BitSet::<0, 5, usize>::from([1, 2]);
    /// let mut bar = BitSet::<0, 5, usize>::new();
    ///
    /// assert_eq!(bar.is_superset(&foo), false);
    ///
    /// bar.insert(0);
    /// bar.insert(1);
    /// assert_eq!(bar.is_superset(&foo), false);
    ///
    /// bar.insert(2);
    /// assert_eq!(bar.is_superset(&foo), true);
    /// ```
    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> BitAnd<&BitSet<LOWER, UPPER, T>>
    for &BitSet<LOWER, UPPER, T>
{
    type Output = BitSet<LOWER, UPPER, T>;

    /// Returns the intersection of self and rhs as a new
    /// [BitSet<LOWER, UPPER, T>].
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let a = BitSet::<1, 6, usize>::from([1, 2, 3]);
    /// let b = BitSet::<1, 6, usize>::from([2, 3, 4]);
    ///
    /// let set = &a & &b;
    ///
    /// let mut i = 0;
    /// let expected = [2, 3];
    /// for x in &set {
    ///     assert!(expected.contains(&x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitand(self, rhs: &BitSet<LOWER, UPPER, T>) -> Self::Output {
        self.intersection(rhs).collect()
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> BitOr<&BitSet<LOWER, UPPER, T>>
    for &BitSet<LOWER, UPPER, T>
{
    type Output = BitSet<LOWER, UPPER, T>;

    /// Returns the union of self and rhs as a new
    /// [BitSet<LOWER, UPPER, T>].
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let a = BitSet::<1, 6, usize>::from([1, 2, 3]);
    /// let b = BitSet::<1, 6, usize>::from([3, 4, 5]);
    ///
    /// let set = &a | &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 3, 4, 5];
    /// for x in &set {
    ///     assert!(expected.contains(&x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitor(self, rhs: &BitSet<LOWER, UPPER, T>) -> Self::Output {
        self.union(rhs).collect()
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> BitXor<&BitSet<LOWER, UPPER, T>>
    for &BitSet<LOWER, UPPER, T>
{
    type Output = BitSet<LOWER, UPPER, T>;

    /// Returns the symmetric difference of self and rhs as a new
    /// [BitSet<LOWER, UPPER, T>].
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let a = BitSet::<1, 6, usize>::from([1, 2, 3]);
    /// let b = BitSet::<1, 6, usize>::from([3, 4, 5]);
    ///
    /// let set = &a ^ &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 4, 5];
    /// for x in &set {
    ///     assert!(expected.contains(&x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitxor(self, rhs: &BitSet<LOWER, UPPER, T>) -> Self::Output {
        self.symmetric_difference(rhs).collect()
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> Extend<T> for BitSet<LOWER, UPPER, T> {
    /// Extends a [BitSet<LOWER, UPPER, T>] with the contents of an iterator.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut a = BitSet::<1, 6, usize>::from([1, 2, 3]);
    /// a.extend([3, 4, 5]);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(a, [1, 2, 3, 4, 5].iter().collect());
    /// ```
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for x in iter {
            self.insert(x);
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Extend<&'a T>
    for BitSet<LOWER, UPPER, T>
{
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for x in iter {
            self.insert(*x);
        }
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
        s.extend(iter);
        s
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> FromIterator<&'a T>
    for BitSet<LOWER, UPPER, T>
{
    fn from_iter<I: IntoIterator<Item = &'a T>>(iter: I) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> IntoIterator for BitSet<LOWER, UPPER, T> {
    type Item = T;
    type IntoIter = IntoIter<LOWER, UPPER, T>;

    /// A consuming iterator visiting all values of the set in ascending order.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<2, 5, usize>::from([2, 4, 5]);
    ///
    /// let mut iter = foo.into_iter();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> IntoIterator
    for &'a BitSet<LOWER, UPPER, T>
{
    type Item = T;
    type IntoIter = Iter<'a, LOWER, UPPER, T>;
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer + PartialEq> PartialEq
    for BitSet<LOWER, UPPER, T>
{
    /// Compares two [BitSet]s.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let a = BitSet::<1, 6, usize>::from([1, 2, 3]);
    /// let b = BitSet::<1, 6, usize>::from([2, 3]);
    /// let c = BitSet::<1, 6, usize>::from([1, 2, 3]);
    ///
    /// assert!(a != b);
    /// assert!(a == c);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().zip(other).all(|(x, y)| x == y)
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer + Eq> Eq for &BitSet<LOWER, UPPER, T> {}

impl<const LOWER: usize, const UPPER: usize, T: Integer> Sub for &BitSet<LOWER, UPPER, T> {
    type Output = BitSet<LOWER, UPPER, T>;

    /// Returns the difference of self and rhs as a new [BitSet<LOWER, UPPER, T>].
    ///
    /// Current limitation: the generic parameters of the lhs and rhs need to
    /// the exact same.
    ///
    /// ```
    /// use firims::BitSet;
    ///
    /// let mut foo = BitSet::<2, 5, usize>::new();
    /// foo.insert(2);
    /// foo.insert(4);
    /// foo.insert(5);
    ///
    /// let mut bar = BitSet::<2, 5, usize>::new();
    /// bar.insert(3);
    /// bar.insert(4);
    ///
    /// let baz = &foo - &bar;
    /// assert_eq!(foo.len(), 3);
    /// assert_eq!(bar.len(), 2);
    /// assert_eq!(baz.len(), 2);
    ///
    /// assert_eq!(baz.contains(2), true);
    /// assert_eq!(baz.contains(3), false);
    /// assert_eq!(baz.contains(4), false);
    /// assert_eq!(baz.contains(5), true);
    /// ```
    fn sub(self, rhs: &BitSet<LOWER, UPPER, T>) -> Self::Output {
        self.difference(rhs).collect()
    }
}

unsafe impl<const LOWER: usize, const UPPER: usize, T> Send for BitSet<LOWER, UPPER, T> {}
unsafe impl<const LOWER: usize, const UPPER: usize, T> Sync for BitSet<LOWER, UPPER, T> {}
impl<const LOWER: usize, const UPPER: usize, T> RefUnwindSafe for BitSet<LOWER, UPPER, T> {}
impl<const LOWER: usize, const UPPER: usize, T> UnwindSafe for BitSet<LOWER, UPPER, T> {}

/// Iterator that visits the values representing the difference, i.e. the
/// values that are in self but not in other.
#[derive(Debug, Clone, Copy)]
pub struct Difference<'a, const LOWER: usize, const UPPER: usize, T: Integer> {
    index: usize,
    lhs: &'a BitSet<LOWER, UPPER, T>,
    rhs: &'a BitSet<LOWER, UPPER, T>,
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Difference<'a, LOWER, UPPER, T> {
    fn new(lhs: &'a BitSet<LOWER, UPPER, T>, rhs: &'a BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            lhs,
            rhs,
        }
    }
}

fn generic_next_binop<
    const LOWER: usize,
    const UPPER: usize,
    T: Integer,
    F: Fn(bool, bool) -> bool,
>(
    index: &mut usize,
    lhs: &BitSet<LOWER, UPPER, T>,
    rhs: &BitSet<LOWER, UPPER, T>,
    op: F,
) -> Option<T> {
    while *index <= UPPER {
        let v = NumCast::from(*index).unwrap();
        *index += 1;
        if op(lhs.contains(v), rhs.contains(v)) {
            return Some(v);
        }
    }
    None
}

fn generic_size_hint_binop<const LOWER: usize, const UPPER: usize, T: Integer>(
    lhs: &BitSet<LOWER, UPPER, T>,
    rhs: &BitSet<LOWER, UPPER, T>,
) -> (usize, Option<usize>) {
    (lhs.len.min(rhs.len), Some(UPPER - LOWER))
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iterator
    for Difference<'a, LOWER, UPPER, T>
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        generic_next_binop(&mut self.index, self.lhs, self.rhs, |x, y| x && !y)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        generic_size_hint_binop(self.lhs, self.rhs)
    }
}

/// Iterator that visits the values representing the symmetric difference, i.e.
/// the values that are in either self or other, but not both.
#[derive(Debug, Clone, Copy)]
pub struct SymmetricDifference<'a, const LOWER: usize, const UPPER: usize, T: Integer> {
    index: usize,
    lhs: &'a BitSet<LOWER, UPPER, T>,
    rhs: &'a BitSet<LOWER, UPPER, T>,
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer>
    SymmetricDifference<'a, LOWER, UPPER, T>
{
    fn new(lhs: &'a BitSet<LOWER, UPPER, T>, rhs: &'a BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            lhs,
            rhs,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iterator
    for SymmetricDifference<'a, LOWER, UPPER, T>
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        generic_next_binop(&mut self.index, self.lhs, self.rhs, |x, y| x ^ y)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        generic_size_hint_binop(self.lhs, self.rhs)
    }
}

/// Iterator that visits the values representing the intersection, i.e.
/// the values that are in both self and other.
#[derive(Debug, Clone, Copy)]
pub struct Intersection<'a, const LOWER: usize, const UPPER: usize, T: Integer> {
    index: usize,
    lhs: &'a BitSet<LOWER, UPPER, T>,
    rhs: &'a BitSet<LOWER, UPPER, T>,
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Intersection<'a, LOWER, UPPER, T> {
    fn new(lhs: &'a BitSet<LOWER, UPPER, T>, rhs: &'a BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            lhs,
            rhs,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iterator
    for Intersection<'a, LOWER, UPPER, T>
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        generic_next_binop(&mut self.index, self.lhs, self.rhs, |x, y| x && y)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        generic_size_hint_binop(self.lhs, self.rhs)
    }
}

/// Iterator that visits the values representing the union, i.e. the values that
/// are in either self or other.
#[derive(Debug, Clone, Copy)]
pub struct Union<'a, const LOWER: usize, const UPPER: usize, T: Integer> {
    index: usize,
    lhs: &'a BitSet<LOWER, UPPER, T>,
    rhs: &'a BitSet<LOWER, UPPER, T>,
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Union<'a, LOWER, UPPER, T> {
    fn new(lhs: &'a BitSet<LOWER, UPPER, T>, rhs: &'a BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            lhs,
            rhs,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iterator
    for Union<'a, LOWER, UPPER, T>
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        generic_next_binop(&mut self.index, self.lhs, self.rhs, |x, y| x || y)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        generic_size_hint_binop(self.lhs, self.rhs)
    }
}

/// Iterator that visits the all values in the set.
#[derive(Debug, Clone, Copy)]
pub struct Iter<'a, const LOWER: usize, const UPPER: usize, T: Integer> {
    index: usize,
    collection: &'a BitSet<LOWER, UPPER, T>,
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iter<'a, LOWER, UPPER, T> {
    fn new(collection: &'a BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            collection,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iterator
    for Iter<'a, LOWER, UPPER, T>
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        while self.index <= UPPER {
            let v = NumCast::from(self.index).unwrap();
            self.index += 1;
            if self.collection.contains(v) {
                return Some(v);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}

/// Draining iterator that visits the all values in the set, and leaves the
/// iterated over spots in the set empty.
pub struct Drain<'a, const LOWER: usize, const UPPER: usize, T> {
    index: usize,
    collection: &'a mut BitSet<LOWER, UPPER, T>,
}

impl<'a, const LOWER: usize, const UPPER: usize, T> Drain<'a, LOWER, UPPER, T> {
    fn new(collection: &'a mut BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            collection,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, T: Integer> Iterator
    for Drain<'a, LOWER, UPPER, T>
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        while self.index <= UPPER {
            let v = NumCast::from(self.index).unwrap();
            self.index += 1;
            if self.collection.contains(v) {
                self.collection.remove(v);
                return Some(v);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}

/// Consuming iterator that visits all values in the set.
pub struct IntoIter<const LOWER: usize, const UPPER: usize, T: Integer> {
    index: usize,
    collection: BitSet<LOWER, UPPER, T>,
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> IntoIter<LOWER, UPPER, T> {
    fn new(collection: BitSet<LOWER, UPPER, T>) -> Self {
        Self {
            index: LOWER,
            collection,
        }
    }
}

impl<const LOWER: usize, const UPPER: usize, T: Integer> Iterator for IntoIter<LOWER, UPPER, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        while self.index <= UPPER {
            let v = NumCast::from(self.index).unwrap();
            self.index += 1;
            if self.collection.contains(v) {
                self.collection.remove(v);
                return Some(v);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}
