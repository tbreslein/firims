use std::{iter::FusedIterator, marker::PhantomData};

use num_traits::NumCast;

use crate::Integer;

#[derive(Debug, Clone)]
pub struct Map<const LOWER: usize, const UPPER: usize, K: Integer, V> {
    data: Vec<Option<V>>,
    len: usize,
    phantom: PhantomData<K>,
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V: Clone> Default
    for Map<LOWER, UPPER, K, V>
{
    fn default() -> Self {
        Self {
            data: vec![None; (UPPER - LOWER) + 1],
            len: 0,
            phantom: PhantomData::<K>,
        }
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V: Clone> Map<LOWER, UPPER, K, V> {
    /// Construct a new [Map<LOWER, UPPER, T>], where [LOWER] and [UPPER] are
    /// [usize] integers that denote the boundaries of the [Map] keys, [K] is
    /// the type for the keys implementing the [Integer] trait, and [V] is the
    /// type for the values.
    ///
    /// ```
    /// use firims::Map;
    /// let foo = Map::<10, 20, usize, f32>::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of elements in the map.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(1, 11.1);
    /// foo.insert(10, 22.2);
    /// foo.insert(5, 33.3);
    ///
    /// assert_eq!(foo.len(), 3);
    ///
    /// foo.remove(1);
    /// assert_eq!(foo.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        debug_assert_eq!(self.data.iter().filter(|x| x.is_some()).count(), self.len);
        self.len
    }

    /// Checks whether the map is empty.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(1, 11.1);
    /// assert_eq!(foo.len(), 1);
    /// assert!(!foo.is_empty());
    ///
    /// foo.remove(1);
    /// assert!(foo.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all items from map.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(1, 11.1);
    /// foo.insert(10, 22.2);
    /// foo.insert(5, 33.3);
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
            *x = None;
        }
        debug_assert_eq!(self.data.iter().filter(|x| x.is_some()).count(), 0);
        self.len = 0;
    }

    /// Returns the array index for an element x.
    fn position(x: K) -> usize {
        <usize as NumCast>::from(x).unwrap() - LOWER
    }

    /// Return whether a key is present in the map.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<3, 32, usize, f32>::new();
    /// foo.insert(3, 11.1);
    /// foo.insert(10, 22.2);
    /// foo.insert(5, 33.3);
    ///
    /// assert_eq!(foo.len(), 3);
    /// assert!(foo.contains_key(3));
    /// assert!(foo.contains_key(10));
    /// assert!(foo.contains_key(5));
    /// ```
    pub fn contains_key(&self, x: K) -> bool {
        x >= NumCast::from(LOWER).unwrap()
            && x <= NumCast::from(UPPER).unwrap()
            && self.data[Self::position(x)].is_some()
    }

    /// Insert a key value pair into the map.
    ///
    /// If the map did not have this key present, None is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned.
    ///
    /// This item `x` has to be constrained to `LOWER <= x <= UPPER`
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(10, 22.2);
    /// foo.insert(32, 33.3);
    /// assert!(foo.contains_key(0));
    /// assert!(foo.contains_key(10));
    /// assert!(foo.contains_key(32));
    /// assert!(!foo.contains_key(2));
    ///
    /// foo.remove(0);
    /// foo.remove(10);
    /// foo.remove(32);
    /// assert!(!foo.contains_key(0));
    /// assert!(!foo.contains_key(10));
    /// assert!(!foo.contains_key(32));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        debug_assert!(
            k >= NumCast::from(LOWER).unwrap(),
            "Out of bounds: Tried inserting at key={:#?}, but lower bound is set to {}",
            k,
            LOWER
        );
        debug_assert!(
            k <= NumCast::from(UPPER).unwrap(),
            "Out of bounds: Tried inserting at key={:#?}, but upper bound is set to {}",
            k,
            UPPER
        );
        if let old_v @ Some(_) = self.data[Self::position(k)].replace(v) {
            old_v
        } else {
            self.len += 1;
            None
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    pub fn remove(&mut self, k: K) -> Option<V> {
        debug_assert!(
            k >= NumCast::from(LOWER).unwrap(),
            "Out of bounds: Tried removing at key={:#?}, but lower bound is set to {}",
            k,
            LOWER
        );
        debug_assert!(
            k <= NumCast::from(UPPER).unwrap(),
            "Out of bounds: Tried removing at key={:#?}, but upper bound is set to {}",
            k,
            UPPER
        );
        if let old_v @ Some(_) = self.data[Self::position(k)].take() {
            self.len -= 1;
            old_v
        } else {
            None
        }
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    pub fn remove_entry(&mut self, k: K) -> Option<(K, V)> {
        debug_assert!(
            k >= NumCast::from(LOWER).unwrap(),
            "Out of bounds: Tried removing at key={:#?}, but lower bound is set to {}",
            k,
            LOWER
        );
        debug_assert!(
            k <= NumCast::from(UPPER).unwrap(),
            "Out of bounds: Tried removing at key={:#?}, but upper bound is set to {}",
            k,
            UPPER
        );
        if let Some(old_v) = self.data[Self::position(k)].take() {
            self.len -= 1;
            Some((k, old_v))
        } else {
            None
        }
    }

    /// An iterator visiting all keys in ascending order.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut keys = foo.keys();
    /// assert_eq!(keys.next(), Some(0));
    /// assert_eq!(keys.next(), Some(10));
    /// assert_eq!(keys.next(), Some(32));
    /// assert_eq!(keys.next(), None);
    /// ```
    pub fn keys(&self) -> Keys<LOWER, UPPER, K, V> {
        Keys::new(self)
    }

    /// A consuming iterator visiting all keys in ascending order.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut keys = foo.into_keys();
    /// assert_eq!(keys.next(), Some(0));
    /// assert_eq!(keys.next(), Some(10));
    /// assert_eq!(keys.next(), Some(32));
    /// assert_eq!(keys.next(), None);
    /// ```
    pub fn into_keys(self) -> IntoKeys<LOWER, UPPER, K, V> {
        IntoKeys::new(self)
    }

    /// An iterator visiting all values in order of ascending keys.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut values = foo.values();
    /// assert_eq!(values.next(), Some(&11.1));
    /// assert_eq!(values.next(), Some(&22.2));
    /// assert_eq!(values.next(), Some(&33.3));
    /// assert_eq!(values.next(), None);
    /// ```
    pub fn values(&self) -> Values<LOWER, UPPER, K, V> {
        Values::new(self)
    }

    /// An iterator visiting all values in order of ascending keys, returning
    /// mutable references.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut values = foo.values_mut();
    /// assert_eq!(values.next(), Some(&mut 11.1));
    /// assert_eq!(values.next(), Some(&mut 22.2));
    /// assert_eq!(values.next(), Some(&mut 33.3));
    /// assert_eq!(values.next(), None);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<LOWER, UPPER, K, V> {
        ValuesMut::new(self)
    }

    /// A consuming iterator visiting all values in order of ascending order.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut values = foo.into_values();
    /// assert_eq!(values.next(), Some(11.1));
    /// assert_eq!(values.next(), Some(22.2));
    /// assert_eq!(values.next(), Some(33.3));
    /// assert_eq!(values.next(), None);
    /// ```
    pub fn into_values(self) -> IntoValues<LOWER, UPPER, K, V> {
        IntoValues::new(self)
    }

    /// An iterator vising all key-value pairs in order of ascending keys.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut iter = foo.iter();
    /// assert_eq!(iter.next(), Some((0, &11.1)));
    /// assert_eq!(iter.next(), Some((10, &22.2)));
    /// assert_eq!(iter.next(), Some((32, &33.3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<LOWER, UPPER, K, V> {
        Iter::new(self)
    }

    /// An iterator vising all key-value pairs in order of ascending keys,
    /// returning mutable references to those values.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut iter = foo.iter_mut();
    /// assert_eq!(iter.next(), Some((0, &mut 11.1)));
    /// assert_eq!(iter.next(), Some((10, &mut 22.2)));
    /// assert_eq!(iter.next(), Some((32, &mut 33.3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<LOWER, UPPER, K, V> {
        IterMut::new(self)
    }

    /// A consuming iterator vising all key-value pairs in order of ascending
    /// keys.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// let mut iter = foo.into_iter();
    /// assert_eq!(iter.next(), Some((0, 11.1)));
    /// assert_eq!(iter.next(), Some((10, 22.2)));
    /// assert_eq!(iter.next(), Some((32, 33.3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_iter(self) -> IntoIter<LOWER, UPPER, K, V> {
        IntoIter::new(self)
    }

    /// A draining iterator vising all key-value pairs in order of ascending
    /// keys.
    ///
    /// ```
    /// use firims::Map;
    ///
    /// let mut foo = Map::<0, 32, usize, f32>::new();
    /// foo.insert(0, 11.1);
    /// foo.insert(32, 33.3);
    /// foo.insert(10, 22.2);
    ///
    /// {
    ///     let mut drain = foo.drain();
    ///     assert_eq!(drain.next(), Some((0, 11.1)));
    ///     assert_eq!(drain.next(), Some((10, 22.2)));
    ///     assert_eq!(drain.next(), Some((32, 33.3)));
    ///     assert_eq!(drain.next(), None);
    /// }
    /// assert!(foo.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<LOWER, UPPER, K, V> {
        Drain::new(self)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs (k, v) for which f(&k, &mut v) returns
    /// false. The elements are visited in order of ascending keys.
    pub fn retain<F>(&mut self, f: F)
    where
        F: Fn(&K, &mut V) -> bool,
    {
        for i in 0..self.len() {
            if self.data[i].is_some()
                && f(
                    &NumCast::from(i + LOWER).unwrap(),
                    &mut self.data[i].as_mut().unwrap(),
                )
            {
                self.data[i] = None;
            }
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// ```
    /// use firims::Map;
    /// let mut foo = Map::<10, 20, usize, f32>::new();
    ///
    /// foo.insert(10, 11.1);
    /// assert_eq!(foo.get(10), Some(&11.1));
    /// assert_eq!(foo.get(20), None);
    /// ```
    pub fn get(&self, k: K) -> Option<&V> {
        debug_assert!(
            k >= NumCast::from(LOWER).unwrap(),
            "Out of bounds: Tried retrieving at key={:#?}, but lower bound is set to {}",
            k,
            LOWER
        );
        debug_assert!(
            k <= NumCast::from(UPPER).unwrap(),
            "Out of bounds: Tried retrieving at key={:#?}, but upper bound is set to {}",
            k,
            UPPER
        );
        self.data[Self::position(k)].as_ref()
    }

    /// Returns a reference to the key-value pair corresponding to the key.
    ///
    /// ```
    /// use firims::Map;
    /// let mut foo = Map::<10, 20, usize, f32>::new();
    ///
    /// foo.insert(10, 11.1);
    /// assert_eq!(foo.get_key_value(10), Some((10, &11.1)));
    /// assert_eq!(foo.get_key_value(20), None);
    /// ```
    pub fn get_key_value(&self, k: K) -> Option<(K, &V)> {
        match self.get(k) {
            Some(value) => Some((k, value)),
            None => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// ```
    /// use firims::Map;
    /// let mut foo = Map::<10, 20, usize, f32>::new();
    ///
    /// foo.insert(10, 11.1);
    /// assert_eq!(foo.get_mut(10), Some(&mut 11.1));
    /// assert_eq!(foo.get(20), None);
    /// ```
    pub fn get_mut(&mut self, k: K) -> Option<&mut V> {
        debug_assert!(
            k >= NumCast::from(LOWER).unwrap(),
            "Out of bounds: Tried retrieving at key={:#?}, but lower bound is set to {}",
            k,
            LOWER
        );
        debug_assert!(
            k <= NumCast::from(UPPER).unwrap(),
            "Out of bounds: Tried retrieving at key={:#?}, but upper bound is set to {}",
            k,
            UPPER
        );
        self.data[Self::position(k)].as_mut()
    }
}

/// Iterator visiting the keys of a [Map].
#[derive(Debug, Clone, Copy)]
pub struct Keys<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> {
    inner: Iter<'a, LOWER, UPPER, K, V>,
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Keys<'a, LOWER, UPPER, K, V> {
    /// Construct a new [Keys] for the `collection` argument.
    fn new(collection: &'a Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            inner: Iter::new(collection),
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for Keys<'a, LOWER, UPPER, K, V>
{
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            Some((k, _)) => Some(k),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.collection.len, Some(UPPER - LOWER))
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for Keys<'a, LOWER, UPPER, K, V>
{
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for Keys<'a, LOWER, UPPER, K, V>
{
}

/// Consuming iterator visiting the keys of a [Map].
#[derive(Debug, Clone)]
pub struct IntoKeys<const LOWER: usize, const UPPER: usize, K: Integer, V> {
    inner: IntoIter<LOWER, UPPER, K, V>,
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> IntoKeys<LOWER, UPPER, K, V> {
    /// Construct a new [IntoKeys] for the `collection` argument.
    fn new(collection: Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            inner: IntoIter::new(collection),
        }
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for IntoKeys<LOWER, UPPER, K, V>
{
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            Some((k, _)) => Some(k),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.collection.len, Some(UPPER - LOWER))
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for IntoKeys<LOWER, UPPER, K, V>
{
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for IntoKeys<LOWER, UPPER, K, V>
{
}

/// Iterator visiting the values of a [Map].
#[derive(Debug, Clone, Copy)]
pub struct Values<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> {
    inner: Iter<'a, LOWER, UPPER, K, V>,
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Values<'a, LOWER, UPPER, K, V> {
    /// Construct a new [Values] for the `collection` argument.
    fn new(collection: &'a Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            inner: Iter::new(collection),
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for Values<'a, LOWER, UPPER, K, V>
{
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.collection.len, Some(UPPER - LOWER))
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for Values<'a, LOWER, UPPER, K, V>
{
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for Values<'a, LOWER, UPPER, K, V>
{
}

/// Iterator returning mutable references to values of a [Map].
#[derive(Debug)]
pub struct ValuesMut<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> {
    inner: IterMut<'a, LOWER, UPPER, K, V>,
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ValuesMut<'a, LOWER, UPPER, K, V> {
    /// Construct a new [ValuesMut] for the `collection` argument.
    fn new(collection: &'a mut Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            inner: IterMut::new(collection),
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for ValuesMut<'a, LOWER, UPPER, K, V>
{
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, v)) = self.inner.next() {
            Some(v)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.collection.len, Some(UPPER - LOWER))
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for ValuesMut<'a, LOWER, UPPER, K, V>
{
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for ValuesMut<'a, LOWER, UPPER, K, V>
{
}

/// Consuming iterator over the values of a [Map].
#[derive(Debug, Clone)]
pub struct IntoValues<const LOWER: usize, const UPPER: usize, K: Integer, V> {
    inner: IntoIter<LOWER, UPPER, K, V>,
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> IntoValues<LOWER, UPPER, K, V> {
    /// Construct a new [IntoValues] for the `collection` argument.
    fn new(collection: Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            inner: IntoIter::new(collection),
        }
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for IntoValues<LOWER, UPPER, K, V>
{
    type Item = V;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.collection.len, Some(UPPER - LOWER))
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for IntoValues<LOWER, UPPER, K, V>
{
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for IntoValues<LOWER, UPPER, K, V>
{
}

/// Iterator visiting the key-value pairs of a [Map], leaving the map empty.
#[derive(Debug)]
pub struct Drain<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> {
    index: usize,
    collection: &'a mut Map<LOWER, UPPER, K, V>,
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Drain<'a, LOWER, UPPER, K, V> {
    /// Construct a new [Drain] for the `collection` argument.
    fn new(collection: &'a mut Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            index: 0,
            collection,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for Drain<'a, LOWER, UPPER, K, V>
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.collection.data.len() {
            let idx = self.index;
            self.index += 1;
            if self.collection.data[idx].is_some() {
                self.collection.len -= 1;
                unsafe {
                    return Some((
                        NumCast::from(idx + LOWER).unwrap(),
                        self.collection.data[idx].take().unwrap_unchecked(),
                    ));
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for Drain<'a, LOWER, UPPER, K, V>
{
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for Drain<'a, LOWER, UPPER, K, V>
{
}

/// Iterator over the key-value pairs of a [Map]
#[derive(Debug, Clone, Copy)]
pub struct Iter<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> {
    index: usize,
    collection: &'a Map<LOWER, UPPER, K, V>,
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iter<'a, LOWER, UPPER, K, V> {
    /// Construct a new [Iter] for the `collection` argument.
    fn new(collection: &'a Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            index: 0,
            collection,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for Iter<'a, LOWER, UPPER, K, V>
{
    type Item = (K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.collection.data.len() {
            let idx = self.index;
            self.index += 1;
            if let Some(v) = &self.collection.data[idx] {
                return Some((NumCast::from(idx + LOWER).unwrap(), &v));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for Iter<'a, LOWER, UPPER, K, V>
{
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for Iter<'a, LOWER, UPPER, K, V>
{
}

/// Iterator over mutable references of the key-value pairs of a [Map].
#[derive(Debug)]
pub struct IterMut<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> {
    index: usize,
    collection: &'a mut Map<LOWER, UPPER, K, V>,
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> IterMut<'a, LOWER, UPPER, K, V> {
    /// Construct a new [IterMut] for the `collection` argument.
    fn new(collection: &'a mut Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            index: 0,
            collection,
        }
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for IterMut<'a, LOWER, UPPER, K, V>
{
    type Item = (K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.collection.data.len() {
            let idx = self.index;
            self.index += 1;
            if self.collection.data[idx].is_some() {
                let ptr = self.collection.data.as_mut_ptr();
                unsafe {
                    let v = (*ptr.add(idx)).as_mut().unwrap_unchecked();
                    return Some((NumCast::from(idx + LOWER).unwrap(), v));
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for IterMut<'a, LOWER, UPPER, K, V>
{
}

impl<'a, const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for IterMut<'a, LOWER, UPPER, K, V>
{
}

/// Consuming iterator over key-value pairs of a [Map].
#[derive(Debug, Clone)]
pub struct IntoIter<const LOWER: usize, const UPPER: usize, K: Integer, V> {
    index: usize,
    collection: Map<LOWER, UPPER, K, V>,
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> IntoIter<LOWER, UPPER, K, V> {
    /// Construct a new [IntoIter] for the `collection` argument.
    fn new(collection: Map<LOWER, UPPER, K, V>) -> Self {
        Self {
            index: 0,
            collection,
        }
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> Iterator
    for IntoIter<LOWER, UPPER, K, V>
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.collection.data.len() {
            let idx = self.index;
            self.index += 1;
            if self.collection.data[idx].is_some() {
                unsafe {
                    let v = self.collection.data[idx].take().unwrap_unchecked();
                    return Some((NumCast::from(idx + LOWER).unwrap(), v));
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.collection.len, Some(UPPER - LOWER))
    }
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> ExactSizeIterator
    for IntoIter<LOWER, UPPER, K, V>
{
}

impl<const LOWER: usize, const UPPER: usize, K: Integer, V> FusedIterator
    for IntoIter<LOWER, UPPER, K, V>
{
}
