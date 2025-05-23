#![doc = include_str!("../README.md")]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

mod bitset;
mod integer;
mod vec_map;

pub use bitset::BitSet;
pub use integer::Integer;
pub use vec_map::VecMap;

type BackingType = u64;
const BIT_WIDTH: usize = BackingType::BITS as usize;

#[cfg(test)]
mod tests {
    use num_traits::NumCast;

    use crate::{BitSet, Integer};

    fn run_test<const LOWER: usize, const UPPER: usize, T: Integer>() {
        let input = (LOWER..=UPPER)
            .map(|k| (NumCast::from(k).unwrap(), 10.0 + k as f32))
            .collect::<Vec<(T, f32)>>();
        let mut set = BitSet::<LOWER, UPPER, T>::new();
        let mut map = crate::VecMap::<LOWER, UPPER, T, f32>::new();

        assert!(set.is_empty());
        assert!(map.is_empty());
        for (k, v) in input.iter() {
            assert!(!set.contains(k));
            assert!(!map.contains_key(*k));
            assert!(map.get(*k).is_none());

            set.insert(*k);
            assert!(map.insert(*k, *v).is_none());

            assert!(set.contains(k));
            assert!(map.contains_key(*k));
            assert!(map.get(*k).is_some_and(|x| *x == *v));
        }

        assert_eq!(set.len(), input.len());
        assert_eq!(map.len(), input.len());

        for (k, v) in input.iter() {
            assert!(set.contains(k));
            assert!(map.contains_key(*k));
            assert!(map.get(*k).is_some_and(|x| *x == *v));

            set.remove(k);
            map.remove(*k);

            assert!(!set.contains(k));
            assert!(!map.contains_key(*k));
            assert!(map.get(*k).is_none());
        }
        assert!(set.is_empty());
        assert!(map.is_empty());
    }

    macro_rules! clamp {
        ($x:expr, $min_:expr, $max_:expr) => {
            if $x < $min_ {
                $min_
            } else if $x > $max_ {
                $max_
            } else {
                $x
            }
        };
    }

    #[test]
    fn test_u8() {
        type T = u8;
        const LOWER: T = T::MAX / 2;
        const UPPER: T = clamp!(LOWER + 100, T::MIN, T::MAX);
        run_test::<{ LOWER as usize }, { UPPER as usize }, T>();
    }

    #[test]
    fn test_u16() {
        type T = u16;
        const LOWER: T = T::MAX / 2;
        const UPPER: T = clamp!(LOWER + 10000, T::MIN, T::MAX);
        run_test::<{ LOWER as usize }, { UPPER as usize }, T>();
    }

    #[test]
    fn test_u32() {
        type T = u32;
        const LOWER: T = T::MAX / 2;
        const UPPER: T = clamp!(LOWER + 10000000, T::MIN, T::MAX);
        run_test::<{ LOWER as usize }, { UPPER as usize }, T>();
    }

    #[test]
    fn test_usize() {
        type T = usize;
        const LOWER: usize = T::MAX / 2;
        const UPPER: usize = clamp!(LOWER + 10000000, T::MIN, T::MAX);
        run_test::<LOWER, UPPER, T>();
    }
}
