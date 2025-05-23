#![allow(clippy::unit_arg)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use integer_hasher::{BuildIntHasher, IntMap, IntSet};
use rand::Rng;
use std::collections::{HashMap, HashSet};

fn construction<const LOWER: usize, const UPPER: usize>(c: &mut Criterion) {
    c.bench_function(&format!("construct IntSet {}", UPPER).to_string(), |b| {
        b.iter(|| black_box(IntSet::from_iter(LOWER..=UPPER)))
    });
    c.bench_function(
        &format!("construct firims::BitSet {}", UPPER).to_string(),
        |b| {
            b.iter(|| {
                black_box(firims::BitSet::<LOWER, UPPER, usize>::from_iter(
                    LOWER..=UPPER,
                ))
            })
        },
    );
}

fn get_rng(lower: usize, upper: usize) -> Vec<usize> {
    let mut rng = rand::rng();
    (0..upper / 2)
        .map(|_| rng.random_range(lower..upper))
        .collect()
}

fn get_rng_key_value(lower: usize, upper: usize) -> Vec<(usize, f32)> {
    let mut rng = rand::rng();
    (0..upper / 2)
        .map(|_| (rng.random_range(lower..upper), rng.random()))
        .collect()
}

fn insertion<const LOWER: usize, const UPPER: usize>(c: &mut Criterion) {
    let rng = get_rng(LOWER, UPPER);
    let mut s: IntSet<usize> = HashSet::with_capacity_and_hasher(UPPER, BuildIntHasher::default());
    c.bench_function(&format!("insert IntSet {}", UPPER).to_string(), |b| {
        b.iter(|| {
            for x in rng.iter() {
                black_box(s.insert(*x));
            }
        })
    });
    let mut s = firims::BitSet::<LOWER, UPPER, usize>::new();
    c.bench_function(
        &format!("insert firims::BitSet {}", UPPER).to_string(),
        |b| {
            b.iter(|| {
                for x in rng.iter() {
                    black_box(s.insert(*x));
                }
            })
        },
    );

    let rng = get_rng_key_value(LOWER, UPPER);
    let mut s: IntMap<usize, f32> =
        HashMap::with_capacity_and_hasher(UPPER, BuildIntHasher::default());
    c.bench_function(&format!("insert IntMap {}", UPPER).to_string(), |b| {
        b.iter(|| {
            for (x, y) in rng.iter() {
                black_box(s.insert(*x, *y));
            }
        })
    });
    let mut s = firims::VecMap::<LOWER, UPPER, usize, f32>::new();
    c.bench_function(&format!("insert firims::Map {}", UPPER).to_string(), |b| {
        b.iter(|| {
            for (x, y) in rng.iter() {
                black_box(s.insert(*x, *y));
            }
        })
    });
}

fn contains<const LOWER: usize, const UPPER: usize>(c: &mut Criterion) {
    let rng = get_rng(LOWER, UPPER);
    let s = IntSet::from_iter(LOWER..=UPPER);
    c.bench_function(&format!("contains intset {}", UPPER).to_string(), |b| {
        b.iter(|| {
            for x in rng.iter() {
                black_box(s.contains(x));
            }
        })
    });
    let s = firims::BitSet::<LOWER, UPPER, usize>::from_iter(LOWER..=UPPER);
    c.bench_function(&format!("contains BitSet {}", UPPER).to_string(), |b| {
        b.iter(|| {
            for x in rng.iter() {
                black_box(s.contains(x));
            }
        })
    });

    let rng_tuple = get_rng_key_value(LOWER, UPPER);
    let mut s: IntMap<usize, f32> =
        HashMap::with_capacity_and_hasher(UPPER, BuildIntHasher::default());
    for (x, y) in rng_tuple.iter() {
        s.insert(*x, *y);
    }
    c.bench_function(&format!("contains IntMap {}", UPPER).to_string(), |b| {
        b.iter(|| {
            for x in rng.iter() {
                black_box(s.contains_key(x));
            }
        })
    });
    let mut s = firims::VecMap::<LOWER, UPPER, usize, f32>::new();
    for (x, y) in rng_tuple.iter() {
        s.insert(*x, *y);
    }
    c.bench_function(
        &format!("contains firims::Map {}", UPPER).to_string(),
        |b| {
            b.iter(|| {
                for x in rng.iter() {
                    black_box(s.contains_key(x));
                }
            })
        },
    );
}

criterion_group!(
    construction_bench,
    construction<0, 100>,
    construction<0, 1_000>,
    construction<0, 10_000>,
    construction<0, 100_000>,
    construction<0, 1_000_000>
);

criterion_group!(
    insertion_bench,
    insertion<0, 100>,
    insertion<0, 1_000>,
    insertion<0, 10_000>,
    insertion<0, 100_000>,
    insertion<0, 1_000_000>
);

criterion_group!(
    contains_bench,
    contains<0, 100>,
    contains<0, 1_000>,
    contains<0, 10_000>,
    contains<0, 100_000>,
    contains<0, 1_000_000>
);

criterion_main!(construction_bench, insertion_bench, contains_bench);
