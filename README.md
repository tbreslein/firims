# Fibis

FIxed size BIt Set.

## Disclaimer

A lot of utility methods and trait implementations have not been implemented yet!
Also, the data structure is currently limited to elements of type `usize`. This
limitation will be lifted in the future, currently this crate is mostly a proof
of concept in order to see benchmark results.

## General

This crate implements a bit set (currently limited to `usize` elements) for
fixed lower and upper boundaries for your set. I.e., if you create a bit set
with boundaries `10` and `200`, then you can only insert elements in between
those two numbers into the set.

While this is a major limitation, whenever you can set constraints like this you
unlock a lot of performance gains, because you don't need to hash numbers.
Instead, you just track booleans (or in this case bits) telling you whether the
number is in the set or not.

The implementation for this type of data structure is fairly simple, so you
should be able to easily adapt this implementation to suit your own needs; just
remember to honor the MIT license.

## Benchmarks

This crate contains a benchmark file `benches/bench.rs`, which benchmark the
following operations:

- construction of new sets
- insertions
- `.contains()` checks

The benchmarks compares the the `fibis::BitSet` with an `IntSet` from the
`integer_hasher` crate. The benchmarks have been run on two different machines:
An M2 macbook pro, as well as an `x86_64-linux` machine using a Ryzen 7 5800X CPU.

In general, the `fibis::BitSet`s beats the `IntSet` in all those benchmarks,
but the `IntSet` is also way more flexible then the `BitSet`s, allowing you to
insert any `usize` at any time.

Also note that the benchmark results are very different between the M2 and the
x86 architecture, with the latter producing a way larger gap between the
`IntSet` and the `BitSet`s.

### M2 benchmark results

```
test construct intset 100 ... bench:         218 ns/iter (+/- 23)
test construct BitSet 100 ... bench:         167 ns/iter (+/- 4)

test construct intset 1000 ... bench:        1947 ns/iter (+/- 162)
test construct BitSet 1000 ... bench:        1902 ns/iter (+/- 67)

test construct intset 10000 ... bench:       19255 ns/iter (+/- 583)
test construct BitSet 10000 ... bench:       19193 ns/iter (+/- 604)

test construct intset 100000 ... bench:      192277 ns/iter (+/- 6017)
test construct BitSet 100000 ... bench:      191929 ns/iter (+/- 6787)

test construct intset 1000000 ... bench:     1960095 ns/iter (+/- 96563)
test construct BitSet 1000000 ... bench:     1940932 ns/iter (+/- 27855)

test insert intset 100 ... bench:          66 ns/iter (+/- 0)
test insert BitSet 100 ... bench:          83 ns/iter (+/- 0)

test insert intset 1000 ... bench:         668 ns/iter (+/- 21)
test insert BitSet 1000 ... bench:         297 ns/iter (+/- 12)

test insert intset 10000 ... bench:        6695 ns/iter (+/- 259)
test insert BitSet 10000 ... bench:        2873 ns/iter (+/- 16)

test insert intset 100000 ... bench:       80119 ns/iter (+/- 3076)
test insert BitSet 100000 ... bench:       28937 ns/iter (+/- 238)

test insert intset 1000000 ... bench:      958061 ns/iter (+/- 45137)
test insert BitSet 1000000 ... bench:      295254 ns/iter (+/- 10133)

test contains intset 100 ... bench:          59 ns/iter (+/- 1)
test contains BitSet 100 ... bench:          22 ns/iter (+/- 3)

test contains intset 1000 ... bench:         584 ns/iter (+/- 18)
test contains BitSet 1000 ... bench:         225 ns/iter (+/- 8)

test contains intset 10000 ... bench:        6094 ns/iter (+/- 173)
test contains BitSet 10000 ... bench:        2211 ns/iter (+/- 177)

test contains intset 100000 ... bench:       69544 ns/iter (+/- 1845)
test contains BitSet 100000 ... bench:       23035 ns/iter (+/- 878)

test contains intset 1000000 ... bench:      830553 ns/iter (+/- 48834)
test contains BitSet 1000000 ... bench:      241406 ns/iter (+/- 5945)
```

### Ryzen 5800X results

```
test construct intset 100 ... bench:         281 ns/iter (+/- 1)
test construct BitSet 100 ... bench:         102 ns/iter (+/- 6)

test construct intset 1000 ... bench:        2581 ns/iter (+/- 84)
test construct BitSet 1000 ... bench:         905 ns/iter (+/- 1)

test construct intset 10000 ... bench:       23137 ns/iter (+/- 1366)
test construct BitSet 10000 ... bench:        8240 ns/iter (+/- 22)

test construct intset 100000 ... bench:      242723 ns/iter (+/- 15537)
test construct BitSet 100000 ... bench:       92953 ns/iter (+/- 5730)

test construct intset 1000000 ... bench:     2416880 ns/iter (+/- 3579)
test construct BitSet 1000000 ... bench:      809255 ns/iter (+/- 1683)

test insert intset 100 ... bench:          76 ns/iter (+/- 1)
test insert BitSet 100 ... bench:          40 ns/iter (+/- 0)

test insert intset 1000 ... bench:         779 ns/iter (+/- 48)
test insert BitSet 1000 ... bench:         270 ns/iter (+/- 1)

test insert intset 10000 ... bench:        8840 ns/iter (+/- 630)
test insert BitSet 10000 ... bench:        2678 ns/iter (+/- 4)

test insert intset 100000 ... bench:      156391 ns/iter (+/- 14140)
test insert BitSet 100000 ... bench:       25735 ns/iter (+/- 303)

test insert intset 1000000 ... bench:     1975837 ns/iter (+/- 42719)
test insert BitSet 1000000 ... bench:      307859 ns/iter (+/- 387)

test contains intset 100 ... bench:          69 ns/iter (+/- 0)
test contains BitSet 100 ... bench:          24 ns/iter (+/- 1)

test contains intset 1000 ... bench:         688 ns/iter (+/- 1)
test contains BitSet 1000 ... bench:         284 ns/iter (+/- 20)

test contains intset 10000 ... bench:        7607 ns/iter (+/- 453)
test contains BitSet 10000 ... bench:        2541 ns/iter (+/- 8)

test contains intset 100000 ... bench:      135306 ns/iter (+/- 369)
test contains BitSet 100000 ... bench:       25945 ns/iter (+/- 318)

test contains intset 1000000 ... bench:     1656241 ns/iter (+/- 19239)
test contains BitSet 1000000 ... bench:      281744 ns/iter (+/- 13323)
```

## License

> MIT License
>
> Copyright (c) 2024-2025 Tommy Breslein
>
> Permission is hereby granted, free of charge, to any person obtaining a copy
> of this software and associated documentation files (the "Software"), to deal
> in the Software without restriction, including without limitation the rights
> to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
> copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all
> copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
> IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
> FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
> AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
> LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
> OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
> SOFTWARE.
