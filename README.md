# firims

FIxed Range Integer Maps and Sets

## General

This crate implements a map ([Map]) and set ([BitSet]) for unsigned integer keys
of a known range. For example, if you need a map with integer keys, and you know
those keys can only ever be numbers between 10 and 200.

While this is a major limitation, whenever you can set constraints like this you
unlock a lot of performance gains, because you don't need to hash numbers.
Instead, in case of the bitset, you just track booleans (or in this case bits)
telling you whether the number is in the set or not.

The implementation for this type of data structure is fairly simple, so you
should be able to easily adapt this implementation to suit your own needs; just
remember to honor the MIT license.

## Implementation details

To ensure some of the limitations on the set members and keys, and to have some
useful generic functionality, this crate uses [num_traits] as a dependency. With
that, the keys / set members are limited to types implementing the [Integer]
type.

The two data structures, the [Map] and the [BitSet], have very simple
implementations. The former is just a `Vec<V>`, where `V` is your value type,
and it maps keys to indexes in the `Vec` through a simple addition. As
simple as that may be, the benefit of the [Map] is that it implements most of
the of the same interface of the [std::collections::HashMap], making
this a good drop-in replacement for most use cases (given that the
[Map] constraints fir you use case).

The [BitSet] is, well, a bit set. Each key is mapped to a bit in an element in a
`Vec<u64>`, and a value being present just means that the bit is set to 1.
Again, very simple implementation, pretty easy to replicate, but it implements
the majority of the [std::collections::HashSet] interface in order to make the
bitset a drop-in replacement.

## Benchmarks

This crate contains a benchmark file `benches/bench.rs`, which benchmarks the
following operations:

- construction of new sets
- insertions
- `.contains()` checks

The benchmarks compares the [BitSet] with an `IntSet` from the `integer_hasher`
crate, and the [Map] with an `IntMap`. The benchmarks have been run on two
different machines: An M2 macbook pro, as well as an `x86_64-linux` machine
using a Ryzen 7 9800x3D CPU.

In general, the [BitSet]s beats the `IntSet` in all those benchmarks, but note
note that the `IntSet` is also way more flexible then the these data structures,
allowing you to insert any sort of integer at any time. The range constraint
on the values / keys is what unlocks those performance gains, but obviously
it does not fit any use case.

Also note that the benchmark results are very different between the M2 and the
x86 architecture, with the latter producing a way larger gap between the
`IntSet` and the [BitSet]s.

### M2

#### `IntSet` vs [BitSet]

| bench \ input size |    100 |    1,000 |    10,000 |    100,000 |    1,000,000 |
| ------------------ | -----: | -------: | --------: | ---------: | -----------: |
| **construction**   |    ... |      ... |       ... |        ... |          ... |
| `IntSet`           | 281 ns | 2,576 ns | 25,711 ns | 254,961 ns | 2,585,656 ns |
| [BitSet]           | 189 ns | 2,015 ns | 19,890 ns | 198,217 ns | 1,987,995 ns |
| **insertion**      |    ... |      ... |       ... |        ... |          ... |
| `IntSet`           | 281 ns | 2,576 ns | 25,711 ns | 254,961 ns | 2,585,656 ns |
| [BitSet]           | 189 ns | 2,015 ns | 19,890 ns | 198,217 ns | 1,987,995 ns |
| **contains**       |    ... |      ... |       ... |        ... |          ... |
| `IntSet`           |  62 ns |   597 ns |  6,207 ns |  70,974 ns |   913,086 ns |
| [BitSet]           |  22 ns |   229 ns |  2,279 ns |  23,698 ns |   247,242 ns |

#### `IntMap` vs [Map]

| bench \ input size |    100 |    1,000 |    10,000 |    100,000 |    1,000,000 |
| ------------------ | -----: | -------: | --------: | ---------: | -----------: |
| **insertion**      |    ... |      ... |       ... |        ... |          ... |
| `IntMap`           | 178 ns | 1,790 ns | 18,243 ns | 186,263 ns | 3,044,192 ns |
| [Map]              |  41 ns |   417 ns |  4,665 ns |  67,046 ns |   837,838 ns |
| **contains**       |    ... |      ... |       ... |        ... |          ... |
| `IntMap`           | 126 ns | 1,121 ns | 16,951 ns | 667,448 ns | 9,376,399 ns |
| [Map]              |  30 ns |   306 ns |  3,010 ns |  35,056 ns |   458,998 ns |

### Ryzen7 9800X3D

#### `IntSet` vs [BitSet]

| bench \ input size |    100 |    1,000 |    10,000 |    100,000 |    1,000,000 |
| ------------------ | -----: | -------: | --------: | ---------: | -----------: |
| **construction**   |    ... |      ... |       ... |        ... |          ... |
| `IntSet`           | 263 ns | 2,541 ns | 23,419 ns | 251,295 ns | 2,335,786 ns |
| [BitSet]           |  75 ns |   681 ns |  6,622 ns |  66,238 ns |   721,745 ns |
| **insertion**      |    ... |      ... |       ... |        ... |          ... |
| `IntSet`           |  83 ns |   804 ns |  8,814 ns | 106,878 ns | 1,629,813 ns |
| [BitSet]           |  58 ns |   339 ns |  2,990 ns |  26,420 ns |   348,972 ns |
| **contains**       |    ... |      ... |       ... |        ... |          ... |
| `IntSet`           |  52 ns |   489 ns |  4,973 ns |  67,423 ns | 1,096,985 ns |
| [BitSet]           |  19 ns |   196 ns |  1,922 ns |  19,189 ns |   194,224 ns |

#### `IntMap` vs [Map]

| bench \ input size |    100 |    1,000 |    10,000 |    100,000 |    1,000,000 |
| ------------------ | -----: | -------: | --------: | ---------: | -----------: |
| **insertion**      |    ... |      ... |       ... |        ... |          ... |
| `IntMap`           |  80 ns |   761 ns |  8,198 ns | 121,147 ns | 1,778,716 ns |
| [Map]              |  30 ns |   297 ns |  3,231 ns |  34,430 ns |   484,658 ns |
| **contains**       |    ... |      ... |       ... |        ... |          ... |
| `IntMap`           | 152 ns | 1,503 ns | 16,344 ns | 640,985 ns | 8,398,847 ns |
| [Map]              |  16 ns |   171 ns |  2,012 ns |  27,972 ns |   357,651 ns |

## License

> MIT License
>
> Copyright (c) 2025 Tommy Breslein
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
