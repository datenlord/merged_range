# merged_range

A crate that can merge overlapping ranges

[![Apache licensed][apache-badge]][apache-url]
[![CI][actions-badge]][actions-url]

[apache-badge]: https://img.shields.io/badge/license-Apache-blue.svg
[apache-url]: https://github.com/datenlord/merged_range/blob/master/LICENSE
[actions-badge]: https://github.com/datenlord/merged_range/actions/workflows/ci.yml/badge.svg
[actions-url]: https://github.com/datenlord/merged_range/actions/workflows/ci.yml

## Overview

merged_range is used to query whether the given range is contained in the existing range, if it is contained, return true, otherwise return false. it uses a sorted vector to store ranges. and it can merge the new range with the existing ranges. insert and query time complexity is both O(logn).

## Example

add dependency to Cargo.toml

```toml
[dependencies]
merged_range = "0.1.0"
```

then use it in your code

```rust
use merged_range::MergedRange;

let mut mr = MergedRange::new();
mr.insert_range(&(1..10));
mr.insert_range(&(5..20));

assert_eq!(mr.contains_range(&(3..15)), true);
assert_eq!(mr.contains_range(&(10..21)), false);
```

## License

This project is licensed under the [MIT license][apache-url].