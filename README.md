# rust-bk-tree
A BK-tree implementation in Rust.

[![Build Status](https://travis-ci.org/eugene-bulkin/rust-bk-tree.svg?branch=master)](https://travis-ci.org/eugene-bulkin/rust-bk-tree) [![Crates.io](https://img.shields.io/crates/v/bk-tree.svg)](https://crates.io/crates/bk-tree) 

[Documentation](https://docs.rs/bk-tree/)

# Examples

Here's some example usages:

```rust
use bk_tree::{BKTree, metrics};

// A BK-tree using the Levenshtein distance metric.
let mut tree: BKTree<&str> = BKTree::new(metrics::levenshtein);

tree.add("foo");
tree.add("bar");
tree.add("baz");
tree.add("bup");

tree.find("bar", 0); // returns vec!["bar"]
tree.find("bar", 1); // returns vec!["bar", "baz"]
tree.find("bup", 2); // returns vec!["bar", "baz", "bup"]
```

# Benchmarks

To run benchmarks, you need to have the nightly version of Rust installed. If you have rustup installed, then you can run

```
rustup run nightly cargo bench
```

to run benchmarks.
