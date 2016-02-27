# rust-bk-tree
A BK-tree implementation in Rust.

[![Build Status](https://travis-ci.org/eugene-bulkin/rust-bk-tree.svg?branch=master)](https://travis-ci.org/eugene-bulkin/rust-bk-tree) [![Crates.io](https://img.shields.io/crates/v/bk-tree.svg)](https://crates.io/crates/bk-tree)

[Documentation](http://eugene-bulkin.github.io/rust-docs/rust-bk-tree/bk_tree/)

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

To run benchmarks, you need to have the nightly version of Rust installed. If you do (and use [multirust](/brson/multirust), for example), then you can run

```
multirust nightly cargo bench
```

to run benchmarks.
