extern crate bk_tree;

use std::default::Default;
use std::fmt::Debug;

use bk_tree::{BKNode, BKTree};

fn assert_eq_sorted<'t, T: 't, I>(left: I, right: &[(u64, T)])
    where T: Ord + Debug, I: Iterator<Item=(u64, &'t T)>
{
    let mut left_mut: Vec<_> = left.collect();
    let mut right_mut: Vec<_> = right.iter().map(|&(dist, ref key)| (dist, key)).collect();

    left_mut.sort();
    right_mut.sort();

    assert_eq!(left_mut, right_mut);
}

#[test]
fn node_construct() {
    let node: BKNode<&str> = BKNode::new("foo");
    assert_eq!(node.key, "foo");
    assert!(node.children.is_empty());
}

#[test]
fn tree_construct() {
    let tree: BKTree<&str> = Default::default();
    assert!(tree.root.is_none());
}

#[test]
fn tree_add() {
    let mut tree: BKTree<&str> = Default::default();
    tree.add("foo");
    match tree.root {
        Some(ref root) => {
            assert_eq!(root.key, "foo");
        },
        None => { assert!(false); }
    }
    tree.add("fop");
    tree.add("f\u{e9}\u{e9}");
    match tree.root {
        Some(ref root) => {
            assert_eq!(root.children.get(&1).unwrap().key, "fop");
            assert_eq!(root.children.get(&2).unwrap().key, "f\u{e9}\u{e9}");
        },
        None => { assert!(false); }
    }
}

#[test]
fn tree_extend() {
    let mut tree: BKTree<&str> = Default::default();
    tree.extend(vec!["foo", "fop"]);
    match tree.root {
        Some(ref root) => {
            assert_eq!(root.key, "foo");
        },
        None => { assert!(false); }
    }
    assert_eq!(tree.root.unwrap().children.get(&1).unwrap().key, "fop");
}

#[test]
fn tree_find() {
    /*
     * This example tree is from
     * https://nullwords.wordpress.com/2013/03/13/the-bk-tree-a-data-structure-for-spell-checking/
     */
    let mut tree: BKTree<&str> = Default::default();
    tree.add("book");
    tree.add("books");
    tree.add("cake");
    tree.add("boo");
    tree.add("cape");
    tree.add("boon");
    tree.add("cook");
    tree.add("cart");
    assert_eq_sorted(tree.find("caqe", 1), &[(1, "cake"), (1, "cape")]);
    assert_eq_sorted(tree.find("cape", 1), &[(1, "cake"), (0, "cape")]);
    assert_eq_sorted(tree.find("book", 1), &[(0, "book"), (1, "books"), (1, "boo"), (1, "boon"), (1, "cook")]);
    assert_eq_sorted(tree.find("book", 0), &[(0, "book")]);
    assert!(tree.find("foobar", 1).next().is_none());
}

#[test]
fn tree_find_exact() {
    let mut tree: BKTree<&str> = Default::default();
    tree.add("book");
    tree.add("books");
    tree.add("cake");
    tree.add("boo");
    tree.add("cape");
    tree.add("boon");
    tree.add("cook");
    tree.add("cart");
    assert_eq!(tree.find_exact("caqe"), None);
    assert_eq!(tree.find_exact("cape"), Some(&"cape"));
    assert_eq!(tree.find_exact("book"), Some(&"book"));
}
