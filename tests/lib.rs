extern crate bk_tree;

use bk_tree::{BKNode, BKTree};

#[test]
fn node_construct() {
    let node: BKNode<&str> = BKNode::new("foo");
    assert_eq!(node.key, "foo");
    assert!(node.children.is_empty());
}

#[test]
fn tree_construct() {
    let metric = |a: &str, b: &str| {
        let a_len = a.len() as i64;
        let b_len = b.len() as i64;
        (a_len - b_len).abs() as u64
    };
    let tree: BKTree<&str> = BKTree::new(metric);
    assert!(tree.root.is_none());
}

#[test]
fn tree_add() {
    let metric = |a: &str, b: &str| {
        let a_len = a.len() as i64;
        let b_len = b.len() as i64;
        (a_len - b_len).abs() as u64
    };
    let mut tree: BKTree<&str> = BKTree::new(metric);
    tree.add("foo");
    assert!(!tree.root.is_none());
    assert_eq!(tree.root.unwrap().key, "foo");
}
