extern crate bk_tree;

use bk_tree::{BKNode, BKTree};
use bk_tree::metrics::levenshtein;

#[test]
fn node_construct() {
    let node: BKNode<&str> = BKNode::new("foo");
    assert_eq!(node.key, "foo");
    assert!(node.children.is_empty());
}

#[test]
fn tree_construct() {
    let tree: BKTree<&str> = BKTree::new(levenshtein);
    assert!(tree.root.is_none());
}

#[test]
fn tree_add() {
    let mut tree: BKTree<&str> = BKTree::new(levenshtein);
    tree.add("foo");
    match tree.root {
        Some(ref root) => {
            assert_eq!(root.key, "foo");
        },
        None => { assert!(false); }
    }
    tree.add("fop");
    println!("foo fop {}", levenshtein("foo", "fop"));
    assert_eq!(tree.root.unwrap().children.get(&1).unwrap().key, "fop");
}
