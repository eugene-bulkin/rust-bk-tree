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

#[test]
fn tree_find() {
    /*
     * This example tree is from
     * https://nullwords.wordpress.com/2013/03/13/the-bk-tree-a-data-structure-for-spell-checking/
     */
    let mut tree: BKTree<&str> = BKTree::new(levenshtein);
    tree.add("book");
    tree.add("books");
    tree.add("cake");
    tree.add("boo");
    tree.add("cape");
    tree.add("boon");
    tree.add("cook");
    tree.add("cart");
    assert_eq!(tree.find("caqe", 1), vec!["cake", "cape"]);
    assert_eq!(tree.find("cape", 1), vec!["cake", "cape"]);
    assert_eq!(tree.find("book", 1), vec!["book", "books", "boo", "boon", "cook"]);
    assert_eq!(tree.find("book", 0), vec!["book"]);
    assert!(tree.find("foobar", 1).is_empty());
}
