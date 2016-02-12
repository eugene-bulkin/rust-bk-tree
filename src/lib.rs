use std::collections::HashMap;

struct BKNode<K> {
    pub key: K,
    children: HashMap<u64, K>,
}

impl<K> BKNode<K> {
    pub fn new(key: K) -> BKNode<K> {
        BKNode {
            key: key,
            children: HashMap::new(),
        }
    }
}

struct BKTree<K> {
    pub root: Option<BKNode<K>>,
    metric: Box<Fn(K, K) -> u64>,
}

impl<K> BKTree<K> {
    pub fn new<M: 'static>(metric: M) -> BKTree<K>
        where M: Fn(K, K) -> u64
    {
        BKTree {
            root: None,
            metric: Box::new(metric),
        }
    }

    pub fn add(&mut self, key: K) {
        match self.root {
            Some(_) => {
                // TODO
            }
            None => {
                self.root = Some(BKNode::new(key));
            }
        }
    }
}

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
