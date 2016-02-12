use std::collections::HashMap;

pub struct BKNode<K> {
    pub key: K,
    pub children: HashMap<u64, K>,
}

impl<K> BKNode<K> {
    pub fn new(key: K) -> BKNode<K> {
        BKNode {
            key: key,
            children: HashMap::new(),
        }
    }
}

pub struct BKTree<K> {
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
