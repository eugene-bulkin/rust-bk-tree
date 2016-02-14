pub mod metrics;

use std::collections::HashMap;

/// A node within the BK-tree.
pub struct BKNode<K: Copy> {
    /// The key determining the node.
    pub key: K,
    /// A hash-map of children, indexed by their distance from this node based
    /// on the metric being used by the tree.
    pub children: HashMap<u64, BKNode<K>>,
}

impl<K> BKNode<K> where K: Copy
{
    /// Constructs a new `BKNode<K>`.
    pub fn new(key: K) -> BKNode<K>
        where K: Copy
    {
        BKNode {
            key: key,
            children: HashMap::new(),
        }
    }

    pub fn add_child(&mut self, distance: u64, key: K) {
        self.children.insert(distance, BKNode::new(key));
    }

    pub fn get_key(&self) -> K {
        self.key
    }
}

/// A representation of a [BK-tree](https://en.wikipedia.org/wiki/BK-tree).
pub struct BKTree<K>
    where K: Copy
{
    /// The root node. May be empty if nothing has been put in the tree yet.
    pub root: Option<BKNode<K>>,
    /// The metric being used to determine the distance between nodes on the
    /// tree.
    metric: Box<Fn(K, K) -> u64>,
}

impl<K> BKTree<K> where K: Copy
{
    /// Constructs a new `BKTree<K>` using the provided metric.
    ///
    /// Note that we make no assumptions about the metric function provided.
    /// *Ideally* it is actually a
    /// [valid metric](https://en.wikipedia.org/wiki/Metric_(mathematics)),
    /// but you may choose to use one that is not technically a valid metric.
    /// If you do not use a valid metric, however, you may find that the tree
    /// behaves confusingly for some values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bk_tree::{BKTree, metrics};
    ///
    /// let tree: BKTree<&str> = BKTree::new(metrics::levenshtein);
    /// ```
    pub fn new<M: 'static>(metric: M) -> BKTree<K>
        where M: Fn(K, K) -> u64
    {
        BKTree {
            root: None,
            metric: Box::new(metric),
        }
    }

    /// Adds a key to the tree.
    ///
    /// If the tree is empty, this simply sets the root to
    /// `Some(BKNode::new(key))`. Otherwise, we iterate downwards through the
    /// tree until we see a node that does not have a child with the same
    /// distance. If we encounter a node that is exactly the same distance from
    /// the root node, then the new key is the same as that node's key and so we
    /// do nothing. **Note**: This means that if your metric allows for unequal
    /// keys to return 0, you will see improper behavior!
    ///
    /// # Examples
    ///
    /// ```
    /// use bk_tree::{BKTree, metrics};
    ///
    /// let mut tree: BKTree<&str> = BKTree::new(metrics::levenshtein);
    ///
    /// tree.add("foo");
    /// tree.add("bar");
    /// ```
    pub fn add(&mut self, key: K) {
        match self.root {
            Some(ref mut root) => {
                let mut cur_node = root;
                let mut cur_dist = (&self.metric)(cur_node.key, key);
                while cur_node.children.contains_key(&cur_dist) && cur_dist > 0 {
                    // We have to do some moving around here to safely get the
                    // child corresponding to the current distance away without
                    // accidentally trying to mutate the wrong thing.
                    //
                    let current = cur_node;
                    let next_node = current.children.get_mut(&cur_dist).unwrap();

                    cur_node = next_node;
                    cur_dist = (&self.metric)(cur_node.key, key);
                }
                cur_node.add_child(cur_dist, key);
            }
            None => {
                self.root = Some(BKNode::new(key));
            }
        }
    }
}
