pub mod metrics;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{self, Debug, Formatter};
use std::iter::Extend;
use std::default::Default;

/// A trait for a *metric* (distance function).
///
/// Implementations should follow the metric axioms:
///
/// * **Zero**: `distance(a, b) == 0` if and only if `a == b`
/// * **Symmetry**: `distance(a, b) == distance(b, a)`
/// * **Triangle inequality**: `distance(a, c) <= distance(a, b) + distance(b, c)`
///
/// If any of these rules are broken, then the BK-tree may give unexpected
/// results.
pub trait Metric<K: ?Sized> {
    fn distance(&self, a: &K, b: &K) -> u64;
}

/// A node within the [BK-tree](https://en.wikipedia.org/wiki/BK-tree).
pub struct BKNode<K> {
    /// The key determining the node.
    pub key: K,
    /// A hash-map of children, indexed by their distance from this node based
    /// on the metric being used by the tree.
    pub children: HashMap<u64, BKNode<K>>,
}

impl<K> BKNode<K>
{
    /// Constructs a new `BKNode<K>`.
    pub fn new(key: K) -> BKNode<K>
    {
        BKNode {
            key: key,
            children: HashMap::new(),
        }
    }

    /// Add a child to the node.
    ///
    /// Given the distance from this node's key, add the given key as a child
    /// node. *Warning:* this does not test the invariant that the distance as
    /// measured by the tree between this node's key and the provided key
    /// actually matches the distance passed in.
    ///
    /// # Examples
    ///
    /// ```
    /// use bk_tree::BKNode;
    ///
    /// let mut foo = BKNode::new("foo");
    /// foo.add_child(1, "fop");
    /// ```
    pub fn add_child(&mut self, distance: u64, key: K) {
        self.children.insert(distance, BKNode::new(key));
    }
}

impl<K> Debug for BKNode<K> where K: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "BKNode({:?}: {:?})", self.key, self.children)
    }
}

/// A representation of a [BK-tree](https://en.wikipedia.org/wiki/BK-tree).
pub struct BKTree<K, M = metrics::Levenshtein>
{
    /// The root node. May be empty if nothing has been put in the tree yet.
    pub root: Option<BKNode<K>>,
    /// The metric being used to determine the distance between nodes on the
    /// tree.
    metric: M,
}

impl<K, M> BKTree<K, M>
    where M: Metric<K>
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
    /// let tree: BKTree<&str> = BKTree::new(metrics::Levenshtein);
    /// ```
    pub fn new(metric: M) -> BKTree<K, M>
    {
        BKTree {
            root: None,
            metric: metric,
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
    /// let mut tree: BKTree<&str> = BKTree::new(metrics::Levenshtein);
    ///
    /// tree.add("foo");
    /// tree.add("bar");
    /// ```
    pub fn add(&mut self, key: K) {
        match self.root {
            Some(ref mut root) => {
                let mut cur_node = root;
                let mut cur_dist = self.metric.distance(&cur_node.key, &key);
                while cur_node.children.contains_key(&cur_dist) && cur_dist > 0 {
                    // We have to do some moving around here to safely get the
                    // child corresponding to the current distance away without
                    // accidentally trying to mutate the wrong thing.
                    //
                    let current = cur_node;
                    let next_node = current.children.get_mut(&cur_dist).unwrap();

                    cur_node = next_node;
                    cur_dist = self.metric.distance(&cur_node.key, &key);
                }
                cur_node.add_child(cur_dist, key);
            }
            None => {
                self.root = Some(BKNode::new(key));
            }
        }
    }

    /// Searches for a key in the BK-tree given a certain tolerance.
    ///
    /// This traverses the tree searching for all keys with distance within
    /// `tolerance` of of the key provided. The tolerance may be zero, in which
    /// case this searches for exact matches. The results are returned in a
    /// `Vec<K>`.
    ///
    /// *Note:* There is no guarantee on the order of the vector provided. The
    /// elements returned may or may not be sorted in terms of distance from the
    /// provided key.
    ///
    /// # Examples
    /// ```
    /// use bk_tree::{BKTree, metrics};
    ///
    /// let mut tree: BKTree<&str> = BKTree::new(metrics::Levenshtein);
    ///
    /// tree.add("foo");
    /// tree.add("fop");
    /// tree.add("bar");
    ///
    /// assert_eq!(tree.find("foo", 0), vec!["foo"]);
    /// assert_eq!(tree.find("foo", 1), vec!["foo", "fop"]);
    /// assert!(tree.find("foz", 0).is_empty());
    /// ```
    pub fn find<Q: ?Sized>(&self, key: &Q, tolerance: u64) -> Vec<K>
        where K: Borrow<Q> + Clone, M: Metric<Q>
    {
        match self.root {
            Some(ref root) => {
                let mut result: Vec<K> = Vec::new();
                self.recursive_find(root, &mut result, key, tolerance);
                result
            }
            None => Vec::new(),
        }
    }

    fn recursive_find<Q: ?Sized>(&self, node: &BKNode<K>, result: &mut Vec<K>, key: &Q, tolerance: u64)
        where K: Borrow<Q> + Clone, M: Metric<Q>
    {
        let cur_dist = self.metric.distance(node.key.borrow() as &Q, key);
        let min_dist = if cur_dist < tolerance {
            0
        } else {
            cur_dist - tolerance
        };
        let max_dist = cur_dist + tolerance;

        if cur_dist <= tolerance {
            result.push(node.key.clone());
        }

        let mut child_result = Vec::new();
        for (dist, ref child) in &node.children {
            if *dist >= min_dist && *dist <= max_dist {
                self.recursive_find(child, &mut child_result, key, tolerance);
            }
        }
        result.extend(child_result);
    }

    /// Searches for an exact match in the tree.
    ///
    /// This is pretty much the same as calling `find` with a tolerance of 0,
    /// with the addition of pulling the value out of the vector if there was
    /// a match.
    ///
    /// # Examples
    /// ```
    /// use bk_tree::{BKTree, metrics};
    ///
    /// let mut tree: BKTree<&str> = BKTree::new(metrics::Levenshtein);
    ///
    /// tree.add("foo");
    /// tree.add("fop");
    /// tree.add("bar");
    ///
    /// assert_eq!(tree.find_exact("foz"), None);
    /// assert_eq!(tree.find_exact("foo"), Some("foo"));
    /// ```
    pub fn find_exact<Q: ?Sized>(&self, key: &Q) -> Option<K>
        where K: Borrow<Q> + Clone, M: Metric<Q>
    {
        let result = self.find(key, 0);
        result.into_iter().next()
    }
}

impl<K: Clone, M: Metric<K>> Extend<K> for BKTree<K, M> {
    /// Adds multiple keys to the tree.
    ///
    /// Given an iterator with items of type `K`, this method simply adds every
    /// item to the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use bk_tree::{BKTree, metrics};
    ///
    /// let mut tree: BKTree<&str> = BKTree::new(metrics::Levenshtein);
    ///
    /// tree.extend(vec!["foo", "bar"]);
    /// ```
    fn extend<I: IntoIterator<Item = K>>(&mut self, keys: I) {
        for key in keys {
            self.add(key);
        }
    }
}

impl<K: AsRef<str>> Default for BKTree<K> {
    fn default() -> BKTree<K> {
        BKTree::new(metrics::Levenshtein)
    }
}
