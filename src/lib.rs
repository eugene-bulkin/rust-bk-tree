pub mod metrics;

use std::{
    fmt::{Debug, Formatter, Result as FmtResult},
    iter::Extend,
    borrow::Borrow,
    collections::VecDeque,
};

#[cfg(feature = "enable-fnv")]
extern crate fnv;
#[cfg(feature = "enable-fnv")]
use fnv::FnvHashMap;

#[cfg(not(feature = "enable-fnv"))]
use std::collections::HashMap;

#[cfg(feature = "serde-support")]
extern crate serde_derive;

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
    fn distance(&self, a: &K, b: &K) -> u32;
    fn threshold_distance(&self, a: &K, b: &K, threshold: u32) -> Option<u32>;
}

/// A node within the [BK-tree](https://en.wikipedia.org/wiki/BK-tree).
#[cfg_attr(feature = "serde-support", derive(serde_derive::Serialize, serde_derive::Deserialize))]
pub struct BKNode<K> {
    /// The key determining the node.
    key: K,
    /// A hash-map of children, indexed by their distance from this node based
    /// on the metric being used by the tree.
    #[cfg(feature = "enable-fnv")]
    children: FnvHashMap<u32, Box<BKNode<K>>>,
    #[cfg(not(feature = "enable-fnv"))]
    children: HashMap<u32, Box<BKNode<K>>>,
    max_child_distance: Option<u32>,
}

impl<K> BKNode<K> {
    /// Constructs a new `BKNode<K>`.
    pub fn new(key: K) -> BKNode<K> {
        BKNode {
            key,
            #[cfg(feature = "enable-fnv")]
            children: fnv::FnvHashMap::default(),
            #[cfg(not(feature = "enable-fnv"))]
            children: HashMap::default(),
            max_child_distance: None,
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
    /// ```ignore
    /// use bk_tree::BKNode;
    ///
    /// let mut foo = BKNode::new("foo");
    /// foo.add_child(1, "fop");
    /// ```
    pub fn add_child(&mut self, distance: u32, key: K) {
        self.children.insert(distance, Box::new(BKNode::new(key)));
        self.max_child_distance = self.max_child_distance.max(Some(distance));
    }
}

#[cfg(feature = "serde-support")]
impl<K> BKNode<K>
where
    K: serde::Serialize + serde::de::DeserializeOwned,
{
    /// Recursively serialize a `BKNode` using [CBOR](https://en.wikipedia.org/wiki/CBOR),
    /// returning the resulting bytes as `Vec<u8>`
    pub fn to_vec(&self) -> Result<Vec<u8>, serde_cbor::error::Error> {
        Ok(serde_cbor::to_vec(self)?)
    }

    /// Deserialize a slice of `u8` into a returned `BKNode`
    pub fn from_slice<'a>(slice: &'a [u8]) -> Result<BKNode<K>, serde_cbor::error::Error> {
        let result: BKNode<K> = serde_cbor::from_slice(slice)?;
        Ok(result)
    }
}

impl<K> Debug for BKNode<K>
where
    K: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        f.debug_map().entry(&self.key, &self.children).finish()
    }
}

/// A representation of a [BK-tree](https://en.wikipedia.org/wiki/BK-tree).
#[derive(Debug)]
pub struct BKTree<K, M = metrics::Levenshtein> {
    /// The root node. May be empty if nothing has been put in the tree yet.
    pub root: Option<BKNode<K>>,
    /// The metric being used to determine the distance between nodes on the
    /// tree.
    metric: M,
}

impl<K, M> BKTree<K, M>
where
    M: Metric<K>,
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
    pub fn new(metric: M) -> BKTree<K, M> {
        BKTree { root: None, metric }
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
    /// case this searches for exact matches. The results are returned as an
    /// iterator of `(distance, key)` pairs.
    ///
    /// *Note:* There is no guarantee on the order of elements yielded by the
    /// iterator. The elements returned may or may not be sorted in terms of
    /// distance from the provided key.
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
    /// assert_eq!(tree.find("foo", 0).collect::<Vec<_>>(), vec![(0, &"foo")]);
    /// assert_eq!(tree.find("foo", 1).collect::<Vec<_>>(), vec![(0, &"foo"), (1, &"fop")]);
    /// assert!(tree.find("foz", 0).next().is_none());
    /// ```
    pub fn find<'a, 'q, Q: ?Sized>(&'a self, key: &'q Q, tolerance: u32) -> Find<'a, 'q, K, Q, M>
    where
        K: Borrow<Q>,
        M: Metric<Q>,
    {
        let candidates = if let Some(root) = &self.root {
            VecDeque::from(vec![root])
        } else {
            VecDeque::new()
        };
        Find {
            candidates,
            tolerance,
            metric: &self.metric,
            key,
        }
    }

    /// Searches for an exact match in the tree.
    ///
    /// This is equivalent to calling `find` with a tolerance of 0, then picking
    /// out the first result.
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
    /// assert_eq!(tree.find_exact("foo"), Some(&"foo"));
    /// ```
    pub fn find_exact<Q: ?Sized>(&self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        M: Metric<Q>,
    {
        self.find(key, 0).next().map(|(_, found_key)| found_key)
    }
}

impl<K, M: Metric<K>> Extend<K> for BKTree<K, M> {
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

/// Iterator for the results of `BKTree::find`.
pub struct Find<'a, 'q, K: 'a, Q: 'q + ?Sized, M: 'a> {
    /// Iterator stack. Because of the inversion of control in play, we must
    /// implement the traversal using an explicit stack.
    candidates: VecDeque<&'a BKNode<K>>,
    tolerance: u32,
    metric: &'a M,
    key: &'q Q,
}

impl<'a, 'q, K, Q: ?Sized, M> Iterator for Find<'a, 'q, K, Q, M>
where
    K: Borrow<Q>,
    M: Metric<Q>,
{
    type Item = (u32, &'a K);

    fn next(&mut self) -> Option<(u32, &'a K)> {
        while let Some(current) = self.candidates.pop_front() {
            let BKNode {
                key,
                children,
                max_child_distance,
            } = current;
            let distance_cutoff = max_child_distance.unwrap_or(0) + self.tolerance;
            let cur_dist = self.metric.threshold_distance(self.key,
                                                          current.key.borrow() as &Q,
                                                          distance_cutoff);
            if let Some(dist) = cur_dist {
                // Find the first child node within an appropriate distance
                let min_dist = dist.saturating_sub(self.tolerance);
                let max_dist = dist.saturating_add(self.tolerance);
                for (dist, child_node) in &mut children.iter() {
                    if min_dist <= *dist && *dist <= max_dist {
                        self.candidates.push_back(child_node);
                    }
                }
                // If this node is also close enough to the key, yield it
                if dist <= self.tolerance {
                    return Some((dist, &key));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;
    use {BKNode, BKTree};
    #[cfg(feature = "serde-support")]
    extern crate serde_cbor;

    fn assert_eq_sorted<'t, T: 't, I>(left: I, right: &[(u32, T)])
    where
        T: Ord + Debug,
        I: Iterator<Item = (u32, &'t T)>,
    {
        let mut left_mut: Vec<_> = left.collect();
        let mut right_mut: Vec<_> = right.iter().map(|&(dist, ref key)| (dist, key)).collect();

        left_mut.sort();
        right_mut.sort();

        assert_eq!(left_mut, right_mut);
    }


    #[cfg(feature = "serde-support")]
    fn assert_serde_roundtrip<K: serde::Serialize + serde::de::DeserializeOwned>(before: &BKNode<K>) {
        let bytes: Vec<u8> = before.to_vec().unwrap();
        assert!(bytes.len() > 0);
        let after: BKNode<K> = BKNode::from_slice(&bytes).unwrap();
        let bytes_after: Vec<u8> = after.to_vec().unwrap();
        assert_eq!(&bytes[..], &bytes_after[..]);
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
            }
            None => {
                assert!(false);
            }
        }
        tree.add("fop");
        tree.add("f\u{e9}\u{e9}");
        match tree.root {
            Some(ref root) => {
                assert_eq!(root.children.get(&1).unwrap().key, "fop");
                assert_eq!(root.children.get(&4).unwrap().key, "f\u{e9}\u{e9}");
            }
            None => {
                assert!(false);
            }
        }
    }

    #[test]
    fn tree_extend() {
        let mut tree: BKTree<&str> = Default::default();
        tree.extend(vec!["foo", "fop"]);
        match tree.root {
            Some(ref root) => {
                assert_eq!(root.key, "foo");
            }
            None => {
                assert!(false);
            }
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
        assert_eq_sorted(
            tree.find("book", 1),
            &[
                (0, "book"),
                (1, "books"),
                (1, "boo"),
                (1, "boon"),
                (1, "cook"),
            ],
        );
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

    #[cfg(feature = "serde-support")]
    #[test]
    fn tree_serde() {
        let mut tree: BKTree<String> = BKTree::default();
        tree.add("".to_string());
        assert_serde_roundtrip(&tree.root.unwrap());

        let mut tree: BKTree<String> = Default::default();
        tree.add("book".to_string());
        tree.add("books".to_string());
        tree.add("cake".to_string());
        tree.add("boo".to_string());
        tree.add("cape".to_string());
        tree.add("boon".to_string());
        tree.add("cook".to_string());
        tree.add("cart".to_string());
        let tree_root = tree.root.unwrap();
        assert_serde_roundtrip(&tree_root);

        let mut tree_same: BKTree<String> = Default::default();
        tree_same.add("book".to_string());
        tree_same.add("books".to_string());
        tree_same.add("cake".to_string());
        tree_same.add("boo".to_string());
        tree_same.add("cape".to_string());
        tree_same.add("boon".to_string());
        tree_same.add("cook".to_string());
        tree_same.add("cart".to_string());
        let tree_same_root = tree_same.root.unwrap();

        // Two trees built using the same operations should be the same.
        let bytes:      Vec<u8> = tree_root     .to_vec().unwrap();
        let bytes_same: Vec<u8> = tree_same_root.to_vec().unwrap();
        assert_eq!(bytes, bytes_same);

        // Ensure that we can use `serde_cbor` functions directly.
        let mut tree: BKTree<String> = Default::default();
        tree.add("cereal".to_string());
        let bytes = serde_cbor::to_vec(&tree.root.unwrap()).unwrap();
        let node: BKNode<String> = serde_cbor::from_slice(&bytes).unwrap();
        let mut new_tree: BKTree<String> = BKTree::default();
        new_tree.root = Some(node);
        assert_eq_sorted(new_tree.find("cereal", 0), &[(0, "cereal".to_string())]);

        // More tests?
        //   * Changing insertion order of the above 2nd tree _does_ change the result. We should be able to scramble
        //     the order of insertions for `tree_same` above and get the same serialization.
    }
}
