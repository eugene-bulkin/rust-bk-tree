//! This is a collection of string metrics that are suitable for use with a
//! BK-tree.


use std::cmp::min;

use Metric;

/// This calculates the Levenshtein distance between two strings.
///
/// The [distance metric itself][1] is calculated using the [Wagner-Fischer][2]
/// dynamic programming algorithm.
///
/// # Examples
///
/// ```
/// use bk_tree::Metric;
/// use bk_tree::metrics::Levenshtein;
///
/// assert_eq!(Levenshtein.distance("bar", "baz"), 1);
/// assert_eq!(Levenshtein.distance("kitten", "sitting"), 3);
/// ```
///
/// [1]: https://en.wikipedia.org/wiki/Levenshtein_distance
/// [2]: https://en.wikipedia.org/wiki/Wagner%E2%80%93Fischer_algorithm
pub struct Levenshtein;

impl<K: AsRef<str> + ?Sized> Metric<K> for Levenshtein
{
    fn distance(&self, a: &K, b: &K) -> u64 {
        let str_a: &str = a.as_ref();
        let str_b: &str = b.as_ref();

        let len_a: u64 = str_a.chars().collect::<Vec<char>>().len() as u64;
        let len_b: u64 = str_b.chars().collect::<Vec<char>>().len() as u64;
        if len_a == 0 {
            return len_b;
        }
        if len_b == 0 {
            return len_a;
        }

        // This is a case-insensitive algorithm
        let a_lower = str_a.to_lowercase();
        let b_lower = str_b.to_lowercase();

        // Initialize the array
        let mut d: Vec<Vec<u64>> = Vec::new();
        for j in 0..(len_b + 1) {
            let mut cur_vec = Vec::new();
            for i in 0..(len_a + 1) {
                if j == 0 {
                    cur_vec.push(i);
                } else if i == 0 {
                    cur_vec.push(j);
                } else {
                    cur_vec.push(0);
                }
            }
            d.push(cur_vec);
        }

        for j in 0..len_b as usize {
            for i in 0..len_a as usize {
                let chr_a = a_lower.chars().nth(i).unwrap();
                let chr_b = b_lower.chars().nth(j).unwrap();
                if chr_a == chr_b {
                    // If they're the same, then don't modify the value
                    d[j + 1][i + 1] = d[j][i];
                } else {
                    // Otherwise, pick the lowest cost option for an error
                    let deletion = d[j + 1][i] + 1;
                    let insertion = d[j][i + 1] + 1;
                    let substitution = d[j][i] + 1;
                    d[j + 1][i + 1] = min(min(deletion, insertion), substitution);
                }
            }
        }

        d[len_b as usize][len_a as usize]
    }
}
