#![feature(test)]
extern crate bk_tree;
extern crate rand;
extern crate test;

use bk_tree::metrics::Levenshtein;
use bk_tree::BKTree;
use rand::{distributions::Alphanumeric, thread_rng, Rng};
use test::Bencher;

fn make_words<R: Rng>(rng: &mut R, n: i32) -> Vec<String> {
    let mut words: Vec<String> = Vec::new();
    for _ in 1..n {
        let l = rng.gen_range(4..12);
        let s: String = rng
            .sample_iter(Alphanumeric)
            .map(|c| c as char)
            .take(l)
            .collect();
        words.push(s);
    }
    words
}

#[bench]
fn bench_find_exact(b: &mut Bencher) {
    let mut tree: BKTree<String> = BKTree::new(Levenshtein);
    let words = make_words(&mut thread_rng(), 1000);
    let word = words.last().unwrap().clone();
    tree.extend(words);

    b.iter(|| tree.find_exact(&word));
}

#[bench]
fn bench_find_tol_one(b: &mut Bencher) {
    let mut tree: BKTree<String> = BKTree::new(Levenshtein);
    let words = make_words(&mut thread_rng(), 1000);
    let word = words.last().unwrap().clone();
    tree.extend(words);

    b.iter(|| tree.find(&word, 1));
}

#[bench]
fn bench_find_tol_two(b: &mut Bencher) {
    let mut tree: BKTree<String> = BKTree::new(Levenshtein);
    let words = make_words(&mut thread_rng(), 1000);
    let word = words.last().unwrap().clone();
    tree.extend(words);

    b.iter(|| tree.find(&word, 2));
}

#[bench]
fn bench_add(b: &mut Bencher) {
    let words = make_words(&mut thread_rng(), 1000);

    b.iter(move || {
        let mut tree: BKTree<String> = BKTree::new(Levenshtein);
        for word in words.clone() {
            tree.add(word);
        }
    });
}

#[bench]
fn bench_extend(b: &mut Bencher) {
    let words = make_words(&mut thread_rng(), 1000);

    b.iter(move || {
        let mut tree: BKTree<String> = BKTree::new(Levenshtein);
        tree.extend(words.clone());
    });
}
