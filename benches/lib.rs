#![feature(test)] extern crate test;
extern crate bk_tree;
extern crate rand;

use bk_tree::BKTree;
use bk_tree::metrics::levenshtein;
use test::Bencher;
use rand::{thread_rng, Rng};

fn make_words<R: Rng>(rng: &mut R, n: i32) -> Vec<String> {
    let mut words: Vec<String> = Vec::new();
    for _ in 1..n {
        let l = rng.gen_range(4, 12);
        let s: String = rng.gen_ascii_chars().take(l).collect();
        words.push(s);
    }
    words
}

#[bench]
fn bench_find_exact(b: &mut Bencher) {
    let mut tree: BKTree<String> = BKTree::new(levenshtein);
    let words = make_words(&mut thread_rng(), 1000);
    tree.extend(words.clone());
    let word = words.last().unwrap();

    b.iter(move || {
        tree.find_exact(word.clone())
    });
}

#[bench]
fn bench_find_tol_one(b: &mut Bencher) {
    let mut tree: BKTree<String> = BKTree::new(levenshtein);
    let words = make_words(&mut thread_rng(), 1000);
    tree.extend(words.clone());
    let word = words.last().unwrap();

    b.iter(move || {
        tree.find(word.clone(), 1)
    });
}


#[bench]
fn bench_find_tol_two(b: &mut Bencher) {
    let mut tree: BKTree<String> = BKTree::new(levenshtein);
    let words = make_words(&mut thread_rng(), 1000);
    tree.extend(words.clone());
    let word = words.last().unwrap();

    b.iter(move || {
        tree.find(word.clone(), 2)
    });
}

#[bench]
fn bench_add(b: &mut Bencher) {
    let words = make_words(&mut thread_rng(), 1000);

    b.iter(move || {
        let mut tree: BKTree<String> = BKTree::new(levenshtein);
        for word in words.clone() {
            tree.add(word);
        }
    });
}

#[bench]
fn bench_extend(b: &mut Bencher) {
    let words = make_words(&mut thread_rng(), 1000);

    b.iter(move || {
        let mut tree: BKTree<String> = BKTree::new(levenshtein);
        tree.extend(words.clone());
    });
}
