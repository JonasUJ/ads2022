use super::{Sorter, Selection, SwapInsertion, Insertion, Shell, Merge, MergeFallback, IterativeMerge, Quick, QuickFallback};

macro_rules! test_sort {
    ($name:ident, $test:ident) => {
        #[test]
        fn $test() {
            let mut unsorted = super::read_test_file("./benches/sort/sort2k.txt");
            let mut sorted = unsorted.clone();
            sorted.sort_unstable();
            $name::sort(&mut unsorted);
            assert_eq!(unsorted, sorted);

            // Test not panicking
            let mut empty = [0usize; 0];
            $name::sort(&mut empty);
        }
    };
}

test_sort!(Selection, selection_sort);
test_sort!(SwapInsertion, swap_insertion_sort);
test_sort!(Insertion, insertion_sort);
test_sort!(Shell, shell_sort);
test_sort!(Merge, merge_sort);
test_sort!(MergeFallback, merge_fallback_sort);
test_sort!(IterativeMerge, iterative_merge_sort);
test_sort!(Quick, quick_sort);
test_sort!(QuickFallback, quick_fallback_sort);

#[test]
fn swap() {
    let mut v = vec![1, 2, 3, 4];
    unsafe {
        super::swap(&mut v, 1, 2);
    }
    assert_eq!(v, vec![1, 3, 2, 4]);
}

#[test]
fn min_index() {
    let v = vec![3, 4, 1, 2];
    let mut iter = v.iter();
    assert_eq!(super::min_index(&mut iter).unwrap(), (2usize, &1));
    let empty = Vec::<usize>::new();
    let mut iter = empty.iter();
    assert_eq!(super::min_index(&mut iter), None);
}

#[test]
fn max_index() {
    let v = vec![3, 4, 1, 2];
    let mut iter = v.iter();
    assert_eq!(super::max_index(&mut iter).unwrap(), (1usize, &4));
    let empty = Vec::<usize>::new();
    let mut iter = empty.iter();
    assert_eq!(super::max_index(&mut iter), None);
}

#[test]
fn merge() {
    let mut v = vec![3, 8, 8, 1, 2, 9];
    let (a, b) = v.split_at_mut(3);
    super::merge(a, b);
    assert_eq!(v, vec![1, 2, 3, 8, 8, 9]);
}

#[test]
fn partition() {
    let mut v = vec![3, 8, 3, 2, 1, 9 ,0, 3, 2, 5, 3, 2, 4];
    let p = super::partition(&mut v);
    assert_eq!(v, vec![2, 2, 3, 2, 1, 3, 0, 3, 3, 5, 9, 8, 4]);
    assert_eq!(v[p], 3);
}

#[test]
fn sort_test() {
    let mut v = vec![8, 8, 3, 2, 1, 9 ,0, 3, 2, 5, 3, 2, 4];
    let mut clone = v.clone();
    clone.sort_unstable();
    IterativeMerge::sort(&mut v);
    assert_eq!(clone, v);
}
