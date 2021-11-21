//! This module provides a handful of [`Sorter`]s and sorting related functions.

use std::ptr;

/// Trait for types that can sort slices in place.
pub trait Sorter<T> {
    /// Sorts `s` in place.
    fn sort(s: &mut [T]);
}

/// [`Sorter`] that implements selectionsort.
pub struct Selection;

impl<T> Sorter<T> for Selection
where
    T: Ord,
{
    fn sort(s: &mut [T]) {
        for i in 0..s.len() {
            let mut rest = s[i..].iter();
            let mi = min_index(&mut rest).unwrap().0;
            // SAFETY: `0 <= i < v.len()` and the range of `mi` shrinks at the same rate as `i` grows,
            // hence `0 <= mi + i < v.len()`
            unsafe {
                swap(s, i, mi + i);
            }
        }
    }
}

/// [`Sorter`] that implements insertionsort, but with far more swaps.
pub struct SwapInsertion;

impl<T> Sorter<T> for SwapInsertion
where
    T: Ord,
{
    fn sort(s: &mut [T]) {
        for mut i in 1..s.len() {
            while i > 0 && s[i] < s[i - 1] {
                // SAFETY: `0 < i < v.len()`
                unsafe {
                    swap(s, i, i - 1);
                }
                i -= 1;
            }
        }
    }
}

/// [`Sorter`] that implements insertionsort.
pub struct Insertion;

impl<T> Sorter<T> for Insertion
where
    T: Ord,
{
    fn sort(s: &mut [T]) {
        for mut i in 1..s.len() {
            let sorted = i;
            let elem = &s[i];
            while i > 0 && &s[i - 1] > elem {
                i -= 1;
            }
            s[i..=sorted].rotate_right(1);
        }
    }
}

/// [`Sorter`] that implements shellsort.
pub struct Shell;

impl<T> Sorter<T> for Shell
where
    T: Ord,
{
    fn sort(s: &mut [T]) {
        let mut h = 1;
        while h < s.len() / 3 {
            h = 3 * h + 1;
        }
        while h > 0 {
            for mut i in h..s.len() {
                while i >= h && s[i] < s[i - h] {
                    // SAFETY: `0 < h <= i < v.len()`
                    unsafe {
                        swap(s, i, i - h);
                    }
                    i -= 1;
                }
            }
            h /= 3;
        }
    }
}

/// [`Sorter`] that implements mergesort.
pub struct Merge;

impl<T> Sorter<T> for Merge
where
    T: Ord + Copy,
{
    fn sort(s: &mut [T]) {
        if s.len() <= 1 {
            return;
        }
        let mid = s.len() / 2;
        let (left, right) = s.split_at_mut(mid);
        Merge::sort(left);
        Merge::sort(right);
        merge(left, right);
    }
}

/// [`Sorter`] that implements mergesort and falls back to [`Insertion`] sort at a certain
/// threshold.
pub struct MergeFallback;

impl<T> Sorter<T> for MergeFallback
where
    T: Ord + Copy,
{
    fn sort(s: &mut [T]) {
        if s.len() <= 12 {
            Insertion::sort(s);
            return;
        }
        let mid = s.len() / 2;
        let (left, right) = s.split_at_mut(mid);
        Merge::sort(left);
        Merge::sort(right);
        merge(left, right);
    }
}

/// [`Sorter`] that implements mergesort in a nonrecursive manner.
pub struct IterativeMerge;

impl<T> Sorter<T> for IterativeMerge
where
    T: Ord + Copy,
{
    fn sort(s: &mut [T]) {
        let len = s.len();
        for size in (1..).map(|n| 1 << n).take_while(|n| n < &(len * 2)) {
            for index in (0..s.len()).step_by(size) {
                let sub = &mut s[index..(index + size).min(len)];
                let (left, right) = sub.split_at_mut((size / 2).min(sub.len()));
                merge(left, right);
            }
        }
    }
}

/// [`Sorter`] that implements quicksort.
pub struct Quick;

impl<T> Sorter<T> for Quick
where
    T: Ord,
{
    fn sort(s: &mut [T]) {
        if s.len() <= 1 {
            return;
        }
        let p = partition(s);
        let (left, right) = s.split_at_mut(p);
        Quick::sort(left);
        Quick::sort(&mut right[1..]);
    }
}

/// [`Sorter`] that implements quicksort and falls back to [`Insertion`] sort at a certain
/// threshold.
pub struct QuickFallback;

impl<T> Sorter<T> for QuickFallback
where
    T: Ord,
{
    fn sort(s: &mut [T]) {
        if s.len() <= 32 {
            Insertion::sort(s);
            return;
        }
        let p = partition(s);
        let (left, right) = s.split_at_mut(p);
        Quick::sort(left);
        Quick::sort(&mut right[1..]);
    }
}

/// Unchecked swap of two elements in a `[T]`.
///
/// # Safety
///
/// `a` and `b` must lie within `s`.
#[inline]
pub unsafe fn swap<T>(s: &mut [T], a: usize, b: usize) {
    std::intrinsics::assume(a < s.len() && b < s.len());
    let pa = ptr::addr_of_mut!(s[a]);
    let pb = ptr::addr_of_mut!(s[b]);
    ptr::swap(pa, pb);
}

/// Returns the minimum value and its index from an iterator.
/// Returns None if the iterator is empty.
pub fn min_index<I, T>(iter: &mut I) -> Option<(usize, T)>
where
    I: Iterator<Item = T>,
    T: Ord,
{
    iter.enumerate().min_by(|(_, a), (_, b)| a.cmp(b))
}

/// Returns the maximum value and its index from an iterator.
/// Returns None if the iterator is empty.
pub fn max_index<I, T>(iter: &mut I) -> Option<(usize, T)>
where
    I: Iterator<Item = T>,
    T: Ord,
{
    iter.enumerate().max_by(|(_, a), (_, b)| a.cmp(b))
}

/// Merges two sorted slices in place, moving elements between the slices.
///
/// Lower elements will be placed in `a`, while greater elements are placed in `b`.
#[allow(clippy::uninit_vec)]
pub fn merge<T>(a: &mut [T], b: &mut [T])
where
    T: Ord + Copy,
{
    // Stop early
    if let (Some(al), Some(bf)) = (a.last(), b.first()) {
        if al <= bf {
            return;
        }
    }

    let mut ac = 0;
    let mut bc = 0;

    let cap = a.len() + b.len();
    // TODO: Move into Merge struct (but it ruins `merge` as a standalone function :C)
    let mut scratch = Vec::<T>::with_capacity(cap);
    // SAFETY: new len is equal to capacity and elements are initialized before any accesses.
    unsafe { scratch.set_len(scratch.capacity()) }

    let (acopy, bcopy) = scratch.split_at_mut(a.len());

    // TODO: Figure out how to use copy_nonoverlapping to avoid T: Copy
    acopy.copy_from_slice(a);
    bcopy.copy_from_slice(b);

    for i in 0..cap {
        let tmp = if bc >= b.len() {
            ac += 1;
            acopy[ac - 1]
        } else if ac >= a.len() {
            bc += 1;
            bcopy[bc - 1]
        } else if acopy[ac] < bcopy[bc] {
            ac += 1;
            acopy[ac - 1]
        } else {
            bc += 1;
            bcopy[bc - 1]
        };
        if i < a.len() {
            a[i] = tmp;
        } else {
            b[i - a.len()] = tmp;
        }
    }
}

/// Partitions `s` around a pivot, which is its first element.
///
/// After this operation, all elements less than the pivot will appear in `s` before any element
/// greater than or equal to the pivot.
pub fn partition<T>(s: &mut [T]) -> usize
where
    T: Ord,
{
    if s.is_empty() {
        return 0;
    } else if s.len() == 2 {
        if s[0] > s[1] {
            // SAFETY: We just checked bounds.
            unsafe { swap(s, 0, 1) }
        }
        return 1;
    }
    let (pivot, r) = s.split_first_mut().unwrap();
    let mut front = 0;
    let mut back = r.len() - 1;
    while front <= back && back > 0 {
        if &r[front] <= pivot {
            front += 1;
        } else if &r[back] > pivot {
            back -= 1;
        } else {
            // SAFETY: `front` and `back` approach the middle of the slice and will never be out of
            // bounds.
            unsafe {
                swap(r, front, back);
            }
            front += 1;
            back -= 1;
        }
    }
    // SAFETY: `front` is in the slice and the slice is not empty.
    unsafe {
        swap(s, 0, front);
    }
    front
}

#[allow(missing_docs)]
#[cfg(any(test, feature = "bench"))]
pub fn read_test_file(filename: &str) -> Vec<usize> {
    std::fs::read_to_string(filename)
        .unwrap()
        .trim()
        .split('\n')
        .map(|n| n.parse::<usize>().unwrap())
        .collect()
}

#[cfg(test)]
mod tests;
