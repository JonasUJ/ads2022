//! Module that provides an n-ary heap.

use std::slice::Iter;

/// Simple n-ary heap.
pub struct NHeap<T: Ord> {
    n: usize,
    data: Vec<T>,
}

impl<T: Ord> NHeap<T> {
    /// Creates a new heap with the given width.
    ///
    /// # Arguments
    ///
    /// * `width` - width of the heap.
    pub fn new(width: usize) -> Self {
        if width == 0 {
            panic!("heap width must be more than 0");
        }

        NHeap {
            n: width,
            data: vec![],
        }
    }

    /// Creates a new heap from the passed elements and with the given width.
    ///
    /// # Arguments
    ///
    /// * `width` - width of the heap.
    /// * `elements` - all elements of the new heap.
    pub fn from(width: usize, elements: impl IntoIterator<Item = T>) -> Self {
        let mut heap = NHeap::new(width);
        heap.data = elements.into_iter().collect();
        heap.rebuild();
        heap
    }

    /// Get the width of the heap.
    pub fn width(&self) -> usize {
        self.n
    }

    /// Checks if the heap is empty.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Empties the heap.
    pub fn clear(&mut self) {
        self.data.clear()
    }

    /// Returns the length of the heap.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns an iterator over all heap elements in an arbirary order.
    pub fn iter(&self) -> Iter<T> {
        self.data.iter()
    }

    /// Insert a new item into the heap.
    pub fn push(&mut self, item: T) {
        self.data.push(item);
        self.sift_up(self.data.len() - 1);
    }

    /// Remove the maximal element from the heap and return it.
    pub fn pop(&mut self) -> Option<T> {
        if self.data.is_empty() {
            return None;
        }

        let res = self.data.swap_remove(0);
        self.sift_down(0);

        Some(res)
    }

    /// Peek at the top item in the heap.
    pub fn peek(&self) -> Option<&T> {
        if self.data.is_empty() {
            None
        } else {
            Some(&self.data[0])
        }
    }

    fn sift_up(&mut self, mut i: usize) {
        while i > 0 && self.data[i / self.n] < self.data[i] {
            self.data.swap(i / self.n, i);
            i /= self.n;
        }
    }

    fn sift_down(&mut self, mut i: usize) {
        while self.n * i < self.len() {
            let j = self.n * i;

            // Find max in all of node children
            let other = self.data[j..self.len().min(j + self.n)]
                .iter()
                .enumerate()
                .max_by(|(_, a), (_, b)| a.cmp(b))
                .map(|t| t.0);

            if other.is_none() {
                break;
            }

            let nj = j + other.unwrap();

            if self.data[i] >= self.data[nj] {
                break;
            }

            self.data.swap(i, nj);
            i = nj;
        }
    }

    fn rebuild(&mut self) {
        for i in (0..self.len() / 2).rev() {
            self.sift_down(i);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        NHeap::<u32>::new(2);
    }

    #[test]
    #[should_panic]
    fn new_panic() {
        NHeap::<u32>::new(0);
    }

    #[test]
    fn from() {
        let heap = NHeap::from(2, vec![1, 2, 3, 4, 3, 2, 1]);
        assert!(Iterator::eq(heap.iter(), vec![4, 3, 3, 2, 1, 2, 1].iter()));
    }

    #[test]
    fn from_empty() {
        let heap = NHeap::from(6, Vec::<i32>::new());
        assert!(heap.is_empty());
    }

    #[test]
    #[should_panic]
    fn from_panic() {
        NHeap::<u32>::from(0, vec![]);
    }

    #[test]
    fn width() {
        assert_eq!(NHeap::<u32>::new(2).width(), 2);
    }

    #[test]
    fn is_empty() {
        let mut heap = NHeap::<u32>::new(2);
        assert!(heap.is_empty());
        heap.push(1);
        assert!(!heap.is_empty());
    }

    #[test]
    fn clear() {
        let mut heap = NHeap::<u32>::new(2);
        heap.push(1);
        assert!(!heap.is_empty());
        heap.clear();
        assert!(heap.is_empty());
    }

    #[test]
    fn len() {
        let mut heap = NHeap::<u32>::new(2);
        assert_eq!(heap.len(), 0);
        heap.push(1);
        assert_eq!(heap.len(), 1);
        heap.push(1);
        assert_eq!(heap.len(), 2);
        heap.pop();
        assert_eq!(heap.len(), 1);
        heap.clear();
        assert_eq!(heap.len(), 0);
    }

    #[test]
    fn iter() {
        let heap = NHeap::from(
            4,
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 9, 8, 7, 6, 5, 4, 3, 2, 1],
        );

        let mut items = vec![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9];
        for n in heap.iter() {
            items.remove(items.iter().position(|i| i == n).unwrap());
        }
        assert!(items.is_empty());
    }

    #[test]
    fn push() {
        let mut heap = NHeap::<u32>::new(4);
        heap.push(1);
        heap.push(1);
        heap.push(1);
        heap.push(1);
        heap.push(2);
        assert_eq!(heap.len(), 5);
        assert_eq!(heap.peek(), Some(&2));
    }

    #[test]
    fn pop() {
        let mut heap = NHeap::from(3, vec![1, 2, 1, 3, 1, 4, 2, 3]);
        println!("{:?}", heap.data);
        assert_eq!(heap.pop(), Some(4));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn peek() {
        let mut heap = NHeap::from(
            4,
            vec![1, 5, 3, 8, 9, 3, 6, 9, 6, 2, 0, 5, 0, 0, 0, 5, 3, 1],
        );
        assert_eq!(heap.peek(), Some(&9));
        heap.clear();
        assert_eq!(heap.peek(), None);
    }
}
