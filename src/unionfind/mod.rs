//! This module provides a [`UnionFind`] struct that keeps track of connections in an undirected
//! graph.

/// Represents a node in the [`UnionFind`].
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct Site(pub usize);

/// A [`Site`] container that also stores a representation of their connections.
#[derive(Clone)]
pub struct UnionFind {
    count: usize,
    id: Vec<Site>,
    sz: Vec<usize>,
}

impl UnionFind {
    /// New [`UnionFind`] struct with given size.
    ///
    /// # Arguments
    ///
    /// * `count` - The number of initial component.
    pub fn new(count: usize) -> Self {
        UnionFind {
            count,
            id: (0..count).map(Site).collect(),
            sz: vec![1; count],
        }
    }

    /// The component the site belongs to. Returns [`None`] if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use ads2022::unionfind::{UnionFind, Site};
    /// let mut uf = UnionFind::new(5);
    /// let a = Site(0);
    /// let b = Site(2);
    /// let c = Site(4);
    ///
    /// assert_eq!(uf.find(a).unwrap(), a);
    /// uf.union(b, c);
    /// uf.union(a, c);
    /// assert_eq!(uf.find(a).unwrap(), b);
    /// ```
    pub fn find(&mut self, mut site: Site) -> Option<Site> {
        if site.0 >= self.id.len() {
            return None;
        }

        // SAFETY: Bounds check done above.
        unsafe {
            site = self.find_unchecked(site);
        }

        Some(site)
    }

    /// The component the site belongs to.
    ///
    /// # Safety
    ///
    /// `site` must be contained in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ads2022::unionfind::{UnionFind, Site};
    /// let mut uf = UnionFind::new(5);
    /// let a = Site(0);
    /// let b = Site(2);
    /// let c = Site(4);
    /// let d = Site(6);
    ///
    /// unsafe {
    ///     assert_eq!(uf.find_unchecked(a), a);
    ///     uf.union(b, c);
    ///     uf.union(a, c);
    ///     assert_eq!(uf.find_unchecked(a), b);
    ///     // UB
    ///     // assert_eq!(uf.find_unchecked(d), d);
    /// }
    /// ```
    pub unsafe fn find_unchecked(&mut self, mut site: Site) -> Site {
        while site != *self.id.get_unchecked(site.0) {
            std::intrinsics::assume(site.0 < self.id.len());
            self.id[site.0] = *self.id.get_unchecked(self.id[site.0].0);
            site = self.id[site.0];
        }

        site
    }

    /// Connect two sites.
    ///
    /// # Arguments
    ///
    /// * `a` - First site.
    /// * `b` - Second site.
    ///
    /// # Examples
    ///
    /// ```
    /// use ads2022::unionfind::{UnionFind, Site};
    /// let mut uf = UnionFind::new(5);
    /// let a = Site(0);
    /// let b = Site(2);
    ///
    /// assert!(!uf.connected(a, b));
    /// uf.union(a, b);
    /// assert!(uf.connected(a, b));
    /// ```
    pub fn union(&mut self, a: Site, b: Site) {
        let a = self.find(a);
        let b = self.find(b);

        if let (Some(a), Some(b)) = (a, b) {
            self.union_impl(a, b);
        }
    }

    /// Connect two sites.
    ///
    /// # Safety
    ///
    /// `a` and `b` must both lie within the bounds `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ads2022::unionfind::{UnionFind, Site};
    /// let mut uf = UnionFind::new(5);
    /// let a = Site(0);
    /// let b = Site(2);
    /// let c = Site(6);
    ///
    /// unsafe {
    ///     assert!(!uf.connected(a, b));
    ///     uf.union_unchecked(a, b);
    ///     assert!(uf.connected(a, b));
    ///     // UB
    ///     // uf.union_unchecked(a, c);
    /// }
    /// ```
    pub unsafe fn union_unchecked(&mut self, a: Site, b: Site) {
        let a = self.find_unchecked(a);
        let b = self.find_unchecked(b);
        self.union_impl(a, b);
    }

    fn union_impl(&mut self, a: Site, b: Site) {
        if a == b {
            return;
        }

        // SAFETY: Bounds checking done callers.
        unsafe {
            std::intrinsics::assume(
                self.sz.len() > a.0
                    && self.sz.len() > b.0
                    && self.id.len() > a.0
                    && self.id.len() > b.0,
            );
        }
        if self.sz[a.0] < self.sz[b.0] {
            self.id[a.0] = b;
            self.sz[b.0] += self.sz[a.0];
        } else {
            self.id[b.0] = a;
            self.sz[a.0] += self.sz[b.0];
        }
        self.count -= 1;
    }

    /// Tell whether two sites are part of the same component.
    /// This has side-effects resulting from the path compression of UnionFind::find.
    ///
    /// # Examples
    ///
    /// ```
    /// use ads2022::unionfind::{UnionFind, Site};
    /// let mut uf = UnionFind::new(5);
    /// let a = Site(0);
    /// let b = Site(2);
    /// let c = Site(4);
    ///
    /// // Not connected initially
    /// assert!(!uf.connected(a, b));
    ///
    /// uf.union(a, c);
    /// uf.union(b, c);
    /// assert!(uf.connected(a, b));
    /// ```
    pub fn connected(&mut self, a: Site, b: Site) -> bool {
        self.find(a) == self.find(b)
    }

    /// The number of components.
    ///
    /// # Examples
    ///
    /// ```
    /// use ads2022::unionfind::{UnionFind, Site};
    /// let mut uf = UnionFind::new(5);
    ///
    /// // No unions - all sites are components.
    /// assert_eq!(uf.count(), 5);
    ///
    /// uf.union(Site(1), Site(3));
    /// uf.union(Site(2), Site(3));
    /// assert_eq!(uf.count(), 3);
    /// ```
    pub fn count(&self) -> usize {
        self.count
    }
}

#[cfg(any(test, feature = "bench"))]
macro_rules! bounds_checked_find {
    ($name:ident, $self:ident, $site:ident, $body:block) => {
        #[inline]
        pub fn $name(&mut $self, mut $site: Site) -> Option<Site> {
            if $site.0 >= $self.id.len() {
                return None;
            }
            $site = $body;
            Some($site)
        }
    }
}

#[allow(missing_docs)]
#[cfg(any(test, feature = "bench"))]
impl UnionFind {
    pub fn union_generic<F>(&mut self, a: Site, b: Site, find: F)
    where
        F: Fn(&mut UnionFind, Site) -> Option<Site>,
    {
        let a = find(self, a);
        let b = find(self, b);

        if let (Some(a), Some(b)) = (a, b) {
            self.union_impl(a, b);
        }
    }

    bounds_checked_find!(find_plain, self, site, {
        unsafe {
            while site != *self.id.get_unchecked(site.0) {
                site = *self.id.get_unchecked(site.0);
            }
        }
        site
    });

    bounds_checked_find!(find_plain_safe, self, site, {
        while site != self.id[site.0] {
            site = self.id[site.0];
        }
        site
    });

    bounds_checked_find!(find_compress_one, self, site, {
        unsafe {
            while site != *self.id.get_unchecked(site.0) {
                std::intrinsics::assume(site.0 < self.id.len());
                self.id[site.0] = *self.id.get_unchecked(self.id[site.0].0);
                site = self.id[site.0];
            }
        }
        site
    });

    bounds_checked_find!(find_compress_one_safe, self, site, {
        while site != self.id[site.0] {
            self.id[site.0] = self.id[self.id[site.0].0];
            site = self.id[site.0];
        }
        site
    });

    bounds_checked_find!(find_compress_one_do_while, self, site, {
        unsafe {
            while {
                std::intrinsics::assume(site.0 < self.id.len());
                self.id[site.0] = *self.id.get_unchecked(self.id[site.0].0);
                site = self.id[site.0];
                site != *self.id.get_unchecked(site.0)
            } {}
        }

        site
    });

    bounds_checked_find!(find_compress_one_do_while_safe, self, site, {
        while {
            self.id[site.0] = self.id[self.id[site.0].0];
            site = self.id[site.0];
            site != self.id[site.0]
        } {}

        site
    });

    bounds_checked_find!(find_compress, self, site, {
        let mut seen: [Site; 8] = [Site(0); 8];
        let mut i: usize = 0;
        unsafe {
            while site != self.id[site.0] {
                seen[i & 7] = self.id[site.0];
                site = self.id[site.0];
                std::intrinsics::assume(site.0 < self.id.len());
                i += 1;
            }
            i = std::cmp::min(i, seen.len());
            for j in 0..i {
                let child = *seen.get_unchecked(j);
                std::intrinsics::assume(child.0 < self.id.len());
                self.id[child.0] = site;
            }
        }
        site
    });

    bounds_checked_find!(find_compress_safe, self, site, {
        let mut seen: [Site; 8] = [Site(0); 8];
        let mut i: usize = 0;
        while site != self.id[site.0] {
            seen[i & 7] = self.id[site.0];
            site = self.id[site.0];
            i += 1;
        }
        i = std::cmp::min(i, seen.len());
        for child in seen.iter().take(i) {
            self.id[child.0] = site;
        }
        site
    });
}

#[allow(missing_docs)]
#[cfg(any(test, feature = "bench"))]
pub fn read_test_file(filename: &str) -> (UnionFind, Vec<(Site, Site)>) {
    use std::fs;
    let string_content = fs::read_to_string(filename).unwrap();
    let mut content = string_content.trim().split('\n');
    let count = content.next().unwrap().parse::<usize>().unwrap();
    (
        UnionFind::new(count),
        content
            .map(|l| {
                l.split_ascii_whitespace()
                    .map(|n| n.parse::<usize>().unwrap())
                    .collect::<Vec<usize>>()
            })
            .map(|p| (Site(p[0]), Site(p[1])))
            .collect(),
    )
}

#[cfg(test)]
mod tests;
