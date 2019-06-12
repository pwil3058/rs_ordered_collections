//Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.

///! Iterators over the output of pairs of ordered Iterators applying
///! various filters. If the Iterators contain no duplicates as well
///! as bing sorted then the filter will produce set operations.
use std::cmp::Ordering;

use crate::ordered_map::OrderedMap;
use crate::ordered_set::OrderedSet;

/// Return true if the data stream from the Iterator is ordered and
/// contains no duplicates.  Useful for testing.
pub fn output_is_ordered_nodups<'a, T, I>(iter: &mut I) -> bool
where
    T: 'a + Ord,
    I: Iterator<Item = &'a T>,
{
    let mut o_previous = iter.next();
    while let Some(previous) = o_previous {
        if let Some(item) = iter.next() {
            if previous >= item {
                return false;
            }
            o_previous = Some(item);
        } else {
            o_previous = None;
        }
    }
    true
}

macro_rules! define_set_operation {
    ( $doc:meta, $iter:ident ) => {
        pub struct $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: Iterator<Item = &'a T>,
            R: Iterator<Item = &'a T>,
        {
            l_item: Option<L::Item>,
            r_item: Option<R::Item>,
            l_iter: L,
            r_iter: R,
        }

        impl<'a, T, L, R> $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: Iterator<Item = &'a T>,
            R: Iterator<Item = &'a T>,
        {
            pub fn new(mut l_iter: L, mut r_iter: R) -> Self {
                Self {
                    l_item: l_iter.next(),
                    r_item: r_iter.next(),
                    l_iter: l_iter,
                    r_iter: r_iter,
                }
            }
        }

        impl<'a, T, L, R> IterSetOperations<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: Iterator<Item = &'a T>,
            R: Iterator<Item = &'a T>,
        {
        }

        impl<'a, T, L, R> SetConversion<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord + Clone,
            L: Iterator<Item = &'a T>,
            R: Iterator<Item = &'a T>,
        {
        }
    };
}

define_set_operation!(
    doc = "An ordered Iterator over the set union of the output of two Iterators whose
(individual) output is ordered and contains no duplicates.",
    Union
);

impl<'a, T, L, R> Iterator for Union<'a, T, L, R>
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_item {
                if let Some(r_item) = self.r_item {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_item = self.l_iter.next();
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_item = self.r_iter.next();
                            return Some(r_item);
                        }
                        Ordering::Equal => {
                            self.l_item = self.l_iter.next();
                            self.r_item = self.r_iter.next();
                            return Some(l_item);
                        }
                    }
                } else {
                    self.l_item = self.l_iter.next();
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_item {
                self.r_item = self.r_iter.next();
                return Some(r_item);
            } else {
                return None;
            }
        }
    }
}

define_set_operation!(
    doc = "An ordered Iterator over the set intersection of the output of two Iterators whose
(individual) output is ordered and contains no duplicates.",
    Intersection
);

impl<'a, T, L, R> Iterator for Intersection<'a, T, L, R>
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_item {
                if let Some(r_item) = self.r_item {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_item = self.l_iter.next();
                        }
                        Ordering::Greater => {
                            self.r_item = self.r_iter.next();
                        }
                        Ordering::Equal => {
                            self.l_item = self.l_iter.next();
                            self.r_item = self.r_iter.next();
                            return Some(l_item);
                        }
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }
}

define_set_operation!(
    doc = "An ordered Iterator over the set difference between the output of two
Iterators whose (individual) output is ordered and contains no duplicates.",
    Difference
);

impl<'a, T, L, R> Iterator for Difference<'a, T, L, R>
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_item {
                if let Some(r_item) = self.r_item {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_item = self.l_iter.next();
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_item = self.r_iter.next();
                        }
                        Ordering::Equal => {
                            self.l_item = self.l_iter.next();
                            self.r_item = self.r_iter.next();
                        }
                    }
                } else {
                    self.l_item = self.l_iter.next();
                    return Some(l_item);
                }
            } else {
                return None;
            }
        }
    }
}

define_set_operation!(
    doc = "An ordered Iterator over the symmetric set difference between the output of two
Iterators whose (individual) output is ordered and contains no duplicates.",
    SymmetricDifference
);

impl<'a, T, L, R> Iterator for SymmetricDifference<'a, T, L, R>
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_item {
                if let Some(r_item) = self.r_item {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_item = self.l_iter.next();
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_item = self.r_iter.next();
                            return Some(r_item);
                        }
                        Ordering::Equal => {
                            self.l_item = self.l_iter.next();
                            self.r_item = self.r_iter.next();
                        }
                    }
                } else {
                    self.l_item = self.l_iter.next();
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_item {
                self.r_item = self.r_iter.next();
                return Some(r_item);
            } else {
                return None;
            }
        }
    }
}

pub trait IterSetOperations<'a, T>: Iterator<Item = &'a T> + Sized
where
    T: 'a + Ord,
{
    fn osi_union<I: Iterator<Item = &'a T>>(self, iter: I) -> Union<'a, T, Self, I> {
        Union::new(self, iter)
    }

    fn osi_intersection<I: Iterator<Item = &'a T>>(self, iter: I) -> Intersection<'a, T, Self, I> {
        Intersection::new(self, iter)
    }

    fn osi_difference<I: Iterator<Item = &'a T>>(self, iter: I) -> Difference<'a, T, Self, I> {
        Difference::new(self, iter)
    }

    fn osi_symmetric_difference<I: Iterator<Item = &'a T>>(
        self,
        iter: I,
    ) -> SymmetricDifference<'a, T, Self, I> {
        SymmetricDifference::new(self, iter)
    }
}

pub trait SetConversion<'a, T>: Iterator<Item = &'a T>
where
    T: 'a + Ord + Clone,
{
    /// Create a OrderedSet<T> from the items in the Iterator's output
    fn to_set(&mut self) -> OrderedSet<T> {
        let ordered_list: Vec<T> = self.cloned().collect();
        OrderedSet::<T>::from(ordered_list)
    }
}

// Set Iterator
pub struct SetIter<'a, T, I>
where
    T: 'a + Ord,
    I: Iterator<Item = &'a T>,
{
    iter: I,
}

impl<'a, T, I> SetIter<'a, T, I>
where
    T: 'a + Ord,
    I: Iterator<Item = &'a T>,
{
    pub fn new(iter: I) -> Self {
        Self { iter: iter }
    }
}

impl<'a, T, I> Iterator for SetIter<'a, T, I>
where
    T: 'a + Ord,
    I: Iterator<Item = &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T, I> IterSetOperations<'a, T> for SetIter<'a, T, I>
where
    T: 'a + Ord,
    I: Iterator<Item = &'a T>,
{
}

impl<'a, T, I> SetConversion<'a, T> for SetIter<'a, T, I>
where
    T: 'a + Ord + Clone,
    I: Iterator<Item = &'a T>,
{
}

// MAP ITERATION CODE

pub trait MapConversion<'a, K, V>: Iterator<Item = &'a (K, V)>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    /// Create a OrderedSet<T> from the items in the Iterator's output
    fn to_map(&mut self) -> OrderedMap<K, V> {
        let ordered_list: Vec<(K, V)> = self.cloned().collect();
        OrderedMap::<K, V>::from(ordered_list)
    }
}

// Map Iterator
pub struct MapIter<'a, K, V, I>
where
    K: 'a + Ord,
    V: 'a,
    I: Iterator<Item = &'a (K, V)>,
{
    iter: I,
}

impl<'a, K, V, I> MapIter<'a, K, V, I>
where
    K: 'a + Ord,
    V: 'a,
    I: Iterator<Item = &'a (K, V)>,
{
    pub fn new(iter: I) -> Self {
        Self { iter: iter }
    }
}

impl<'a, K, V, I> Iterator for MapIter<'a, K, V, I>
where
    K: 'a + Ord,
    V: 'a,
    I: Iterator<Item = &'a (K, V)>,
{
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, K, V, I> MapConversion<'a, K, V> for MapIter<'a, K, V, I>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    I: Iterator<Item = &'a (K, V)>,
{
}

// Map Merge Iterator
/// Ordered Iterator over the merged output of two disjoint map Iterators.
pub struct MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: Iterator<Item = &'a (K, V)>,
    R: Iterator<Item = &'a (K, V)>,
{
    l_item: Option<L::Item>,
    r_item: Option<R::Item>,
    l_iter: L,
    r_iter: R,
}

impl<'a, K, V, L, R> MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: Iterator<Item = &'a (K, V)>,
    R: Iterator<Item = &'a (K, V)>,
{
    pub fn new(mut l_iter: L, mut r_iter: R) -> Self {
        Self {
            l_item: l_iter.next(),
            r_item: r_iter.next(),
            l_iter: l_iter,
            r_iter: r_iter,
        }
    }
}

impl<'a, K, V, L, R> Iterator for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: Iterator<Item = &'a (K, V)>,
    R: Iterator<Item = &'a (K, V)>,
{
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_item {
                if let Some(r_item) = self.r_item {
                    match l_item.0.cmp(&r_item.0) {
                        Ordering::Less => {
                            self.l_item = self.l_iter.next();
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_item = self.r_iter.next();
                            return Some(r_item);
                        }
                        Ordering::Equal => {
                            panic!("merged map Iterators are not disjoint");
                        }
                    }
                } else {
                    self.l_item = self.l_iter.next();
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_item {
                self.r_item = self.r_iter.next();
                return Some(r_item);
            } else {
                return None;
            }
        }
    }
}

impl<'a, K, V, L, R> MapConversion<'a, K, V> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: Iterator<Item = &'a (K, V)>,
    R: Iterator<Item = &'a (K, V)>,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    static LIST_0: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static LIST_1: &[&str] = &["b", "d", "f", "h", "i", "k", "m"];
    static LIST_2: &[&str] = &[
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
    ];
    static LIST_UNORDERED: &[&str] = &["a", "c", "e", "z", "g", "i", "k", "m"];

    #[test]
    fn output_is_ordered_nodups_works() {
        assert!(output_is_ordered_nodups(&mut LIST_0.iter()));
        assert!(!output_is_ordered_nodups(&mut LIST_0.iter().rev()));
        assert!(!output_is_ordered_nodups(&mut LIST_UNORDERED.iter()));
        assert!(!output_is_ordered_nodups(&mut LIST_UNORDERED.iter().rev()));
    }

    #[test]
    fn union_works() {
        let mut test_iter = Union::new(LIST_0[..3].iter(), LIST_1[..2].iter());
        assert_eq!(test_iter.next(), Some(&"a"));
        let result: Vec<&str> = Union::new(LIST_0[..3].iter(), LIST_1[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "b", "c", "d", "e"]);
        let result: Vec<&str> = Union::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "b", "c", "e"]);
        let result: Vec<&str> = Union::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "c", "d", "e", "f"]);
        let set = Union::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["a", "c", "d", "e", "f"]);
    }

    #[test]
    fn intersection_works() {
        let mut test_iter = Intersection::new(LIST_0[..3].iter(), LIST_1[..2].iter());
        assert_eq!(test_iter.next(), None);
        let result: Vec<&str> = Intersection::new(LIST_0[..3].iter(), LIST_1[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, Vec::<&str>::new());
        let result: Vec<&str> = Intersection::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a"]);
        let result: Vec<&str> = Intersection::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "b", "d", "f"]);
        let set = Intersection::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["a", "b", "d", "f"]);
    }

    #[test]
    fn difference() {
        let mut test_iter = Difference::new(LIST_0[..1].iter(), LIST_0[..1].iter());
        assert_eq!(test_iter.next(), None);
        let mut test_iter = Difference::new(LIST_0[..3].iter(), LIST_1[..2].iter());
        assert_eq!(test_iter.next(), Some(&"a"));
        let result: Vec<&str> = Difference::new(LIST_0[..3].iter(), LIST_1[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "c", "e"]);
        let result: Vec<&str> = Difference::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["c", "e"]);
        let result: Vec<&str> = Difference::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["b", "c", "d", "e", "f"]);
        let set = Difference::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["b", "c", "d", "e", "f"]);
    }

    #[test]
    fn symmetric_difference_works() {
        let mut test_iter = SymmetricDifference::new(LIST_0[..3].iter(), LIST_1[..2].iter());
        assert_eq!(test_iter.next(), Some(&"a"));
        let result: Vec<&str> = SymmetricDifference::new(LIST_0[..3].iter(), LIST_1[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "b", "c", "d", "e"]);
        let result: Vec<&str> = SymmetricDifference::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["b", "c", "e"]);
        let result: Vec<&str> = SymmetricDifference::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["c", "d", "e", "f"]);
        let set = SymmetricDifference::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .symmetric_difference(LIST_1[..3].iter())
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["c", "d", "e", "f"]);
    }
}
