///! Iterators over the output of pairs of ordered Iterators applying
///! various filters. If the Iterators contain no duplicates as well
///! as being sorted then the filter will produce set operations.
use std::cmp::Ordering;
use std::marker::PhantomData;

use crate::ordered_iterators::*;

use crate::SkipAheadIterator;

pub trait IterSetOperations<'a, T>: SkipAheadIterator<'a, T, &'a T> + Sized
where
    T: 'a + Ord,
{
    /// Iterate over the set union of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn union<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> Union<'a, T, Self, I> {
        Union::new(self, iter)
    }

    /// Iterate over the set intersection of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn intersection<I: SkipAheadIterator<'a, T, &'a T>>(
        self,
        iter: I,
    ) -> Intersection<'a, T, Self, I> {
        Intersection::new(self, iter)
    }

    /// Iterate over the set difference of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn difference<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> Difference<'a, T, Self, I> {
        Difference::new(self, iter)
    }

    /// Iterate over the set symmetric difference of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn symmetric_difference<I: SkipAheadIterator<'a, T, &'a T>>(
        self,
        iter: I,
    ) -> SymmetricDifference<'a, T, Self, I> {
        SymmetricDifference::new(self, iter)
    }

    /// Is the output of the given Iterator disjoint from the output of
    /// this iterator?
    fn is_disjoint<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> bool {
        are_disjoint(self, iter)
    }

    /// Is the output of the given Iterator a proper subset of the output of
    /// this iterator?
    fn is_proper_subset<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> bool {
        a_proper_superset_b(self, iter)
    }

    /// Is the output of the given Iterator a proper superset of the output of
    /// this iterator?
    fn is_proper_superset<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> bool {
        a_proper_superset_b(iter, self)
    }

    /// Is the output of the given Iterator a subset of the output of
    /// this iterator?
    fn is_subset<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> bool {
        a_superset_b(self, iter)
    }

    /// Is the output of the given Iterator a superset of the output of
    /// this iterator?
    fn is_superset<I: SkipAheadIterator<'a, T, &'a T>>(self, iter: I) -> bool {
        a_superset_b(iter, self)
    }
}

/// The contents of the two iterators are disjoint
pub fn are_disjoint<'a, T, L, R>(mut l_iter: L, mut r_iter: R) -> bool
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    let mut o_l_item = l_iter.next();
    let mut o_r_item = r_iter.next();

    loop {
        if let Some(l_item) = o_l_item {
            if let Some(r_item) = o_r_item {
                match l_item.cmp(&r_item) {
                    Ordering::Less => {
                        o_l_item = l_iter.next_from(r_item);
                    }
                    Ordering::Greater => {
                        o_r_item = r_iter.next_from(l_item);
                    }
                    Ordering::Equal => {
                        return false;
                    }
                }
            } else {
                return true;
            }
        } else {
            return true;
        }
    }
}

/// The contents of Iterator "a" are a superset of the contents of "b"
pub fn a_superset_b<'a, T, A, B>(mut a_iter: A, mut b_iter: B) -> bool
where
    T: 'a + Ord,
    A: SkipAheadIterator<'a, T, &'a T>,
    B: SkipAheadIterator<'a, T, &'a T>,
{
    let mut o_a_item = a_iter.next();
    let mut o_b_item = b_iter.next();

    while let Some(b_item) = o_b_item {
        if let Some(a_item) = o_a_item {
            match b_item.cmp(&a_item) {
                Ordering::Less => {
                    return false;
                }
                Ordering::Greater => {
                    o_a_item = a_iter.next_from(b_item);
                }
                Ordering::Equal => {
                    o_b_item = b_iter.next();
                    o_a_item = a_iter.next();
                }
            }
        } else {
            return false;
        }
    }
    true
}

/// The contents of Iterator "a" are a proper superset of the contents of "b"
pub fn a_proper_superset_b<'a, T, A, B>(mut a_iter: A, mut b_iter: B) -> bool
where
    T: 'a + Ord,
    A: SkipAheadIterator<'a, T, &'a T>,
    B: SkipAheadIterator<'a, T, &'a T>,
{
    let mut o_a_item = a_iter.next();
    let mut o_b_item = b_iter.next();

    let mut result = false;
    while let Some(b_item) = o_b_item {
        if let Some(a_item) = o_a_item {
            match b_item.cmp(&a_item) {
                Ordering::Less => {
                    return false;
                }
                Ordering::Greater => {
                    result = true;
                    o_a_item = a_iter.next_from(b_item);
                }
                Ordering::Equal => {
                    o_b_item = b_iter.next();
                    o_a_item = a_iter.next();
                }
            }
        } else {
            return false;
        }
    }
    result
}

macro_rules! define_set_op_iterator {
    ( $doc:meta, $iter:ident ) => {
        #[$doc]
        pub struct $iter<'a, T, L, R>
        where
            T: Ord,
            L: SkipAheadIterator<'a, T, &'a T>,
            R: SkipAheadIterator<'a, T, &'a T>,
        {
            l_iter: L,
            r_iter: R,
            phantom: PhantomData<&'a T>
        }

        impl<'a, T, L, R> $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: SkipAheadIterator<'a, T, &'a T>,
            R: SkipAheadIterator<'a, T, &'a T>,
        {
            pub fn new(l_iter: L, r_iter: R) -> Self {
                Self {
                    l_iter: l_iter,
                    r_iter: r_iter,
                    phantom: PhantomData,
                }
            }
        }

        impl<'a, T, L, R> ToList<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord + Clone,
            L: SkipAheadIterator<'a, T, &'a T>,
            R: SkipAheadIterator<'a, T, &'a T>,
        {
        }

        impl<'a, T, L, R> ToSet<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord + Clone,
            L: SkipAheadIterator<'a, T, &'a T>,
            R: SkipAheadIterator<'a, T, &'a T>,
        {
        }

        impl<'a, T, L, R> IterSetOperations<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: SkipAheadIterator<'a, T, &'a T>,
            R: SkipAheadIterator<'a, T, &'a T>,
        {
        }
    };
}

define_set_op_iterator!(
    doc = "An ordered Iterator over the set union of the output of two Iterators whose
(individual) output is ordered and contains no duplicates.",
    Union
);

impl<'a, T, L, R> Iterator for Union<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(l_item) = self.l_iter.peek() {
            if let Some(r_item) = self.r_iter.peek() {
                match l_item.cmp(&r_item) {
                    Ordering::Less => {
                        return self.l_iter.next();
                    }
                    Ordering::Greater => {
                        return self.r_iter.next();
                    }
                    Ordering::Equal => {
                        self.r_iter.next();
                        return self.l_iter.next();
                    }
                }
            } else {
                return self.l_iter.next();
            }
        } else {
            return self.r_iter.next();
        }
    }
}

impl<'a, T, L, R> SkipAheadIterator<'a, T, &'a T> for Union<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        if let Some(l_item) = self.l_iter.peek() {
            if let Some(r_item) = self.r_iter.peek() {
                match l_item.cmp(&r_item) {
                    Ordering::Less | Ordering::Equal => {
                        return Some(l_item);
                    }
                    Ordering::Greater => {
                        return Some(r_item);
                    }
                }
            } else {
                return Some(l_item);
            }
        } else {
            return self.r_iter.peek();
        }
    }

    fn skip_past(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_past(t);
        self.r_iter.skip_past(t);
        self
    }

    fn skip_until(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_until(t);
        self.r_iter.skip_until(t);
        self
    }
}

define_set_op_iterator!(
    doc = "An ordered Iterator over the set intersection of the output of two Iterators whose
(individual) output is ordered and contains no duplicates.",
    Intersection
);

impl<'a, T, L, R> Iterator for Intersection<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_iter.peek() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.skip_until(&r_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_item);
                        }
                        Ordering::Equal => {
                            self.r_iter.next();
                            return self.l_iter.next();
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

impl<'a, T, L, R> SkipAheadIterator<'a, T, &'a T> for Intersection<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        loop {
            if let Some(l_item) = self.l_iter.peek() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.skip_until(&r_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_item);
                        }
                        Ordering::Equal => {
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

    fn skip_past(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_past(t);
        self.r_iter.skip_past(t);
        self
    }

    fn skip_until(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_until(t);
        self.r_iter.skip_until(t);
        self
    }
}

define_set_op_iterator!(
    doc = "An ordered Iterator over the set difference between the output of two
Iterators whose (individual) output is ordered and contains no duplicates.",
    Difference
);

impl<'a, T, L, R> Iterator for Difference<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_iter.peek() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            return self.l_iter.next();
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_item);
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return self.l_iter.next();
                }
            } else {
                return None;
            }
        }
    }
}

impl<'a, T, L, R> SkipAheadIterator<'a, T, &'a T> for Difference<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        loop {
            if let Some(l_item) = self.l_iter.peek() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_item);
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return Some(l_item);
                }
            } else {
                return None;
            }
        }
    }

    fn skip_past(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_past(t);
        self.r_iter.skip_past(t);
        self
    }

    fn skip_until(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_until(t);
        self.r_iter.skip_until(t);
        self
    }
}

define_set_op_iterator!(
    doc = "An ordered Iterator over the symmetric set difference between the output of two
Iterators whose (individual) output is ordered and contains no duplicates.",
    SymmetricDifference
);

impl<'a, T, L, R> Iterator for SymmetricDifference<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_iter.peek() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            return  self.l_iter.next();
                        }
                        Ordering::Greater => {
                            return self.r_iter.next();
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return self.l_iter.next();
                }
            } else {
                return self.r_iter.next();
            }
        }
    }
}

impl<'a, T, L, R> SkipAheadIterator<'a, T, &'a T> for SymmetricDifference<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T, &'a T>,
    R: SkipAheadIterator<'a, T, &'a T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        loop {
            if let Some(l_item) = self.l_iter.peek() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            return  Some(l_item);
                        }
                        Ordering::Greater => {
                            return Some(r_item);
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return Some(l_item);
                }
            } else {
                return self.r_iter.peek();
            }
        }
    }

    fn skip_past(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_past(t);
        self.r_iter.skip_past(t);
        self
    }

    fn skip_until(&mut self, t: &T) -> &mut Self {
        self.l_iter.skip_until(t);
        self.r_iter.skip_until(t);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn are_disjoint_works() {
        let list1 = vec!["a", "c", "e", "g", "i", "k", "m"];
        let list2 = vec!["b", "d", "f", "h", "j", "l", "n"];
        let list3 = vec!["e", "f", "x", "y", "z"];

        assert!(are_disjoint(SetIter::new(&list1), SetIter::new(&list2)));
        assert!(!are_disjoint(SetIter::new(&list1), SetIter::new(&list3)));
        assert!(!are_disjoint(SetIter::new(&list3), SetIter::new(&list2)));
    }

    #[test]
    fn a_superset_b_works() {
        let list1 = vec!["a", "d", "g", "j", "m", "p", "s", "v", "y"];
        let list2 = vec!["b", "e", "h", "k", "n", "q", "r", "w", "z"];
        let list3 = vec!["a", "j", "s", "y"];
        let list4 = vec!["e", "k", "q", "w"];

        assert!(!a_superset_b(SetIter::new(&list1), SetIter::new(&list2)));
        assert!(a_superset_b(SetIter::new(&list1), SetIter::new(&list3)));
        assert!(!a_superset_b(SetIter::new(&list3), SetIter::new(&list1)));
        assert!(a_superset_b(SetIter::new(&list2), SetIter::new(&list4)));
        assert!(!a_superset_b(SetIter::new(&list4), SetIter::new(&list2)));
        assert!(a_superset_b(SetIter::new(&list1), SetIter::new(&list1)));
        assert!(a_superset_b(SetIter::new(&list2), SetIter::new(&list2)));
        assert!(a_superset_b(SetIter::new(&list3), SetIter::new(&list3)));
        assert!(a_superset_b(SetIter::new(&list4), SetIter::new(&list4)));
    }

    #[test]
    fn a_proper_superset_b_works() {
        let list1 = vec!["a", "d", "g", "j", "m", "p", "s", "v", "y"];
        let list2 = vec!["b", "e", "h", "k", "n", "q", "r", "w", "z"];
        let list3 = vec!["a", "j", "s", "y"];
        let list4 = vec!["e", "k", "q", "w"];

        assert!(!a_proper_superset_b(
            SetIter::new(&list1),
            SetIter::new(&list2)
        ));
        assert!(a_proper_superset_b(
            SetIter::new(&list1),
            SetIter::new(&list3)
        ));
        assert!(!a_proper_superset_b(
            SetIter::new(&list3),
            SetIter::new(&list1)
        ));
        assert!(a_proper_superset_b(
            SetIter::new(&list2),
            SetIter::new(&list4)
        ));
        assert!(!a_proper_superset_b(
            SetIter::new(&list4),
            SetIter::new(&list2)
        ));
        assert!(!a_proper_superset_b(
            SetIter::new(&list1),
            SetIter::new(&list1)
        ));
        assert!(!a_proper_superset_b(
            SetIter::new(&list2),
            SetIter::new(&list2)
        ));
        assert!(!a_proper_superset_b(
            SetIter::new(&list3),
            SetIter::new(&list3)
        ));
        assert!(!a_proper_superset_b(
            SetIter::new(&list4),
            SetIter::new(&list4)
        ));
    }

    static LIST_0: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static LIST_1: &[&str] = &["b", "d", "f", "h", "i", "k", "m"];
    static LIST_2: &[&str] = &[
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
    ];

    #[test]
    fn union_works() {
        let mut test_iter = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_1[0..2]));
        assert_eq!(test_iter.next(), Some(&"a"));
        let result = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_1[0..2])).to_list();
        assert_eq!(result, vec!["a", "b", "c", "d", "e"]);
        let result = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2])).to_list();
        assert_eq!(result, vec!["a", "b", "c", "e"]);
        let result = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .to_list();
        assert_eq!(result, vec!["a", "c", "d", "e", "f"]);
        let set = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .to_set();
        let vec: Vec<&str> = set.iter().to_list();
        assert_eq!(vec, vec!["a", "c", "d", "e", "f"]);
    }

    #[test]
    fn intersection_works() {
        let mut test_iter =
            Intersection::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_1[..2]));
        assert_eq!(test_iter.next(), None);
        let result: Vec<&str> =
            Intersection::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_1[..2]))
                .cloned()
                .collect();
        assert_eq!(result, Vec::<&str>::new());
        let result: Vec<&str> =
            Intersection::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["a"]);
        let result: Vec<&str> =
            Intersection::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
                .symmetric_difference(SetIter::new(&LIST_1[..3]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["a", "b", "d", "f"]);
        let set = Intersection::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["a", "b", "d", "f"]);
    }

    #[test]
    fn difference() {
        let mut test_iter = Difference::new(SetIter::new(&LIST_0[..1]), SetIter::new(&LIST_0[..1]));
        assert_eq!(test_iter.next(), None);
        let mut test_iter = Difference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_1[..2]));
        assert_eq!(test_iter.next(), Some(&"a"));
        let result: Vec<&str> =
            Difference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_1[..2]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["a", "c", "e"]);
        let result: Vec<&str> =
            Difference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["c", "e"]);
        let result: Vec<&str> =
            Difference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
                .symmetric_difference(SetIter::new(&LIST_1[..3]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["b", "c", "d", "e", "f"]);
        let set = Difference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["b", "c", "d", "e", "f"]);
    }

    #[test]
    fn symmetric_difference_works() {
        let mut test_iter =
            SymmetricDifference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_1[..2]));
        assert_eq!(test_iter.next(), Some(&"a"));
        let result: Vec<&str> =
            SymmetricDifference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_1[..2]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["a", "b", "c", "d", "e"]);
        let result: Vec<&str> =
            SymmetricDifference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["b", "c", "e"]);
        let result: Vec<&str> =
            SymmetricDifference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
                .symmetric_difference(SetIter::new(&LIST_1[..3]))
                .cloned()
                .collect();
        assert_eq!(result, vec!["c", "d", "e", "f"]);
        let set = SymmetricDifference::new(SetIter::new(&LIST_0[..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .to_set();
        let vec: Vec<&str> = set.iter().cloned().collect();
        assert_eq!(vec, vec!["c", "d", "e", "f"]);
    }

    #[test]
    fn skip_past_works() {
        let set = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .skip_past(&"c")
            .to_set();
        let vec: Vec<&str> = set.iter().to_list();
        assert_eq!(vec, vec!["d", "e", "f"]);
    }

    #[test]
    fn skip_until_works() {
        let set = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .skip_until(&"c")
            .to_set();
        let vec: Vec<&str> = set.iter().to_list();
        assert_eq!(vec, vec!["c", "d", "e", "f"]);
    }
}
