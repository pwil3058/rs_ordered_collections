macro_rules! after_index {
    ( $list:expr, $target:expr ) => {
        match $list.binary_search($target) {
            Ok(index) => index + 1,
            Err(index) => index,
        }
    };
}

macro_rules! from_index {
    ( $list:expr, $target:expr ) => {
        match $list.binary_search($target) {
            Ok(index) => index,
            Err(index) => index,
        }
    };
}

use std::cmp::Ordering;
use std::marker::PhantomData;
use std::ops::{BitAnd, BitOr, BitXor, Sub};

use crate::OrderedSet;

/// Iterator enhancement to provide a skip ahead feature. This mechanism
/// is used to optimise implementation of set operation (difference, intersection, etc)
/// iterators.
pub trait SkipAheadIterator<'a, T: 'a + Ord>: Iterator<Item = &'a T> {
    /// Peek at the next item in the iterator
    fn peek(&mut self) -> Option<&'a T>;

    /// Skip ahead to the next item in the iterator after the given item.
    fn skip_past(&mut self, t: &T) -> &mut Self;

    /// Skip ahead to the next item in the iterator at or after the given item.
    fn skip_until(&mut self, t: &T) -> &mut Self;
}

pub trait ToList<'a, T>: Iterator<Item = &'a T>
where
    T: 'a + Clone,
{
    /// Create a Vec<T> list from the elements in the Iterator's output
    fn to_list(&mut self) -> Vec<T> {
        self.cloned().collect()
    }
}

pub trait ToSet<'a, T>: ToList<'a, T>
where
    T: 'a + Ord + Clone,
{
    /// Create a OrderedSet<T> from the elements in the Iterator's output
    fn to_set(&mut self) -> OrderedSet<T> {
        OrderedSet::<T> {
            members: self.to_list(),
        }
    }
}

// SET ITERATOR

/// An Iterator over the elements in an ordered list
pub struct SetIter<'a, T: Ord> {
    elements: &'a [T],
    index: usize,
}

impl<'a, T: Ord> SetIter<'a, T> {
    pub(crate) fn new(elements: &'a [T]) -> Self {
        Self { elements, index: 0 }
    }
}

impl<'a, T: Ord> Iterator for SetIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(element) = self.elements.get(self.index) {
            self.index += 1;
            Some(element)
        } else {
            None
        }
    }
}

impl<'a, T: 'a + Ord> SkipAheadIterator<'a, T> for SetIter<'a, T> {
    fn skip_past(&mut self, t: &T) -> &mut Self {
        self.index += after_index!(self.elements[self.index..], t);
        self
    }

    fn skip_until(&mut self, t: &T) -> &mut Self {
        self.index += from_index!(self.elements[self.index..], t);
        self
    }

    fn peek(&mut self) -> Option<&'a T> {
        self.elements.get(self.index)
    }
}

impl<'a, T: Ord + Clone> ToList<'a, T> for SetIter<'a, T> {}

impl<'a, T: Ord + Clone> ToSet<'a, T> for SetIter<'a, T> {}

impl<'a, T: Ord + Clone> IterSetOperations<'a, T> for SetIter<'a, T> {}

macro_rules! impl_op_for_set_iter {
    ( $op:ident, $op_fn:ident, $output:ident, $doc:meta ) => {
        impl<'a, T, I> $op<I> for SetIter<'a, T>
        where
            T: Ord,
            Self: Sized,
            I: SkipAheadIterator<'a, T>,
        {
            type Output = $output<'a, T, Self, I>;

            #[$doc]
            fn $op_fn(self, other: I) -> Self::Output {
                $output::new(self, other)
            }
        }
    };
}

impl_op_for_set_iter!(
    BitOr,
    bitor,
    Union,
    doc = "Return a new ordered iterator orver the set union of the contents
    of this iterator and other i.e. elements that appear in this iterator
    or other."
);
impl_op_for_set_iter!(
    BitAnd,
    bitand,
    Intersection,
    doc = "Return a new ordered iterator orver the set intersection of the contents
    of this iterator and other i.e. elements that appear in both this iterator
    and other."
);
impl_op_for_set_iter!(
    BitXor,
    bitxor,
    SymmetricDifference,
    doc = "Return a new ordered iterator orver the symmetric set difference
    between the contents of this iterator and other i.e. elements that appear
    in this iterator or other but not both."
);
impl_op_for_set_iter!(
    Sub,
    sub,
    Difference,
    doc = "Return a new ordered iterator orver the set difference of the contents
    of this iterator and other i.e. elements that appear in this iterator
    but not other."
);

pub trait IterSetOperations<'a, T>: SkipAheadIterator<'a, T> + Sized
where
    T: 'a + Ord,
{
    /// Iterate over the set union of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn union<I: SkipAheadIterator<'a, T>>(self, iter: I) -> Union<'a, T, Self, I> {
        Union::new(self, iter)
    }

    /// Iterate over the set intersection of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn intersection<I: SkipAheadIterator<'a, T>>(self, iter: I) -> Intersection<'a, T, Self, I> {
        Intersection::new(self, iter)
    }

    /// Iterate over the set difference of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn difference<I: SkipAheadIterator<'a, T>>(self, iter: I) -> Difference<'a, T, Self, I> {
        Difference::new(self, iter)
    }

    /// Iterate over the set symmetric difference of this Iterator and the given Iterator
    /// in the order defined their elements Ord trait implementation.
    fn symmetric_difference<I: SkipAheadIterator<'a, T>>(
        self,
        iter: I,
    ) -> SymmetricDifference<'a, T, Self, I> {
        SymmetricDifference::new(self, iter)
    }

    /// Is the output of the given Iterator disjoint from the output of
    /// this iterator?
    fn is_disjoint<I: SkipAheadIterator<'a, T>>(self, iter: I) -> bool {
        are_disjoint(self, iter)
    }

    /// Is the output of the given Iterator a proper subset of the output of
    /// this iterator?
    fn is_proper_subset<I: SkipAheadIterator<'a, T>>(self, iter: I) -> bool {
        a_proper_superset_b(self, iter)
    }

    /// Is the output of the given Iterator a proper superset of the output of
    /// this iterator?
    fn is_proper_superset<I: SkipAheadIterator<'a, T>>(self, iter: I) -> bool {
        a_proper_superset_b(iter, self)
    }

    /// Is the output of the given Iterator a subset of the output of
    /// this iterator?
    fn is_subset<I: SkipAheadIterator<'a, T>>(self, iter: I) -> bool {
        a_superset_b(self, iter)
    }

    /// Is the output of the given Iterator a superset of the output of
    /// this iterator?
    fn is_superset<I: SkipAheadIterator<'a, T>>(self, iter: I) -> bool {
        a_superset_b(iter, self)
    }
}

/// The contents of the two iterators are disjoint
pub fn are_disjoint<'a, T, L, R>(mut l_iter: L, mut r_iter: R) -> bool
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    loop {
        if let Some(l_element) = l_iter.peek() {
            if let Some(r_element) = r_iter.peek() {
                match l_element.cmp(&r_element) {
                    Ordering::Less => {
                        l_iter.skip_until(r_element);
                    }
                    Ordering::Greater => {
                        r_iter.skip_until(l_element);
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
    A: SkipAheadIterator<'a, T>,
    B: SkipAheadIterator<'a, T>,
{
    while let Some(b_element) = b_iter.peek() {
        if let Some(a_element) = a_iter.peek() {
            match b_element.cmp(&a_element) {
                Ordering::Less => {
                    return false;
                }
                Ordering::Greater => {
                    a_iter.skip_until(b_element);
                }
                Ordering::Equal => {
                    b_iter.next();
                    a_iter.next();
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
    A: SkipAheadIterator<'a, T>,
    B: SkipAheadIterator<'a, T>,
{
    let mut result = false;
    while let Some(b_element) = b_iter.peek() {
        if let Some(a_element) = a_iter.peek() {
            match b_element.cmp(&a_element) {
                Ordering::Less => {
                    return false;
                }
                Ordering::Greater => {
                    result = true;
                    a_iter.skip_until(b_element);
                }
                Ordering::Equal => {
                    b_iter.next();
                    a_iter.next();
                }
            }
        } else {
            return false;
        }
    }
    result
}

macro_rules! impl_op_for_iterator {
    ( $iterator:ident, $op:ident, $op_fn:ident, $output:ident, $doc:meta, ) => {
        impl<'a, T, L, R, I> $op<I> for $iterator<'a, T, L, R>
        where
            T: Ord,
            Self: Sized,
            L: SkipAheadIterator<'a, T>,
            R: SkipAheadIterator<'a, T>,
            I: SkipAheadIterator<'a, T>,
        {
            type Output = $output<'a, T, Self, I>;

            #[$doc]
            fn $op_fn(self, other: I) -> Self::Output {
                $output::new(self, other)
            }
        }
    };
}

macro_rules! define_set_op_iterator {
    ( $doc:meta, $iter:ident ) => {
        #[$doc]
        pub struct $iter<'a, T, L, R>
        where
            T: Ord,
            L: SkipAheadIterator<'a, T>,
            R: SkipAheadIterator<'a, T>,
        {
            l_iter: L,
            r_iter: R,
            phantom: PhantomData<&'a T>,
        }

        impl<'a, T, L, R> $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: SkipAheadIterator<'a, T>,
            R: SkipAheadIterator<'a, T>,
        {
            pub(crate) fn new(l_iter: L, r_iter: R) -> Self {
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
            L: SkipAheadIterator<'a, T>,
            R: SkipAheadIterator<'a, T>,
        {
        }

        impl<'a, T, L, R> ToSet<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord + Clone,
            L: SkipAheadIterator<'a, T>,
            R: SkipAheadIterator<'a, T>,
        {
        }

        impl<'a, T, L, R> IterSetOperations<'a, T> for $iter<'a, T, L, R>
        where
            T: 'a + Ord,
            L: SkipAheadIterator<'a, T>,
            R: SkipAheadIterator<'a, T>,
        {
        }

        impl_op_for_iterator!(
            $iter,
            BitOr,
            bitor,
            Union,
            doc = "Apply the | operator to return a new ordered iterator
        over the union of this iteratro and other
        i.e. the elements that are in this iterator or in other.",
        );
        impl_op_for_iterator!(
            $iter,
            BitAnd,
            bitand,
            Intersection,
            doc = "Apply the & operator to return a new ordered iterator
        over the intersection of this iterator and other i.e. the
        elements that are in both this set and in other.",
        );
        impl_op_for_iterator!(
            $iter,
            BitXor,
            bitxor,
            SymmetricDifference,
            doc = "Apply the ^ operator to return a new ordered iterator over
        the symmetric set difference between this iterator and other
        i.e. the elements that are in this iterator or in other but not in both.",
        );
        impl_op_for_iterator!(
            $iter,
            Sub,
            sub,
            Difference,
            doc = "Apply the - operator to return a new ordered iterator over
        the set difference between this set and other i.e. the elements
        that are in this iterator but not in other.",
        );
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
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(l_element) = self.l_iter.peek() {
            if let Some(r_element) = self.r_iter.peek() {
                match l_element.cmp(&r_element) {
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

impl<'a, T, L, R> SkipAheadIterator<'a, T> for Union<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        if let Some(l_element) = self.l_iter.peek() {
            if let Some(r_element) = self.r_iter.peek() {
                match l_element.cmp(&r_element) {
                    Ordering::Less | Ordering::Equal => {
                        return Some(l_element);
                    }
                    Ordering::Greater => {
                        return Some(r_element);
                    }
                }
            } else {
                return Some(l_element);
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
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_element) = self.l_iter.peek() {
                if let Some(r_element) = self.r_iter.peek() {
                    match l_element.cmp(&r_element) {
                        Ordering::Less => {
                            self.l_iter.skip_until(&r_element);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_element);
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

impl<'a, T, L, R> SkipAheadIterator<'a, T> for Intersection<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        loop {
            if let Some(l_element) = self.l_iter.peek() {
                if let Some(r_element) = self.r_iter.peek() {
                    match l_element.cmp(&r_element) {
                        Ordering::Less => {
                            self.l_iter.skip_until(&r_element);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_element);
                        }
                        Ordering::Equal => {
                            return Some(l_element);
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
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_element) = self.l_iter.peek() {
                if let Some(r_element) = self.r_iter.peek() {
                    match l_element.cmp(&r_element) {
                        Ordering::Less => {
                            return self.l_iter.next();
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_element);
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

impl<'a, T, L, R> SkipAheadIterator<'a, T> for Difference<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        loop {
            if let Some(l_element) = self.l_iter.peek() {
                if let Some(r_element) = self.r_iter.peek() {
                    match l_element.cmp(&r_element) {
                        Ordering::Less => {
                            return Some(l_element);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_element);
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return Some(l_element);
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
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_element) = self.l_iter.peek() {
                if let Some(r_element) = self.r_iter.peek() {
                    match l_element.cmp(&r_element) {
                        Ordering::Less => {
                            return self.l_iter.next();
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

impl<'a, T, L, R> SkipAheadIterator<'a, T> for SymmetricDifference<'a, T, L, R>
where
    T: 'a + Ord,
    L: SkipAheadIterator<'a, T>,
    R: SkipAheadIterator<'a, T>,
{
    fn peek(&mut self) -> Option<&'a T> {
        loop {
            if let Some(l_element) = self.l_iter.peek() {
                if let Some(r_element) = self.r_iter.peek() {
                    match l_element.cmp(&r_element) {
                        Ordering::Less => {
                            return Some(l_element);
                        }
                        Ordering::Greater => {
                            return Some(r_element);
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return Some(l_element);
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

    // Return true if the data stream from the Iterator is ordered and
    // contains no duplicates.  Useful for testing.
    fn output_is_ordered_nodups<'a, T, I>(iter: &mut I) -> bool
    where
        T: 'a + Ord,
        I: SkipAheadIterator<'a, T>,
    {
        let mut o_previous = iter.next();
        while let Some(previous) = o_previous {
            if let Some(element) = iter.next() {
                if previous >= element {
                    return false;
                }
                o_previous = Some(element);
            } else {
                o_previous = None;
            }
        }
        true
    }

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static LIST_UNORDERED: &[&str] = &["a", "c", "e", "z", "g", "i", "k", "m"];

    #[test]
    fn output_is_ordered_nodups_works() {
        assert!(output_is_ordered_nodups(&mut SetIter::new(LIST)));
        let rev: Vec<&str> = LIST.iter().rev().cloned().collect();
        assert!(!output_is_ordered_nodups(&mut SetIter::new(&rev)));
        assert!(!output_is_ordered_nodups(&mut SetIter::new(LIST_UNORDERED)));
        let rev: Vec<&str> = LIST_UNORDERED.iter().rev().cloned().collect();
        assert!(!output_is_ordered_nodups(&mut SetIter::new(&rev)));
        //assert!(output_is_ordered_nodups(&mut MapIter::new(MAP)));
    }

    #[test]
    fn set_iter_works() {
        let vec = LIST.to_vec();
        assert_eq!(SetIter::new(LIST).to_list(), vec);
        let mut set_iter = SetIter::new(LIST);
        assert_eq!(set_iter.skip_past(&"g").next(), Some(&"i"));
        assert_eq!(set_iter.to_list(), vec[5..].to_vec());
        let mut set_iter = SetIter::new(LIST);
        assert_eq!(set_iter.skip_until(&"g").next(), Some(&"g"));
        assert_eq!(set_iter.to_list(), vec[4..].to_vec());
    }

    #[test]
    fn set_iter_skip_past_works() {
        assert_eq!(SetIter::new(LIST).skip_past(&"g").next(), Some(&"i"));
        assert_eq!(SetIter::new(LIST).skip_past(&"f").next(), Some(&"g"));
        assert_eq!(SetIter::new(LIST).skip_past(&"g").to_set().len(), 3);
    }

    #[test]
    fn set_iter_skip_until_works() {
        assert_eq!(SetIter::new(LIST).skip_until(&"g").next(), Some(&"g"));
        assert_eq!(SetIter::new(LIST).skip_until(&"f").next(), Some(&"g"));
        assert_eq!(SetIter::new(LIST).skip_until(&"f").to_set().len(), 4);
    }

    #[test]
    fn iter_after_works() {
        let vec = LIST.to_vec();
        let mut iter_after = SetIter::new(&LIST[after_index!(LIST, &"g")..]);
        assert_eq!(iter_after.to_list(), vec[4..].to_vec());
        let mut iter_after = SetIter::new(&LIST[after_index!(LIST, &"f")..]);
        assert_eq!(iter_after.to_list(), vec[3..].to_vec());
    }

    #[test]
    fn iter_before_works() {
        let vec = LIST.to_vec();
        let mut iter_before = SetIter::new(&LIST[..from_index!(LIST, &"g")]);
        assert_eq!(iter_before.to_list(), vec[..3].to_vec());
        let mut iter_before = SetIter::new(&LIST[..from_index!(LIST, &"f")]);
        assert_eq!(iter_before.to_list(), vec[..3].to_vec());
    }

    #[test]
    fn iter_from_works() {
        let vec = LIST.to_vec();
        let mut iter_from = SetIter::new(&LIST[from_index!(LIST, &"g")..]);
        assert_eq!(iter_from.to_list(), vec[3..].to_vec());
        let mut iter_from = SetIter::new(&LIST[from_index!(LIST, &"f")..]);
        assert_eq!(iter_from.to_list(), vec[3..].to_vec());
    }

    #[test]
    fn iter_until_works() {
        let vec = LIST.to_vec();
        let mut iter_until = SetIter::new(&LIST[..after_index!(LIST, &"g")]);
        assert_eq!(iter_until.to_list(), vec[..4].to_vec());
        let mut iter_until = SetIter::new(&LIST[..after_index!(LIST, &"f")]);
        assert_eq!(iter_until.to_list(), vec[..3].to_vec());
    }

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
    fn union_skip_past_works() {
        let set = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .skip_past(&"c")
            .to_set();
        let vec: Vec<&str> = set.iter().to_list();
        assert_eq!(vec, vec!["d", "e", "f"]);
    }

    #[test]
    fn union_skip_until_works() {
        let set = Union::new(SetIter::new(&LIST_0[0..3]), SetIter::new(&LIST_2[..2]))
            .symmetric_difference(SetIter::new(&LIST_1[..3]))
            .skip_until(&"c")
            .to_set();
        let vec: Vec<&str> = set.iter().to_list();
        assert_eq!(vec, vec!["c", "d", "e", "f"]);
    }

    #[test]
    fn set_iter_operators() {
        let i1 = SetIter::new(&["a", "d", "f", "h", "k"]);
        let i2 = SetIter::new(&["b", "d", "h", "i", "j", "k"]);
        assert_eq!(
            (i1 | i2).to_list(),
            &["a", "b", "d", "f", "h", "i", "j", "k"]
        );
        let i1 = SetIter::new(&["a", "d", "f", "h", "k"]);
        let i2 = SetIter::new(&["b", "d", "h", "i", "j", "k"]);
        assert_eq!((i1 & i2).to_list(), &["d", "h", "k"]);
        let i1 = SetIter::new(&["a", "d", "f", "h", "k"]);
        let i2 = SetIter::new(&["b", "d", "h", "i", "j", "k"]);
        assert_eq!((i1 ^ i2).to_list(), &["a", "b", "f", "i", "j"]);
        let i1 = SetIter::new(&["a", "d", "f", "h", "k"]);
        let i2 = SetIter::new(&["b", "d", "h", "i", "j", "k"]);
        let i3 = SetIter::new(&["a", "c", "h", "k", "l", "m"]);
        let i4 = SetIter::new(&["a", "d", "e", "i", "k", "l"]);
        let i5 = SetIter::new(&["b", "d", "h", "i", "j", "k"]);
        assert_eq!(
            (((i1 | i2) & i3) ^ (i4 - i5)).to_list(),
            &["e", "h", "k", "l"]
        );
    }
}
