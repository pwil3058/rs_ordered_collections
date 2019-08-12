//! Sets implemented as a sorted list.
//! Useful for those situations when ordered iteration over a set's
//! contents is a frequent requirement.

use std::borrow::Borrow;
use std::convert::From;
use std::default::Default;
use std::iter::FromIterator;
use std::ops::{BitAnd, BitOr, BitXor, Sub};
use std::vec::Drain;

pub mod ord_set_iterators;

use self::ord_set_iterators::{
    a_superset_b, are_disjoint, Difference, Intersection, SetIter, SymmetricDifference, ToSet,
    Union,
};

/// An set of items of type T ordered according to Ord (with no duplicates)
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OrderedSet<T: Ord> {
    pub(crate) members: Vec<T>,
}

impl<T: Ord> OrderedSet<T> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the number of items in this set.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    pub fn is_empty(&self) -> bool {
        self.members.len() == 0
    }

    pub fn capacity(&self) -> usize {
        self.members.capacity()
    }

    pub fn clear(&mut self) {
        self.members.clear()
    }

    /// Return false if the item was already a member otherwise true
    pub fn insert(&mut self, item: T) -> bool {
        if let Err(index) = self.members.binary_search(&item) {
            self.members.insert(index, item);
            true
        } else {
            false
        }
    }

    /// Return true if the item was a member and false otherwise
    pub fn remove<Q>(&mut self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Ok(index) = self.members.binary_search_by_key(&item, |x| x.borrow()) {
            self.members.remove(index);
            true
        } else {
            false
        }
    }

    /// Return false if the item is already a member
    pub fn contains<Q>(&self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.members
            .binary_search_by_key(&item, |x| x.borrow())
            .is_ok()
    }

    pub fn first(&self) -> Option<&T> {
        self.members.first()
    }

    pub fn last(&self) -> Option<&T> {
        self.members.last()
    }

    pub fn iter(&self) -> SetIter<'_, T> {
        SetIter::new(&self.members)
    }

    pub fn drain(&mut self) -> Drain<'_, T> {
        self.members.drain(..)
    }

    // Return true if members is sorted and contains no duplicates
    #[cfg(test)]
    pub(crate) fn is_valid(&self) -> bool {
        for i in 1..self.members.len() {
            if self.members[i - 1] >= self.members[i] {
                return false;
            }
        }
        true
    }

    /// Return true if this OrderedSet is disjoint from the other OrderedSet
    pub fn is_disjoint(&self, other: &Self) -> bool {
        are_disjoint(self.iter(), other.iter())
    }

    /// Return true if self is a subset of other
    pub fn is_subset(&self, other: &Self) -> bool {
        a_superset_b(other.iter(), self.iter())
    }

    /// Return true if self is a subset of other
    pub fn is_proper_subset(&self, other: &Self) -> bool {
        other.len() > self.len() && a_superset_b(other.iter(), self.iter())
    }

    /// Return true if self is a superset of other
    pub fn is_superset(&self, other: &Self) -> bool {
        a_superset_b(self.iter(), other.iter())
    }

    /// Return true if self is a superset of other
    pub fn is_proper_superset(&self, other: &Self) -> bool {
        self.len() > other.len() && a_superset_b(self.iter(), other.iter())
    }
}

impl<T: Ord> Default for OrderedSet<T> {
    fn default() -> Self {
        Self { members: vec![] }
    }
}

/// Convert to OrderedSet<T> from a slice of elements
impl<T: Ord + Clone> From<&[T]> for OrderedSet<T> {
    fn from(list: &[T]) -> Self {
        let mut vec = list.to_vec();
        vec.sort();
        vec.dedup();
        Self { members: vec }
    }
}

/// Convert to OrderedSet<T> from a slice of elements
impl<T: Ord + Clone> From<Vec<T>> for OrderedSet<T> {
    fn from(mut vec: Vec<T>) -> Self {
        vec.sort();
        vec.dedup();
        Self { members: vec }
    }
}

impl<T: Ord> FromIterator<T> for OrderedSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut ordered_set = OrderedSet::<T>::default();

        for i in iter {
            ordered_set.insert(i);
        }

        ordered_set
    }
}

impl<'a, T: 'a + Ord + Clone> FromIterator<&'a T> for OrderedSet<T> {
    fn from_iter<I: IntoIterator<Item = &'a T>>(iter: I) -> Self {
        let mut ordered_set = OrderedSet::<T>::default();

        for i in iter.into_iter().cloned() {
            ordered_set.insert(i);
        }

        ordered_set
    }
}

macro_rules! define_set_operation {
    ( $iter:ident, $fn_doc:meta, $function:ident,  $op_doc:meta, $op:ident, $op_fn:ident ) => {
        impl<T: Ord> OrderedSet<T> {
            #[$fn_doc]
            pub fn $function<'a>(
                &'a self,
                other: &'a Self,
            ) -> $iter<'a, T, SetIter<'a, T>, SetIter<'a, T>> {
                $iter::new(self.iter(), other.iter())
            }
        }

        impl<T: Ord + Clone> $op for OrderedSet<T> {
            type Output = Self;

            #[$op_doc]
            fn $op_fn(self, other: Self) -> Self::Output {
                self.$function(&other).to_set()
            }
        }

        impl<T: Ord + Clone> $op for &OrderedSet<T> {
            type Output = OrderedSet<T>;

            #[$op_doc]
            fn $op_fn(self, other: Self) -> Self::Output {
                self.$function(&other).to_set()
            }
        }
    };
}

define_set_operation!(
    Difference,
    doc = "Return an ordered iterator over the set difference between this set and other
    i.e. the elements that are in this set but not in other.",
    difference,
    doc = "Apply the - operator to return a new set containing the set difference
    between this set and other i.e. the elements that are in this set but not in other.",
    Sub,
    sub
);
define_set_operation!(
    SymmetricDifference,
    doc = "Return an ordered iterator over the symmetric set difference between this set and other
    i.e. the elements that are in this set or in other but not in both.",
    symmetric_difference,
    doc = "Apply the ^ operator to return a new set containing the symmetric set difference
    between this set and other i.e. the elements that are in this set or in other but not in both.",
    BitXor,
    bitxor
);
define_set_operation!(
    Union,
    doc = "Return an ordered iterator over the union of this set and other
    i.e. the elements that are in this set or other.",
    union,
    doc = "Apply the | operator to return a new set containing the union of this set and other
    i.e. the elements that are in this set or in other.",
    BitOr,
    bitor
);
define_set_operation!(
    Intersection,
    doc = "Return an ordered iterator over the intersection of this set and other
    i.e. the elements that are in both this set and other.",
    intersection,
    doc = "Apply the & operator to return a new set containing the intersection
    of this set and other i.e. the elements that are in both this set and in other.",
    BitAnd,
    bitand
);

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    use super::*;
    use rand::prelude::*;

    use crate::ordered_set::ord_set_iterators::{SkipAheadIterator, ToList};

    static TEST_STRS: &[&str] = &[
        "hhh", "aaa", "ggg", "sss", "zzz", "bbb", "fff", "iii", "qqq", "jjj", "ddd", "eee", "ccc",
        "mmm", "lll", "nnn", "ppp", "rrr",
    ];

    fn random_sequence(length: usize) -> Vec<u64> {
        let mut v = vec![];
        for _ in 0..length {
            let t: u64 = random();
            v.push(t)
        }
        v
    }

    fn calculate_hash<T: Hash>(t: &T) -> u64 {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        s.finish()
    }

    #[test]
    fn default_works() {
        assert!(OrderedSet::<String>::default().len() == 0);
        assert!(OrderedSet::<u32>::default().len() == 0);
    }

    #[test]
    fn from_works() {
        let set: OrderedSet<&str> = TEST_STRS.into();
        let mut vec = TEST_STRS.to_vec();
        vec.sort();
        assert_eq!(vec, set.iter().to_list());
        let uvec = TEST_STRS.to_vec();
        let set: OrderedSet<&str> = uvec.into();
        assert_eq!(vec, set.iter().to_list());
        let set: OrderedSet<&str> = vec!["a", "h", "b", "z", "x", "i", "b"].into();
        assert_eq!(vec!["a", "b", "h", "i", "x", "z"], set.iter().to_list());
    }

    #[test]
    fn check_constraints() {
        // This is to check what constraints are required for T
        // to give full functionality to the sets
        // Won't compile with Clone.
        #[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
        struct Item {
            i: u32,
        }
        let list_1 = OrderedSet::<Item>::default();
        let list_2 = OrderedSet::<Item>::default();
        let list_3 = list_1 | list_2;
        assert!(list_3.len() == 0);
    }

    #[test]
    fn insert_works() {
        let mut str_set = OrderedSet::<String>::default();
        assert!(str_set.is_valid());
        assert!(str_set.first().is_none());
        for text in TEST_STRS.iter() {
            assert!(str_set.insert(text.to_string()));
            assert!(str_set.is_valid());
            assert!(str_set.contains(&text.to_string()));
            assert!(!str_set.insert(text.to_string()));
            assert!(str_set.is_valid());
            assert!(str_set.contains(&text.to_string()));
        }
        for text in TEST_STRS.iter() {
            assert!(!str_set.insert(text.to_string()));
            assert!(str_set.is_valid());
            assert!(str_set.contains(&text.to_string()));
        }
        assert_eq!(str_set.first(), Some(&"aaa".to_string()));
    }

    #[test]
    fn from_iter_works() {
        let str_set: OrderedSet<String> = TEST_STRS.into_iter().map(|s| s.to_string()).collect();
        assert!(str_set.is_valid());
        for text in TEST_STRS.iter() {
            assert!(str_set.contains(&text.to_string()))
        }
        for string in str_set.iter() {
            assert!(TEST_STRS.contains(&string.as_str()));
        }

        let u64_seq = random_sequence(1000);
        assert_eq!(u64_seq.len(), 1000);
        let u64_set: OrderedSet<u64> = u64_seq.iter().map(|u| *u).collect();
        assert!(u64_set.is_valid());
        for u in u64_seq.iter() {
            assert!(u64_set.contains(u));
        }
        for u in u64_set.iter() {
            assert!(u64_seq.contains(u));
        }
        assert_eq!(u64_seq.len(), u64_set.len());
    }

    #[test]
    fn iter_after_works() {
        let str_set: OrderedSet<String> = TEST_STRS.into_iter().map(|s| s.to_string()).collect();
        for item in str_set.iter().advance_past(&"jjj".to_string()) {
            assert!(item > &"jjj".to_string());
            assert!(TEST_STRS.contains(&item.as_str()));
        }
        for item in str_set.iter().advance_past(&"zzz".to_string()) {
            assert!(item > &"zzz".to_string());
            assert!(false);
        }
    }

    #[test]
    fn remove_works() {
        let mut str_set: OrderedSet<String> =
            TEST_STRS.into_iter().map(|s| s.to_string()).collect();
        for text in TEST_STRS.iter() {
            assert!(str_set.remove(&text.to_string()));
            assert!(!str_set.remove(&text.to_string()));
        }
        assert!(str_set.is_empty());
    }

    #[test]
    fn equality_and_hash_work() {
        let str_set1: OrderedSet<String> = TEST_STRS.into_iter().map(|s| s.to_string()).collect();
        let mut str_set2: OrderedSet<String> =
            TEST_STRS.into_iter().map(|s| s.to_string()).collect();
        assert_eq!(str_set1, str_set2);
        assert_eq!(calculate_hash(&str_set1), calculate_hash(&str_set2));
        assert!(str_set2.remove(&TEST_STRS.first().unwrap().to_string()));
        assert!(str_set1 != str_set2);
        assert!(calculate_hash(&str_set1) != calculate_hash(&str_set2));
    }

    #[test]
    fn test_is_disjoint() {
        let str_set1: OrderedSet<String> =
            TEST_STRS[0..5].into_iter().map(|s| s.to_string()).collect();
        let str_set2: OrderedSet<String> =
            TEST_STRS[5..].into_iter().map(|s| s.to_string()).collect();
        assert!(str_set1.is_disjoint(&str_set2));
        let str_set1: OrderedSet<String> =
            TEST_STRS[0..8].into_iter().map(|s| s.to_string()).collect();
        let str_set2: OrderedSet<String> =
            TEST_STRS[4..].into_iter().map(|s| s.to_string()).collect();
        assert!(!str_set1.is_disjoint(&str_set2));

        let u64_seq = random_sequence(1000);
        let set1: OrderedSet<u64> = u64_seq[0..500].iter().map(|u| *u).collect();
        let set2: OrderedSet<u64> = u64_seq[500..].iter().map(|u| *u).collect();
        assert!(set1.is_disjoint(&set2));
        let set1: OrderedSet<u64> = u64_seq[0..700].iter().map(|u| *u).collect();
        let set2: OrderedSet<u64> = u64_seq[300..].iter().map(|u| *u).collect();
        assert!(!set1.is_disjoint(&set2));
    }

    #[test]
    fn test_is_subset() {
        let max = TEST_STRS.len();
        for test in &[
            ((0, 7), (7, max), false, false),
            ((7, max), (5, max), true, true),
            ((5, max), (7, max), false, false),
            ((1, 7), (1, 7), true, false),
            ((0, 9), (5, max), false, false),
            ((1, max), (1, 7), false, false),
        ] {
            println!("TEST: {:?}", test); // to help identify failed tests
            let set1: OrderedSet<String> = TEST_STRS[(test.0).0..(test.0).1]
                .into_iter()
                .map(|s| s.to_string())
                .collect();
            let set2: OrderedSet<String> = TEST_STRS[(test.1).0..(test.1).1]
                .into_iter()
                .map(|s| s.to_string())
                .collect();
            assert!(set1.is_subset(&set2) == test.2);
            if set1.is_subset(&set2) {
                for item in set1.iter() {
                    assert!(set2.contains(item));
                }
            }
            assert!(set1.is_proper_subset(&set2) == test.3);
        }
    }

    #[test]
    fn test_is_superset() {
        let max = TEST_STRS.len();
        for test in &[
            ((0, 7), (7, max), false, false),
            ((7, max), (5, max), false, false),
            ((5, max), (7, max), true, true),
            ((1, 7), (1, 7), true, false),
            ((0, 9), (5, max), false, false),
            ((1, max), (1, 7), true, true),
        ] {
            println!("TEST: {:?}", test); // to help identify failed tests
            let set1: OrderedSet<String> = TEST_STRS[(test.0).0..(test.0).1]
                .into_iter()
                .map(|s| s.to_string())
                .collect();
            let set2: OrderedSet<String> = TEST_STRS[(test.1).0..(test.1).1]
                .into_iter()
                .map(|s| s.to_string())
                .collect();
            assert!(set1.is_superset(&set2) == test.2);
            if set1.is_superset(&set2) {
                for item in set2.iter() {
                    assert!(set1.contains(item));
                }
            }
            assert!(set1.is_proper_superset(&set2) == test.3);
        }
    }

    #[test]
    fn test_difference() {
        let str_set1: OrderedSet<String> =
            TEST_STRS[0..8].into_iter().map(|s| s.to_string()).collect();
        let str_set2: OrderedSet<String> =
            TEST_STRS[4..].into_iter().map(|s| s.to_string()).collect();
        let expected: OrderedSet<String> =
            TEST_STRS[0..4].into_iter().map(|s| s.to_string()).collect();
        let result = &str_set1 - &str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
        let result = str_set1 - str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
    }

    #[test]
    fn test_symmetric_difference() {
        let str_set1: OrderedSet<String> =
            TEST_STRS[0..8].into_iter().map(|s| s.to_string()).collect();
        let str_set2: OrderedSet<String> =
            TEST_STRS[4..].into_iter().map(|s| s.to_string()).collect();
        let mut expected: OrderedSet<String> =
            TEST_STRS[0..4].into_iter().map(|s| s.to_string()).collect();
        for item in TEST_STRS[8..].into_iter().map(|s| s.to_string()) {
            expected.insert(item);
        }
        let result = &str_set1 ^ &str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
        let result = str_set1 ^ str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
    }

    #[test]
    fn test_union() {
        let str_set1: OrderedSet<String> =
            TEST_STRS[0..8].into_iter().map(|s| s.to_string()).collect();
        let str_set2: OrderedSet<String> =
            TEST_STRS[4..].into_iter().map(|s| s.to_string()).collect();
        let expected: OrderedSet<String> =
            TEST_STRS[0..].into_iter().map(|s| s.to_string()).collect();
        let result = &str_set1 | &str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
        let result = str_set1 | str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
    }

    #[test]
    fn test_intersection() {
        let str_set1: OrderedSet<String> =
            TEST_STRS[0..8].into_iter().map(|s| s.to_string()).collect();
        let str_set2: OrderedSet<String> =
            TEST_STRS[4..].into_iter().map(|s| s.to_string()).collect();
        let expected: OrderedSet<String> =
            TEST_STRS[4..8].into_iter().map(|s| s.to_string()).collect();
        let result = &str_set1 & &str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
        let result = str_set1 & str_set2;
        assert!(result.is_valid());
        assert_eq!(expected, result);
    }
}
