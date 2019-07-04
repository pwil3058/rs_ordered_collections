use std::convert::From;
use std::default::Default;

use crate::iter_ops::*;
use crate::ordered_iterators::*;

use crate::OrderedMap;

impl<K: Ord, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        Self {
            keys: vec![],
            values: vec![],
        }
    }
}

impl<K: Ord, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return true if keys is sorted and contains no duplicate keys
    /// and the same length as values.
    pub fn is_valid(&self) -> bool {
        for i in 1..self.keys.len() {
            if self.keys[i - 1] >= self.keys[i] {
                return false;
            }
        }
        self.keys.len() == self.values.len()
    }

    /// Return the number of items in this set.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.keys.len() == 0
    }

    pub fn capacity(&self) -> usize {
        self.keys.capacity().min(self.values.capacity())
    }

    pub fn clear(&mut self) {
        self.keys.clear();
        self.values.clear();
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.keys.binary_search(key).is_ok()
    }

    // TODO: implement a useful drain for OrderedMap
    //pub fn drain(&mut self) -> Drain<(K, V)> {
    //    self.keys.drain(..)
    //}

    pub fn iter(&self) -> MapIter<'_, K, V> {
        MapIter::new(&self.keys, &self.values)
    }

    pub fn merge<'a>(
        &'a self,
        other: &'a Self,
    ) -> MapMergeIter<'a, K, V, MapIter<'_, K, V>, MapIter<'_, K, V>> {
        MapMergeIter::new(self.iter(), other.iter())
    }

    pub fn iter_mut(&mut self) -> MapIterMut<'_, K, V> {
        MapIterMut::new(&self.keys, &mut self.values)
    }

    pub fn keys(&self) -> SetIter<'_, K> {
        SetIter::new(&self.keys)
    }

    pub fn values(&self) -> ValueIter<'_, K, V> {
        ValueIter::new(&self.keys, &self.values)
    }

    pub fn values_mut(&mut self) -> ValueIterMut<'_, K, V> {
        ValueIterMut::new(&self.keys, &mut self.values)
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        if let Ok(index) = self.keys.binary_search(key) {
            Some(&self.values[index])
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Ok(index) = self.keys.binary_search(key) {
            Some(&mut self.values[index])
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.keys.binary_search(&key) {
            Ok(index) => {
                let old = self.values.remove(index);
                self.values.insert(index, value);
                Some(old)
            }
            Err(index) => {
                self.keys.insert(index, key);
                self.values.insert(index, value);
                None
            }
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        match self.keys.binary_search(&key) {
            Ok(index) => {
                self.keys.remove(index);
                Some(self.values.remove(index))
            }
            Err(_) => None,
        }
    }

    /// Iterate over the set union of the keys of this OrderedMap and
    /// and the keys the given OrderedMap in the order defined their
    /// elements Ord trait implementation.
    pub fn keys_union<'a>(
        &'a self,
        other: &'a Self,
    ) -> Union<'a, K, SetIter<'a, K>, SetIter<'a, K>> {
        Union::new(self.keys(), other.keys())
    }

    /// Iterate over the set intersection of the keys of this OrderedMap and
    /// and the keys the given OrderedMap in the order defined their
    /// elements Ord trait implementation.
    pub fn keys_intersection<'a>(
        &'a self,
        other: &'a Self,
    ) -> Intersection<'a, K, SetIter<'a, K>, SetIter<'a, K>> {
        Intersection::new(self.keys(), other.keys())
    }

    /// Iterate over the set difference of the keys of this OrderedMap and
    /// and the keys the given OrderedMap in the order defined their
    /// elements Ord trait implementation.
    pub fn keys_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Difference<'a, K, SetIter<'a, K>, SetIter<'a, K>> {
        Difference::new(self.keys(), other.keys())
    }

    /// Iterate over the set symmetric difference of the keys of this OrderedMap and
    /// and the keys the given OrderedMap in the order defined their
    /// elements Ord trait implementation.
    pub fn keys_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> SymmetricDifference<'a, K, SetIter<'a, K>, SetIter<'a, K>> {
        SymmetricDifference::new(self.keys(), other.keys())
    }

    /// Are the keys of the given OrderedMap disjoint from the keys of
    /// this OrderedMapr?
    pub fn is_keys_disjoint(&self, other: &Self) -> bool {
        are_disjoint(self.keys(), other.keys())
    }

    /// Are the keys of the given OrderedMap a proper subset o the keys of
    /// this OrderedMapr?
    pub fn is_keys_proper_subset(&self, other: &Self) -> bool {
        a_proper_superset_b(self.keys(), other.keys())
    }

    /// Are the keys of the given OrderedMap a proper superset o the keys of
    /// this OrderedMapr?
    pub fn is_keys_proper_superset(&self, other: &Self) -> bool {
        a_proper_superset_b(other.keys(), self.keys())
    }

    /// Are the keys of the given OrderedMap subset of the keys of
    /// this OrderedMapr?
    pub fn is_keys_subset(&self, other: &Self) -> bool {
        a_superset_b(self.keys(), other.keys())
    }

    /// Are the keys of the given OrderedMap superset of the keys of
    /// this OrderedMapr?
    pub fn is_keys_superset(&self, other: &Self) -> bool {
        a_superset_b(other.keys(), self.keys())
    }
}

/// Convert to OrderedMap<K, V> from a Vec<(K, V)>
impl<K: Ord, V> From<Vec<(K, V)>> for OrderedMap<K, V> {
    fn from(mut list: Vec<(K, V)>) -> Self {
        let mut map = Self::default();
        for (key, value) in list.drain(..) {
            map.insert(key, value);
        }
        assert!(map.is_valid());
        map
    }
}

/// Convert to OrderedMap<K, V> from a Vec<(K, V)>
impl<K: Ord + Clone, V: Clone> From<&[(K, V)]> for OrderedMap<K, V> {
    fn from(list: &[(K, V)]) -> Self {
        let mut map = Self::default();
        for (key, value) in list.iter() {
            map.insert(key.clone(), value.clone());
        }
        assert!(map.is_valid());
        map
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    static TEST_ITEMS_0: &[(&str, (&str, u32))] = &[
        ("hhh", ("HHH", 0)),
        ("aaa", ("AAA", 0)),
        ("ggg", ("GGG", 0)),
        ("sss", ("SSS", 0)),
        ("zzz", ("ZZZ", 0)),
        ("bbb", ("BBB", 0)),
        ("fff", ("FFF", 0)),
        ("iii", ("III", 0)),
        ("qqq", ("QQQ", 0)),
        ("jjj", ("JJJ", 0)),
        ("ddd", ("DDD", 0)),
        ("eee", ("EEE", 0)),
        ("ccc", ("CCC", 0)),
        ("mmm", ("MMM", 0)),
        ("lll", ("LLL", 0)),
        ("nnn", ("NNN", 0)),
        ("ppp", ("PPP", 0)),
        ("rrr", ("RRR", 0)),
    ];

    static TEST_ITEMS_1: &[(&str, (&str, u32))] = &[
        ("hhh", ("HHH", 1)),
        ("aaa", ("AAA", 1)),
        ("ggg", ("GGG", 1)),
        ("sss", ("SSS", 1)),
        ("zzz", ("ZZZ", 1)),
        ("bbb", ("BBB", 1)),
        ("fff", ("FFF", 1)),
        ("iii", ("III", 1)),
        ("qqq", ("QQQ", 1)),
        ("jjj", ("JJJ", 1)),
        ("ddd", ("DDD", 1)),
        ("eee", ("EEE", 1)),
        ("ccc", ("CCC", 1)),
        ("mmm", ("MMM", 1)),
        ("lll", ("LLL", 1)),
        ("nnn", ("NNN", 1)),
        ("ppp", ("PPP", 1)),
        ("rrr", ("RRR", 1)),
    ];

    #[test]
    fn map_default_works() {
        let map = OrderedMap::<u32, u32>::default();
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
    }

    #[test]
    fn map_basic_functionality() {
        let mut map = OrderedMap::<&str, (&str, u32)>::default();
        for (key, value) in TEST_ITEMS_0.iter() {
            println!("{:?} => {:?}", key, value);
            assert!(map.insert(key, *value).is_none());
            assert!(map.is_valid());
            assert_eq!(map.get(key), Some(value));
            assert_eq!(map.insert(key, *value), Some(*value));
            assert!(map.is_valid());
        }
        let mut hash_map = HashMap::<&str, (&str, u32)>::new();
        for (key, value) in TEST_ITEMS_0.iter() {
            assert!(hash_map.insert(key, *value).is_none());
        }
        for (key, value) in TEST_ITEMS_1.iter() {
            if let Some(old_value) = hash_map.get(key) {
                assert_eq!(map.insert(key, *value), Some(*old_value));
                assert!(map.is_valid());
                assert_eq!(map.get(key), Some(value));
            } else {
                assert!(false);
            }
        }
    }
}
