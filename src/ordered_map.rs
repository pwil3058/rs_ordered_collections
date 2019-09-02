use std::borrow::Borrow;
use std::convert::From;
use std::default::Default;
use std::ops::{Index, IndexMut};
use std::vec;

pub mod map_entry;
pub mod ord_map_iterators;

pub use self::map_entry::*;

pub use self::ord_map_iterators::{
    MapDrain, MapIter, MapIterFilter, MapIterMerge, MapIterMut, MapIterMutFilter, MapIterMutMerge,
    MapMergeIter, MapMergeIterMut, ToMap, ValueIter, ValueIterMut,
};

pub use crate::ordered_set::ord_set_iterators::{
    Difference, Intersection, SetIter, SymmetricDifference, Union,
};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OrderedMap<K: Ord, V> {
    pub(crate) keys: Vec<K>,
    pub(crate) values: Vec<V>,
}

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

    // Return true if keys is sorted and contains no duplicate keys
    // and the same length as values.
    #[cfg(test)]
    pub(crate) fn is_valid(&self) -> bool {
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

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.keys.binary_search_by_key(&key, |x| x.borrow()).is_ok()
    }

    pub fn drain<Q, R>(&mut self, range: R) -> MapDrain<K, V>
    where
        Q: Ord + Sized,
        R: std::ops::RangeBounds<Q>,
        K: Borrow<Q>,
    {
        let (start_index, end_index) = super::range_indices(&self.keys, range);
        MapDrain::new(
            self.keys.drain(start_index..end_index),
            self.values.drain(start_index..end_index),
        )
    }

    pub fn iter(&self) -> MapIter<'_, K, V> {
        MapIter::new(&self.keys, &self.values)
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

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Ok(index) = self.keys.binary_search_by_key(&key, |x| x.borrow()) {
            Some(&self.values[index])
        } else {
            None
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Ok(index) = self.keys.binary_search_by_key(&key, |x| x.borrow()) {
            Some(&mut self.values[index])
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.keys.binary_search(&key) {
            Ok(index) => {
                self.values.push(value);
                Some(self.values.swap_remove(index))
            }
            Err(index) => {
                self.keys.insert(index, key);
                self.values.insert(index, value);
                None
            }
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.keys.binary_search_by_key(&key, |x| x.borrow()) {
            Ok(index) => {
                self.keys.remove(index);
                Some(self.values.remove(index))
            }
            Err(_) => None,
        }
    }

    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.keys.binary_search_by_key(&key, |x| x.borrow()) {
            Ok(index) => Some((self.keys.remove(index), self.values.remove(index))),
            Err(_) => None,
        }
    }
}

/// Convert to OrderedMap<K, V> from a Vec<(K, V)>
impl<K: Ord, V> From<Vec<(K, V)>> for OrderedMap<K, V> {
    fn from(mut list: Vec<(K, V)>) -> Self {
        let mut map = Self::default();
        for (key, value) in list.drain(..) {
            map.insert(key, value);
        }
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
        map
    }
}

impl<K: Ord, V> Index<K> for OrderedMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        if let Ok(index) = self.keys.binary_search(&key) {
            &self.values[index]
        } else {
            panic!("Unknown key")
        }
    }
}

impl<K: Ord, V> IndexMut<K> for OrderedMap<K, V> {
    fn index_mut<'a>(&'a mut self, key: K) -> &'a mut Self::Output {
        if let Ok(index) = self.keys.binary_search(&key) {
            &mut self.values[index]
        } else {
            panic!("Unknown key")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordered_set::ord_set_iterators::{ToList, ToSet};
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
    fn contains_key() {
        let map = OrderedMap::<String, u32>::default();
        let anything = "anything".to_string();
        assert!(!map.contains_key(&anything));
        assert!(!map.contains_key("whatever"));
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

    #[test]
    fn drain_map() {
        let mut map1: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0.into();
        let keys_before = map1.keys().to_set();
        let list: Vec<(&str, (&str, u32))> = map1.drain("ccc".."iii").collect();
        let map2: OrderedMap<&str, (&str, u32)> = list.into();
        assert_eq!(
            map2.keys().to_list(),
            vec!["ccc", "ddd", "eee", "fff", "ggg", "hhh"]
        );
        let keys_after = map1.keys().to_set();
        assert_eq!(keys_after, keys_before - map2.keys().to_set());
    }

    #[test]
    fn map_borrow_functionality() {
        let mut map = OrderedMap::<String, (&str, u32)>::default();
        for (key, value) in TEST_ITEMS_0.iter() {
            println!("{:?} => {:?}", key, value);
            assert!(map.insert(key.to_string(), *value).is_none());
            assert!(map.is_valid());
            assert_eq!(map.get(*key), Some(value));
            assert_eq!(map.insert(key.to_string(), *value), Some(*value));
            assert!(map.is_valid());
        }
        let mut hash_map = HashMap::<String, (&str, u32)>::new();
        for (key, value) in TEST_ITEMS_0.iter() {
            assert!(hash_map.insert(key.to_string(), *value).is_none());
        }
        for (key, value) in TEST_ITEMS_1.iter() {
            if let Some(old_value) = hash_map.get(*key) {
                assert_eq!(map.insert(key.to_string(), *value), Some(*old_value));
                assert!(map.is_valid());
                assert_eq!(map.get(*key), Some(value));
            } else {
                assert!(false);
            }
        }
    }

    #[test]
    fn map_merge_basic() {
        let map1: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[..5].into();
        let map2: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[5..].into();
        let merged = map1.iter().merge(map2.iter()).to_map();
        assert_eq!(map1.len() + map2.len(), merged.len());
        assert!(merged.is_valid());
        let merged = (map1.iter() | map2.iter()).to_map();
        assert_eq!(map1.len() + map2.len(), merged.len());
        assert!(merged.is_valid());
    }

    #[test]
    fn map_merge_except() {
        let map1: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[..5].into();
        let map2: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[5..].into();
        let merged = map1
            .iter()
            .merge(map2.iter())
            .except(SetIter::new(&["bbb", "lll", "mmm"]))
            .to_map();
        assert_eq!(map1.len() + map2.len(), merged.len() + 3);
        assert!(merged.is_valid());
    }

    #[test]
    fn map_merge_only() {
        let map1: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[..5].into();
        let map2: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[5..].into();
        let merged = map1
            .iter()
            .merge(map2.iter())
            .only(SetIter::new(&["bbb", "lll", "mmm"]))
            .to_map();
        assert_eq!(3, merged.len());
        assert!(merged.is_valid());
    }

    #[test]
    #[should_panic]
    fn map_merge_overlap_panic() {
        let map1: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[..5].into();
        let map2: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[3..].into();
        let _merged = map1.iter().merge(map2.iter()).to_map();
    }

    #[test]
    #[should_panic]
    fn map_merge_mut_overlap_panic() {
        let mut map1: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[..5].into();
        let mut map2: OrderedMap<&str, (&str, u32)> = TEST_ITEMS_0[3..].into();
        for (_, _) in map1.iter_mut().merge(map2.iter_mut()) {}
    }
}
