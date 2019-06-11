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

use std::convert::From;
use std::default::Default;
use std::slice::{Iter, IterMut};
use std::vec::Drain;

use crate::iterators::{MapIter, MapMergeIter, SetConversion, SetOperations};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OrderedMap<K: Ord, V> {
    ordered_list: Vec<(K, V)>,
}

impl<K: Ord, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        Self {
            ordered_list: vec![],
        }
    }
}

impl<K: Ord, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return true if ordered_list is sorted and contains no duplicate keys
    pub fn is_valid(&self) -> bool {
        for i in 1..self.ordered_list.len() {
            if self.ordered_list[i - 1].0 >= self.ordered_list[i].0 {
                return false;
            }
        }
        true
    }

    /// Return the number of items in this set.
    pub fn len(&self) -> usize {
        self.ordered_list.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ordered_list.len() == 0
    }

    pub fn capacity(&self) -> usize {
        self.ordered_list.capacity()
    }

    pub fn clear(&mut self) {
        self.ordered_list.clear()
    }

    fn get_index_for(&self, key: &K) -> Result<usize, usize> {
        self.ordered_list.binary_search_by(|k| k.0.cmp(key))
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.get_index_for(key).is_ok()
    }

    pub fn drain(&mut self) -> Drain<(K, V)> {
        self.ordered_list.drain(..)
    }

    pub fn iter(&self) -> MapIter<K, V, Iter<(K, V)>> {
        MapIter::new(self.ordered_list.iter())
    }

    pub fn merge<'a>(
        &'a self,
        other: &'a Self,
    ) -> MapMergeIter<'a, K, V, Iter<(K, V)>, Iter<(K, V)>> {
        MapMergeIter::new(self.ordered_list.iter(), other.ordered_list.iter())
    }

    fn iter_mut(&mut self) -> IterMut<(K, V)> {
        self.ordered_list.iter_mut()
    }

    pub fn iter_after(&self, key: &K) -> Iter<(K, V)> {
        match self.get_index_for(key) {
            Ok(index) => self.ordered_list[index + 1..].iter(),
            Err(index) => self.ordered_list[index..].iter(),
        }
    }

    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            iter: self.ordered_list.iter(),
        }
    }

    pub fn values(&self) -> Values<K, V> {
        Values {
            iter: self.ordered_list.iter(),
        }
    }

    pub fn values_mut<'a>(&'a mut self) -> ValuesMut<'a, K, V> {
        ValuesMut {
            iter_mut: self.iter_mut(),
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        if let Ok(index) = self.get_index_for(key) {
            Some(&self.ordered_list.get(index).unwrap().1)
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Ok(index) = self.get_index_for(key) {
            Some(&mut self.ordered_list.get_mut(index).unwrap().1)
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.get_index_for(&key) {
            Ok(index) => {
                let old = self.ordered_list.remove(index);
                self.ordered_list.insert(index, (key, value));
                Some(old.1)
            }
            Err(index) => {
                self.ordered_list.insert(index, (key, value));
                None
            }
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        match self.get_index_for(&key) {
            Ok(index) => Some(self.ordered_list.remove(index).1),
            Err(_) => None,
        }
    }
}
/// Convert to OrderedMap<K, V> from ordered Vec<(K, V)> with no duplicates
impl<K: Ord, V> From<Vec<(K, V)>> for OrderedMap<K, V> {
    fn from(ordered_list: Vec<(K, V)>) -> Self {
        let list = Self { ordered_list };
        assert!(list.is_valid());
        list
    }
}

pub struct Keys<'a, K, V> {
    iter: Iter<'a, (K, V)>,
}

impl<'a, K: Ord, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((key, _)) = self.iter.next() {
            return Some(key);
        } else {
            None
        }
    }
}

impl<'a, K, V, I> SetOperations<'a, K, I> for Keys<'a, K, V>
where
    K: 'a + Ord,
    I: Iterator<Item = &'a K>,
{
}

impl<'a, K, V> SetConversion<'a, K> for Keys<'a, K, V> where K: 'a + Ord + Clone {}

pub struct Values<'a, K, V> {
    iter: Iter<'a, (K, V)>,
}

impl<'a, K: Ord, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, value)) = self.iter.next() {
            return Some(value);
        } else {
            None
        }
    }
}

pub struct ValuesMut<'a, K: Ord, V> {
    iter_mut: IterMut<'a, (K, V)>,
}

impl<'a, K: Ord, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, value)) = self.iter_mut.next() {
            return Some(value);
        } else {
            None
        }
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
