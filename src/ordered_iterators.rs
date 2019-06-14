// Copyright 2019 Peter Williams <pwil3058@gmail.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// Iterator enhancements for ordered colletions without duplicates
pub trait OrderedIterator<'a, T: 'a + Ord>: Iterator<Item = &'a T> {
    /// Return the next item in the iterator whose value is greater than the given value
    fn next_after(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value > target {
                return Some(value);
            }
        }
        None
    }

    /// Return the next item in the iterator whose value is less than the given value
    fn next_before(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value < target {
                return Some(value);
            }
        }
        None
    }

    /// Return the next item in the iterator whose value is greater than or equal to the given value
    fn next_from(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value >= target {
                return Some(value);
            }
        }
        None
    }

    /// Return the next item in the iterator whose value is less than or equal to the given value
    fn next_until(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value <= target {
                return Some(value);
            }
        }
        None
    }
}

// SET ITERATOR

/// An Iterator over the items in an ordered list
pub struct SetIter<'a, T: Ord> {
    ordered_list: &'a Vec<T>,
    index: usize,
}

impl<'a, T: Ord> SetIter<'a, T> {
    pub fn new(ordered_list: &'a Vec<T>) -> Self {
        Self {
            ordered_list,
            index: 0,
        }
    }
}

impl<'a, T: Ord> Iterator for SetIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for SetIter<'a, T> {
    fn next_from(&mut self, t: &T) -> Option<&'a T> {
        self.index += match self.ordered_list[self.index..].binary_search(t) {
            Ok(index) => index,
            Err(index) => index,
        };
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }

    fn next_after(&mut self, t: &T) -> Option<&'a T> {
        self.index += match self.ordered_list[self.index..].binary_search(t) {
            Ok(index) => index + 1,
            Err(index) => index,
        };
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

/// An Iterator over the items in an ordered list after a given value
pub struct SetIterAfter<'a, T: 'a + Ord> {
    set_iter: SetIter<'a, T>,
}

impl<'a, T: 'a + Ord> SetIterAfter<'a, T> {
    pub fn new(ordered_list: &'a Vec<T>, t: &T) -> Self {
        let mut set_iter = SetIter::new(ordered_list);
        set_iter.index += match set_iter.ordered_list.binary_search(t) {
            Ok(index) => index + 1,
            Err(index) => index,
        };
        Self { set_iter }
    }
}

impl<'a, T: Ord> Iterator for SetIterAfter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next()
    }
}

impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for SetIterAfter<'a, T> {}

/// An Iterator over the items in an ordered list before a given value
pub struct SetIterBefore<'a, T: 'a + Ord> {
    set_iter: SetIter<'a, T>,
    limit: &'a T,
}

impl<'a, T: 'a + Ord> SetIterBefore<'a, T> {
    pub fn new(ordered_list: &'a Vec<T>, t: &'a T) -> Self {
        Self {
            set_iter: SetIter::new(ordered_list),
            limit: t,
        }
    }
}

impl<'a, T: Ord> Iterator for SetIterBefore<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next_before(self.limit)
    }
}

impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for SetIterBefore<'a, T> {}

/// An Iterator over the items in an ordered list from a given value
pub struct SetIterFrom<'a, T: 'a + Ord> {
    set_iter: SetIter<'a, T>,
}

impl<'a, T: 'a + Ord> SetIterFrom<'a, T> {
    pub fn new(ordered_list: &'a Vec<T>, t: &T) -> Self {
        let mut set_iter = SetIter::new(ordered_list);
        set_iter.index += match set_iter.ordered_list.binary_search(t) {
            Ok(index) => index,
            Err(index) => index,
        };
        Self { set_iter }
    }
}

impl<'a, T: Ord> Iterator for SetIterFrom<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next()
    }
}

impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for SetIterFrom<'a, T> {}

/// An Iterator over the items in an ordered list until a given value
pub struct SetIterUntil<'a, T: 'a + Ord> {
    set_iter: SetIter<'a, T>,
    limit: &'a T,
}

impl<'a, T: 'a + Ord> SetIterUntil<'a, T> {
    pub fn new(ordered_list: &'a Vec<T>, t: &'a T) -> Self {
        Self {
            set_iter: SetIter::new(ordered_list),
            limit: t,
        }
    }
}

impl<'a, T: Ord> Iterator for SetIterUntil<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next_until(self.limit)
    }
}

impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for SetIterUntil<'a, T> {}

// MAP ITERATOR

#[derive(Clone, Debug, Hash, PartialEq, Eq, Ord)]
struct KeyValuePair<K: Ord, V>(K, V);

/// An Iterator over the items in an ordered map
pub struct MapIter<'a, K: Ord, V> {
    ordered_list: &'a Vec<(K, V)>,
    index: usize,
}

impl<'a, K: Ord, V> MapIter<'a, K, V> {
    pub fn new(ordered_list: &'a Vec<(K, V)>) -> Self {
        Self {
            ordered_list,
            index: 0,
        }
    }
}

impl<'a, K: Ord, V> Iterator for MapIter<'a, K, V> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<'a, K: 'a + Ord, V> OrderedIterator<'a, (K, V)> for MapIter<'a, K, V> {
    fn next_from(&mut self, k: &K) -> Option<&'a (K, V)> {
        self.index += match self.ordered_list[self.index..].binary_search(k) {
            Ok(index) => index,
            Err(index) => index,
        };
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }

    fn next_after(&mut self, k: &K) -> Option<&'a (K, V)> {
        self.index += match self.ordered_list[self.index..].binary_search(k) {
            Ok(index) => index + 1,
            Err(index) => index,
        };
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

/// An Iterator over the items in an ordered map after a given key
pub struct MapIterAfter<'a, K: 'a + Ord, V> {
    set_iter: MapIter<'a, K, V>,
}

impl<'a, K: 'a + Ord, V> MapIterAfter<'a, K, V> {
    pub fn new(ordered_list: &'a Vec<(K, V)>, k: &K) -> Self {
        let mut set_iter = MapIter::new(ordered_list);
        set_iter.index += match set_iter.ordered_list.binary_search(k) {
            Ok(index) => index + 1,
            Err(index) => index,
        };
        Self { set_iter }
    }
}

impl<'a, K: Ord, V> Iterator for MapIterAfter<'a, K, V> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next()
    }
}

//impl<'a, K: 'a + Ord, V>  OrderedIterator<'a, (K, V)> for MapIterAfter<'a, K, V> {}

/// An Iterator over the items in an ordered map before a given key
pub struct MapIterBefore<'a, K: 'a + Ord, V> {
    set_iter: MapIter<'a, K, V>,
    limit: &'a K,
}

impl<'a, K: 'a + Ord, V> MapIterBefore<'a, K, V> {
    pub fn new(ordered_list: &'a Vec<(K, V)>, k: &'a K) -> Self {
        Self {
            set_iter: MapIter::new(ordered_list),
            limit: k,
        }
    }
}

impl<'a, K: Ord, V> Iterator for MapIterBefore<'a, K, V> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next_before(self.limit)
    }
}

//impl<'a, K: 'a + Ord, V> OrderedIterator<'a, (K, V)> for MapIterBefore<'a, K, V> {}

/// An Iterator over the items in an ordered map from a given key
pub struct MapIterFrom<'a, K: 'a + Ord, V> {
    set_iter: MapIter<'a, K, V>,
}

impl<'a, K: 'a + Ord, V> MapIterFrom<'a, K, V> {
    pub fn new(ordered_list: &'a Vec<(K, V)>, k: &K) -> Self {
        let mut set_iter = MapIter::new(ordered_list);
        set_iter.index += match set_iter.ordered_list.binary_search(k) {
            Ok(index) => index,
            Err(index) => index,
        };
        Self { set_iter }
    }
}

impl<'a, K: Ord, V> Iterator for MapIterFrom<'a, K, V> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next()
    }
}

//impl<'a, K: 'a + Ord, V> OrderedIterator<'a, (K, V)> for MapIterFrom<'a, K, V> {}

/// An Iterator over the items in an ordered map until a given key
pub struct MapIterUntil<'a, K: 'a + Ord, V> {
    set_iter: MapIter<'a, K, V>,
    limit: &'a K,
}

impl<'a, K: 'a + Ord, V> MapIterUntil<'a, K, V> {
    pub fn new(ordered_list: &'a Vec<(K, V)>, k: &'a K) -> Self {
        Self {
            set_iter: MapIter::new(ordered_list),
            limit: k,
        }
    }
}

impl<'a, K: Ord, V> Iterator for MapIterUntil<'a, K, V> {
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.set_iter.next_until(self.limit)
    }
}

//impl<'a, K: 'a + Ord, V> OrderedIterator<'a, (K, V)> for MapIterUntil<'a, K, V> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::slice::Iter;

    impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for Iter<'a, T> {}

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];

    #[test]
    fn next_before_works() {
        assert_eq!(LIST.iter().next_before(&"g"), Some(&"a"));
        assert_eq!(LIST.iter().next_before(&"a"), None);
        let mut iter = LIST.iter();
        assert_eq!(iter.next_before(&"c"), Some(&"a"));
        assert_eq!(iter.next_before(&"c"), None);
    }

    #[test]
    fn next_until_works() {
        assert_eq!(LIST.iter().next_until(&"g"), Some(&"a"));
        assert_eq!(LIST.iter().next_until(&"a"), Some(&"a"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_until(&"a"), Some(&"a"));
        assert_eq!(iter.next_until(&"a"), None);
    }

    #[test]
    fn next_from_works() {
        assert_eq!(LIST.iter().next_from(&"g"), Some(&"g"));
        assert_eq!(LIST.iter().next_from(&"a"), Some(&"a"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_from(&"m"), Some(&"m"));
        assert_eq!(iter.next_from(&"m"), None);
    }

    #[test]
    fn next_after_works() {
        assert_eq!(LIST.iter().next_after(&"g"), Some(&"i"));
        assert_eq!(LIST.iter().next_after(&"a"), Some(&"c"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_after(&"k"), Some(&"m"));
        assert_eq!(iter.next_after(&"k"), None);
    }

    #[test]
    fn set_iter_works() {
        let vec = LIST.to_vec();
        let set_iter = SetIter::new(&vec);
        let result: Vec<&str> = set_iter.cloned().collect();
        assert_eq!(result, vec);
        let mut set_iter = SetIter::new(&vec);
        assert_eq!(set_iter.next_after(&"g"), Some(&"i"));
        let result: Vec<&str> = set_iter.cloned().collect();
        assert_eq!(result, vec[5..].to_vec());
        let mut set_iter = SetIter::new(&vec);
        assert_eq!(set_iter.next_from(&"g"), Some(&"g"));
        let result: Vec<&str> = set_iter.cloned().collect();
        assert_eq!(result, vec[4..].to_vec());
    }

    #[test]
    fn iter_after_works() {
        let vec = LIST.to_vec();
        let iter_after = SetIterAfter::new(&vec, &"g");
        let result: Vec<&str> = iter_after.cloned().collect();
        assert_eq!(result, vec[4..].to_vec());
        let iter_after = SetIterAfter::new(&vec, &"f");
        let result: Vec<&str> = iter_after.cloned().collect();
        assert_eq!(result, vec[3..].to_vec());
    }

    #[test]
    fn iter_before_works() {
        let vec = LIST.to_vec();
        let iter_before = SetIterBefore::new(&vec, &"g");
        let result: Vec<&str> = iter_before.cloned().collect();
        assert_eq!(result, vec[..3].to_vec());
        let iter_before = SetIterBefore::new(&vec, &"f");
        let result: Vec<&str> = iter_before.cloned().collect();
        assert_eq!(result, vec[..3].to_vec());
    }

    #[test]
    fn iter_from_works() {
        let vec = LIST.to_vec();
        let iter_from = SetIterFrom::new(&vec, &"g");
        let result: Vec<&str> = iter_from.cloned().collect();
        assert_eq!(result, vec[3..].to_vec());
        let iter_from = SetIterFrom::new(&vec, &"f");
        let result: Vec<&str> = iter_from.cloned().collect();
        assert_eq!(result, vec[3..].to_vec());
    }

    #[test]
    fn iter_until_works() {
        let vec = LIST.to_vec();
        let iter_until = SetIterUntil::new(&vec, &"g");
        let result: Vec<&str> = iter_until.cloned().collect();
        assert_eq!(result, vec[..4].to_vec());
        let iter_until = SetIterUntil::new(&vec, &"f");
        let result: Vec<&str> = iter_until.cloned().collect();
        assert_eq!(result, vec[..3].to_vec());
    }
}
