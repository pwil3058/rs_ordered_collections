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

/// Iterator enhancement to provide a skip ahead feature. This mechanism
/// is used to optimise implementation of set operation (difference, intersection, etc)
/// iterators. NB the default implementations do not provide any performance
/// enhancement and are only provided so that algorithms that use these
/// functions will still work.
pub trait SkipAheadIterator<'a, T: 'a + Ord>: Iterator<Item = &'a T> {
    /// Return the next item in the iterator whose value is greater than
    /// to the given value.
    fn next_after(&mut self, target: &T) -> Option<Self::Item> {
        while let Some(item) = self.next() {
            if item > target {
                return Some(item);
            }
        }
        None
    }

    /// Return the next item in the iterator whose value is greater than
    /// or equal to the given value.  Used to optimise set operation
    /// iterators.
    fn next_from(&mut self, target: &T) -> Option<Self::Item> {
        while let Some(item) = self.next() {
            if item >= target {
                return Some(item);
            }
        }
        None
    }
}

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

macro_rules! tuple_after_index {
    ( $list:expr, $target:expr ) => {
        match $list.binary_search_by(|x| x.0.cmp($target)) {
            Ok(index) => index + 1,
            Err(index) => index,
        }
    };
}

macro_rules! tuple_from_index {
    ( $list:expr, $target:expr ) => {
        match $list.binary_search_by(|x| x.0.cmp($target)) {
            Ok(index) => index,
            Err(index) => index,
        }
    };
}

// SET ITERATOR

/// An Iterator over the items in an ordered list
pub struct SetIter<'a, T: Ord> {
    ordered_list: &'a[T],
    index: usize,
}

impl<'a, T: Ord> SetIter<'a, T> {
    pub fn new(ordered_list: &'a[T]) -> Self {
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

impl<'a, T: 'a + Ord> SkipAheadIterator<'a, T> for SetIter<'a, T> {
    fn next_after(&mut self, t: &T) -> Option<&'a T> {
        self.index += after_index!(self.ordered_list[self.index..], t);
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }

    fn next_from(&mut self, t: &T) -> Option<&'a T> {
        self.index += from_index!(self.ordered_list[self.index..], t);
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

// MAP ITERATOR

/// Iterator enhancement to provide a skip ahead feature. This mechanism
/// is used to optimise implementation of set operation (difference, intersection, etc)
/// iterators. NB the default implementations do not provide any performance
/// enhancement and are only provided so that algorithms that use these
/// functions will still work.
pub trait SkipAheadMapIterator<'a, K: 'a + Ord, V: 'a>: Iterator<Item = &'a (K, V)> {
    /// Return the next item in the iterator whose value is greater than
    /// to the given value.
    fn next_after(&mut self, target: &K) -> Option<Self::Item> {
        while let Some(item) = self.next() {
            if &item.0 > target {
                return Some(item);
            }
        }
        None
    }

    /// Return the next item in the iterator whose value is greater than
    /// or equal to the given value.  Used to optimise set operation
    /// iterators.
    fn next_from(&mut self, target: &K) -> Option<Self::Item> {
        while let Some(item) = self.next() {
            if &item.0 >= target {
                return Some(item);
            }
        }
        None
    }
}

/// An Iterator over the items in an ordered map
pub struct MapIter<'a, K: Ord, V> {
    ordered_list: &'a [(K, V)],
    index: usize,
}

impl<'a, K: Ord, V> MapIter<'a, K, V> {
    pub fn new(ordered_list: &'a [(K, V)]) -> Self {
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

impl<'a, K: 'a + Ord, V> SkipAheadMapIterator<'a, K, V> for MapIter<'a, K, V> {
    fn next_after(&mut self, k: &K) -> Option<&'a (K, V)> {
        self.index += tuple_after_index!(self.ordered_list[self.index..], k);
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }

    fn next_from(&mut self, k: &K) -> Option<&'a (K, V)> {
        self.index += tuple_from_index!(self.ordered_list[self.index..], k);
        if let Some(item) = self.ordered_list.get(self.index) {
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::slice::Iter;

    impl<'a, T: 'a + Ord> SkipAheadIterator<'a, T> for Iter<'a, T> {}

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static MAP: &[(&str, i32)] = &[
        ("a", 6),
        ("c", 5),
        ("e", 4),
        ("g", 3),
        ("i", 2),
        ("k", 1),
        ("m", 0),
    ];

    #[test]
    fn defaul_next_from_works() {
        assert_eq!(LIST.iter().next_from(&"g"), Some(&"g"));
        assert_eq!(LIST.iter().next_from(&"a"), Some(&"a"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_from(&"m"), Some(&"m"));
        assert_eq!(iter.next_from(&"m"), None);
    }

    #[test]
    fn defaul_next_after_works() {
        assert_eq!(LIST.iter().next_after(&"g"), Some(&"i"));
        assert_eq!(LIST.iter().next_after(&"a"), Some(&"c"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_after(&"k"), Some(&"m"));
        assert_eq!(iter.next_after(&"k"), None);
    }

    #[test]
    fn map_next_after_works() {
        assert_eq!(MapIter::new(MAP).next_after(&"g"), Some(&("i", 2)));
        assert_eq!(MapIter::new(MAP).next_after(&"a"), Some(&("c", 5)));
        let mut iter = MapIter::new(MAP);
        assert_eq!(iter.next_after(&"k"), Some(&("m", 0)));
        assert_eq!(iter.next_after(&"k"), None);
    }

    #[test]
    fn map_next_from_works() {
        assert_eq!(MapIter::new(MAP).next_from(&"g"), Some(&("g", 3)));
        assert_eq!(MapIter::new(MAP).next_from(&"a"), Some(&("a", 6)));
        let mut iter = MapIter::new(MAP);
        assert_eq!(iter.next_from(&"m"), Some(&("m", 0)));
        assert_eq!(iter.next_from(&"m"), None);
    }

    #[test]
    fn set_iter_works() {
        let vec = LIST.to_vec();
        let set_iter = SetIter::new(LIST);
        let result: Vec<&str> = set_iter.cloned().collect();
        assert_eq!(result, vec);
        let mut set_iter = SetIter::new(LIST);
        assert_eq!(set_iter.next_after(&"g"), Some(&"i"));
        let result: Vec<&str> = set_iter.cloned().collect();
        assert_eq!(result, vec[5..].to_vec());
        let mut set_iter = SetIter::new(LIST);
        assert_eq!(set_iter.next_from(&"g"), Some(&"g"));
        let result: Vec<&str> = set_iter.cloned().collect();
        assert_eq!(result, vec[4..].to_vec());
    }

    #[test]
    fn map_iter_works() {
        let vec = MAP.to_vec();
        let set_iter = MapIter::new(MAP);
        let result: Vec<(&str, i32)> = set_iter.cloned().collect();
        assert_eq!(result, vec);
        let mut set_iter = MapIter::new(MAP);
        assert_eq!(set_iter.next_after(&"g"), Some(&("i", 2)));
        let result: Vec<(&str, i32)> = set_iter.cloned().collect();
        assert_eq!(result, vec[5..].to_vec());
        let mut set_iter = MapIter::new(MAP);
        assert_eq!(set_iter.next_from(&"g"), Some(&("g", 3)));
        let result: Vec<(&str, i32)> = set_iter.cloned().collect();
        assert_eq!(result, vec[4..].to_vec());
    }

    #[test]
    fn iter_after_works() {
        let vec = LIST.to_vec();
        let iter_after = SetIter::new(&LIST[after_index!(LIST, &"g")..]);
        let result: Vec<&str> = iter_after.cloned().collect();
        assert_eq!(result, vec[4..].to_vec());
        let iter_after = SetIter::new(&LIST[after_index!(LIST, &"f")..]);
        let result: Vec<&str> = iter_after.cloned().collect();
        assert_eq!(result, vec[3..].to_vec());
    }

    #[test]
    fn iter_before_works() {
        let vec = LIST.to_vec();
        let iter_before = SetIter::new(&LIST[..from_index!(LIST, &"g")]);
        let result: Vec<&str> = iter_before.cloned().collect();
        assert_eq!(result, vec[..3].to_vec());
        let iter_before = SetIter::new(&LIST[..from_index!(LIST, &"f")]);
        let result: Vec<&str> = iter_before.cloned().collect();
        assert_eq!(result, vec[..3].to_vec());
    }

    #[test]
    fn iter_from_works() {
        let vec = LIST.to_vec();
        let iter_from = SetIter::new(&LIST[from_index!(LIST, &"g")..]);
        let result: Vec<&str> = iter_from.cloned().collect();
        assert_eq!(result, vec[3..].to_vec());
        let iter_from = SetIter::new(&LIST[from_index!(LIST, &"f")..]);
        let result: Vec<&str> = iter_from.cloned().collect();
        assert_eq!(result, vec[3..].to_vec());
    }

    #[test]
    fn iter_until_works() {
        let vec = LIST.to_vec();
        let iter_until = SetIter::new(&LIST[..after_index!(LIST, &"g")]);
        let result: Vec<&str> = iter_until.cloned().collect();
        assert_eq!(result, vec[..4].to_vec());
        let iter_until = SetIter::new(&LIST[..after_index!(LIST, &"f")]);
        let result: Vec<&str> = iter_until.cloned().collect();
        assert_eq!(result, vec[..3].to_vec());
    }
}
