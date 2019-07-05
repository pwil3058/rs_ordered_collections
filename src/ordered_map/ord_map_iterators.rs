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
use std::slice::IterMut;

use crate::OrderedMap;
use crate::SkipAheadIterator;

pub use crate::ordered_iterators::SetIter;

pub trait ToMap<'a, K, V>: Iterator<Item = (&'a K, &'a V)>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
{
    /// Create a OrderedSet<T> from the items in the Iterator's output
    fn to_map(&mut self) -> OrderedMap<K, V> {
        let mut keys: Vec<K> = vec![];
        let mut values: Vec<V> = vec![];
        for (k, v) in self {
            keys.push(k.clone());
            values.push(v.clone());
        }
        OrderedMap::<K, V> { keys, values }
    }
}

// MAP ITERATOR

/// An Iterator over the items in an ordered map
pub struct MapIter<'a, K: Ord, V> {
    keys: &'a [K],
    values: &'a [V],
    index: usize,
}

impl<'a, K: Ord, V> MapIter<'a, K, V> {
    pub fn new(keys: &'a [K], values: &'a [V]) -> Self {
        Self {
            keys,
            values,
            index: 0,
        }
    }
}

impl<'a, K: Ord, V> Iterator for MapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.keys.len() {
            let keys = &self.keys[self.index];
            let values = &self.values[self.index];
            self.index += 1;
            Some((keys, values))
        } else {
            None
        }
    }
}

impl<'a, K: 'a + Ord, V: 'a> SkipAheadIterator<'a, K, (&'a K, &'a V)> for MapIter<'a, K, V> {
    fn skip_past(&mut self, k: &K) -> &mut Self {
        self.index += after_index!(self.keys[self.index..], k);
        self
    }

    fn skip_until(&mut self, k: &K) -> &mut Self {
        self.index += from_index!(self.keys[self.index..], k);
        self
    }
}

impl<'a, K: Ord + Clone, V: Clone> ToMap<'a, K, V> for MapIter<'a, K, V> {}

// MUT MAP ITERATOR

/// An Iterator over the keys and mutable values in an ordered map in key order
// Use built in mutable iterator due to insoluble lifetime issues
pub struct MapIterMut<'a, K: Ord, V> {
    keys: &'a [K],
    index: usize,
    iter_mut: IterMut<'a, V>,
}

impl<'a, K: 'a + Ord, V: 'a> MapIterMut<'a, K, V> {
    pub fn new(keys: &'a [K], values: &'a mut [V]) -> Self {
        Self {
            iter_mut: values.iter_mut(),
            keys,
            index: 0,
        }
    }
}

impl<'a, K: Ord, V> Iterator for MapIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(key) = self.keys.get(self.index) {
            self.index += 1;
            Some((key, self.iter_mut.next().unwrap()))
        } else {
            None
        }
    }
}

impl<'a, K: 'a + Ord, V: 'a> SkipAheadIterator<'a, K, (&'a K, &'a mut V)> for MapIterMut<'a, K, V> {
    /// Skip ahead to the item in the iterator after the selector key.
    fn skip_past(&mut self, k: &K) -> &mut Self {
        let index_incr = after_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }

    /// Skip ahead to the item in the iterator at or after the selector key.
    fn skip_until(&mut self, k: &K) -> &mut Self {
        let index_incr = from_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }
}

// VALUE ITERATOR

/// An Iterator over the values in an ordered map in key order
pub struct ValueIter<'a, K: Ord, V> {
    keys: &'a [K],
    values: &'a [V],
    index: usize,
}

impl<'a, K: Ord, V> ValueIter<'a, K, V> {
    pub fn new(keys: &'a [K], values: &'a [V]) -> Self {
        Self {
            keys,
            values,
            index: 0,
        }
    }
}

impl<'a, K: Ord, V> Iterator for ValueIter<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(value) = self.values.get(self.index) {
            self.index += 1;
            Some(value)
        } else {
            None
        }
    }
}

impl<'a, K: Ord, V> SkipAheadIterator<'a, K, &'a V> for ValueIter<'a, K, V> {
    fn skip_past(&mut self, k: &K) -> &mut Self {
        self.index += after_index!(self.keys[self.index..], k);
        self
    }

    fn skip_until(&mut self, k: &K) -> &mut Self {
        self.index += from_index!(self.keys[self.index..], k);
        self
    }
}

// MUT VALUE ITERATOR

/// An Iterator over the values in an ordered map in key order
pub struct ValueIterMut<'a, K: Ord, V> {
    keys: &'a [K],
    index: usize,
    iter_mut: IterMut<'a, V>,
}

impl<'a, K: 'a + Ord, V: 'a> ValueIterMut<'a, K, V> {
    pub fn new(keys: &'a [K], values: &'a mut [V]) -> Self {
        Self {
            iter_mut: values.iter_mut(),
            keys,
            index: 0,
        }
    }
}

impl<'a, K: Ord, V> Iterator for ValueIterMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.keys.len() {
            self.index += 1;
            self.iter_mut.next()
        } else {
            None
        }
    }
}

impl<'a, K: Ord, V: 'a> SkipAheadIterator<'a, K, &'a mut V> for ValueIterMut<'a, K, V> {
    /// Skip ahead past items in the iterator whose keys are less than
    /// or equal to the given key
    fn skip_past(&mut self, k: &K) -> &mut Self {
        let index_incr = after_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }

    /// Skip ahead past items in the iterator whose keys are less than
    /// the given key
    fn skip_until(&mut self, k: &K) -> &mut Self {
        let index_incr = from_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }
}

// Map Merge Iterator
/// Ordered Iterator over the merged output of two disjoint map Iterators.
// TODO: does this need to be so general i.e. limit to MapIter
pub struct MapMergeIter<'a, K, V, L, R>
where
    K: Ord,
    L: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
{
    l_item: Option<(&'a K, &'a V)>,
    r_item: Option<(&'a K, &'a V)>,
    l_iter: L,
    r_iter: R,
}

impl<'a, K, V, L, R> MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
{
    pub fn new(mut l_iter: L, mut r_iter: R) -> Self {
        Self {
            l_item: l_iter.next(),
            r_item: r_iter.next(),
            l_iter,
            r_iter,
        }
    }
}

impl<'a, K, V, L, R> Iterator for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
{
    type Item = (&'a K, &'a V);

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

impl<'a, K, V, L, R> SkipAheadIterator<'a, K, (&'a K, &'a V)> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
{
    fn skip_past(&mut self, k: &K) -> &mut Self {
        if let Some(l_item) = self.l_item {
            if l_item.0 <= k {
                self.l_item = self.l_iter.skip_past(k).next();
            }
        }
        if let Some(r_item) = self.r_item {
            if r_item.0 <= k {
                self.r_item = self.r_iter.skip_past(k).next();
            }
        }
        self
    }

    fn skip_until(&mut self, k: &K) -> &mut Self {
        if let Some(l_item) = self.l_item {
            if l_item.0 < k {
                self.l_item = self.l_iter.skip_until(k).next();
            }
        }
        if let Some(r_item) = self.r_item {
            if r_item.0 < k {
                self.r_item = self.r_iter.skip_until(k).next();
            }
        }
        self
    }
}

impl<'a, K, V, L, R> ToMap<'a, K, V> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K, (&'a K, &'a V)>,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static VALUES: &[i32] = &[6, 5, 4, 3, 2, 1, 0];
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
    fn map_next_after_works() {
        assert_eq!(
            MapIter::new(LIST, VALUES).next_after(&"g"),
            Some((&"i", &2))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES).next_after(&"a"),
            Some((&"c", &5))
        );
        let mut iter = MapIter::new(LIST, VALUES);
        assert_eq!(iter.next_after(&"k"), Some((&"m", &0)));
        assert_eq!(iter.next_after(&"k"), None);
    }

    #[test]
    fn map_next_from_works() {
        assert_eq!(MapIter::new(LIST, VALUES).next_from(&"g"), Some((&"g", &3)));
        assert_eq!(MapIter::new(LIST, VALUES).next_from(&"a"), Some((&"a", &6)));
        let mut iter = MapIter::new(LIST, VALUES);
        assert_eq!(iter.next_from(&"m"), Some((&"m", &0)));
        assert_eq!(iter.next_from(&"m"), None);
    }

    #[test]
    fn skip_past_works() {
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_past(&"g").next(),
            Some((&"i", &2))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_past(&"f").next(),
            Some((&"g", &3))
        );
        assert_eq!(MapIter::new(LIST, VALUES).skip_past(&"g").to_map().len(), 3);
    }

    #[test]
    fn skip_until_works() {
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_until(&"g").next(),
            Some((&"g", &3))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_until(&"f").next(),
            Some((&"g", &3))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_until(&"f").to_map().len(),
            4
        );
    }

    #[test]
    fn map_iter_works() {
        let vec = MAP.to_vec();
        let set_iter = MapIter::new(LIST, VALUES);
        let result: Vec<(&str, i32)> = set_iter.map(|(x, y)| (x.clone(), y.clone())).collect();
        assert_eq!(result, vec);
        let mut set_iter = MapIter::new(LIST, VALUES);
        assert_eq!(set_iter.next_after(&"g"), Some((&"i", &2)));
        let result: Vec<(&str, i32)> = set_iter.map(|(x, y)| (x.clone(), y.clone())).collect();
        assert_eq!(result, vec[5..].to_vec());
        let mut set_iter = MapIter::new(LIST, VALUES);
        assert_eq!(set_iter.next_from(&"g"), Some((&"g", &3)));
        let result: Vec<(&str, i32)> = set_iter.map(|(x, y)| (x.clone(), y.clone())).collect();
        assert_eq!(result, vec[4..].to_vec());
    }

    #[test]
    fn map_iter_mut_works() {
        let mut values: Vec<i32> = VALUES.iter().cloned().collect();
        for (i, pair) in MapIter::new(LIST, &values).enumerate() {
            assert_eq!((6 - i as i32), *pair.1);
        }
        for (i, (_, value)) in MapIterMut::new(LIST, &mut values).enumerate() {
            *value = i as i32 + 5;
        }
        for (i, pair) in MapIter::new(LIST, &values).enumerate() {
            assert_eq!((i as i32 + 5), *pair.1);
        }
    }

    #[test]
    fn value_iter_mut_works() {
        let vec: Vec<i32> = VALUES.iter().cloned().collect();
        let mut values: Vec<i32> = VALUES.iter().cloned().collect();
        let result: Vec<i32> = ValueIterMut::new(LIST, &mut values).map(|x| *x).collect();
        assert_eq!(result, vec);
        assert_eq!(
            ValueIterMut::new(LIST, &mut values).next_after(&"g"),
            Some(&mut 2_i32)
        );
        let result: Vec<i32> = ValueIterMut::new(LIST, &mut values)
            .skip_past(&"i")
            .map(|x| *x)
            .collect();
        assert_eq!(result, vec[5..].to_vec());
        assert_eq!(
            ValueIterMut::new(LIST, &mut values).next_from(&"g"),
            Some(&mut 3_i32)
        );
        let result: Vec<i32> = ValueIterMut::new(LIST, &mut values)
            .skip_past(&"g")
            .map(|x| *x)
            .collect();
        assert_eq!(result, vec[4..].to_vec());
        for (i, value) in ValueIter::new(LIST, &values).enumerate() {
            assert!(*value != i as i32 || i == 3);
        }
        for (i, value) in ValueIterMut::new(LIST, &mut values).enumerate() {
            *value = i as i32;
        }
        for (i, value) in ValueIter::new(LIST, &values).enumerate() {
            assert_eq!(*value, i as i32);
        }
    }

    #[test]
    fn value_iter_works() {
        let vec: Vec<i32> = VALUES.iter().cloned().collect();
        let values: Vec<i32> = ValueIter::new(LIST, VALUES).cloned().collect();
        assert_eq!(values, vec);
        let mut value_iter = ValueIter::new(LIST, VALUES);
        assert_eq!(value_iter.next_after(&"g"), Some(&2_i32));
        let values: Vec<i32> = value_iter.cloned().collect();
        assert_eq!(values, vec[5..].to_vec());
        let mut value_iter = ValueIter::new(LIST, VALUES);
        assert_eq!(value_iter.next_from(&"g"), Some(&3_i32));
        let values: Vec<i32> = value_iter.cloned().collect();
        assert_eq!(values, vec[4..].to_vec());
    }
}
