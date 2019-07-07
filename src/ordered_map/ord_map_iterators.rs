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
use std::slice::IterMut;

use crate::OrderedMap;

use crate::SkipAheadIterator;

/// Iterator enhancement to provide a skip ahead feature. This mechanism
/// is used to optimise implementation of set like operation (except, only, etc)
/// filters.
pub trait SkipAheadMapIterator<'a, K: 'a + Ord, I: 'a>: Iterator<Item = I> {
    /// Peek at the next key in the iterator
    fn peek_key(&mut self) -> Option<&'a K>;

    /// Skip ahead to the next item in the iterator with a key after the given key.
    fn skip_past_key(&mut self, key: &K) -> &mut Self;

    /// Skip ahead to the item in the iterator with a key at or after the given key.
    fn skip_until_key(&mut self, key: &K) -> &mut Self;
}

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

impl<'a, K: 'a + Ord, V: 'a> SkipAheadMapIterator<'a, K, (&'a K, &'a V)> for MapIter<'a, K, V> {
    fn skip_past_key(&mut self, k: &K) -> &mut Self {
        self.index += after_index!(self.keys[self.index..], k);
        self
    }

    fn skip_until_key(&mut self, k: &K) -> &mut Self {
        self.index += from_index!(self.keys[self.index..], k);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        self.keys.get(self.index)
    }
}

impl<'a, K: Ord + Clone, V: Clone> ToMap<'a, K, V> for MapIter<'a, K, V> {}

impl<'a, K: Ord, V> MapIterFilter<'a, K, V> for MapIter<'a, K, V> {}

impl<'a, K, V> MapIterMerge<'a, K, V> for MapIter<'a, K, V>
where
    K: 'a + Ord + Clone,
    V: 'a,
{
}

pub trait MapIterFilter<'a, K: 'a + Ord, V: 'a>:
    SkipAheadMapIterator<'a, K, (&'a K, &'a V)> + Sized
{
    /// Exclude keys in the given key iterator from the output stream.
    fn except<I: SkipAheadIterator<'a, K>>(self, iter: I) -> MapIterExcept<'a, K, V, Self, I> {
        MapIterExcept::new(self, iter)
    }

    /// Exclude keys not in the given key iteratorn from the output stream.
    fn only<I: SkipAheadIterator<'a, K>>(self, iter: I) -> MapIterOnly<'a, K, V, Self, I> {
        MapIterOnly::new(self, iter)
    }
}

macro_rules! define_mapiter_filter {
    ( $doc:meta, $iter:ident ) => {
        #[$doc]
        pub struct $iter<'a, K, V, L, R>
        where
            K: Ord,
            L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
            R: SkipAheadIterator<'a, K>,
        {
            l_iter: L,
            r_iter: R,
            phantom: PhantomData<(&'a K, &'a V)>,
        }

        impl<'a, K, V, L, R> $iter<'a, K, V, L, R>
        where
            K: Ord,
            L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
            R: SkipAheadIterator<'a, K>,
        {
            pub(crate) fn new(l_iter: L, r_iter: R) -> Self {
                Self {
                    l_iter,
                    r_iter,
                    phantom: PhantomData,
                }
            }
        }

        impl<'a, K, V, L, R> ToMap<'a, K, V> for $iter<'a, K, V, L, R>
        where
            K: Ord + Clone,
            V: Clone,
            L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
            R: SkipAheadIterator<'a, K>,
        {
        }
    };
}

define_mapiter_filter!(
    doc = "Iterator over the contents of a MapIter excepting those whose
    keys are in the provided key iterator.",
    MapIterExcept
);

impl<'a, K, V, L, R> Iterator for MapIterExcept<'a, K, V, L, R>
where
    K: Ord,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K>,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_key) = self.r_iter.peek() {
                    match l_key.cmp(&r_key) {
                        Ordering::Less => {
                            return self.l_iter.next();
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
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

impl<'a, K, V, L, R> SkipAheadMapIterator<'a, K, (&'a K, &'a V)> for MapIterExcept<'a, K, V, L, R>
where
    K: 'a + Ord,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K>,
{
    fn skip_past_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_past_key(key);
        self.r_iter.skip_past(key);
        self
    }

    fn skip_until_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_until_key(key);
        self.r_iter.skip_until(key);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            return Some(l_key);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
                        }
                        Ordering::Equal => {
                            self.l_iter.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return Some(l_key);
                }
            } else {
                return None;
            }
        }
    }
}

impl<'a, K, V, L, R> MapIterMerge<'a, K, V> for MapIterExcept<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K>,
{
}

define_mapiter_filter!(
    doc = "Iterator over the contents of a MapIter excepting those whose
    keys are not in the provided key iterator.",
    MapIterOnly
);

impl<'a, K, V, L, R> Iterator for MapIterOnly<'a, K, V, L, R>
where
    K: Ord,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K>,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.skip_until_key(&r_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
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

impl<'a, K, V, L, R> SkipAheadMapIterator<'a, K, (&'a K, &'a V)> for MapIterOnly<'a, K, V, L, R>
where
    K: 'a + Ord,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K>,
{
    fn skip_past_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_past_key(key);
        self.r_iter.skip_past(key);
        self
    }

    fn skip_until_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_until_key(key);
        self.r_iter.skip_until(key);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.skip_until_key(&r_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
                        }
                        Ordering::Equal => {
                            return Some(l_key);
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

impl<'a, K, V, L, R> MapIterMerge<'a, K, V> for MapIterOnly<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadIterator<'a, K>,
{
}

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

    /// Exclude keys in the given key iterator from the output stream.
    pub fn except<I: SkipAheadIterator<'a, K>>(self, iter: I) -> MapIterMutExcept<'a, K, V, I> {
        MapIterMutExcept::new(self, iter)
    }

    /// Exclude keys not in the given key iteratorn from the output stream.
    pub fn only<I: SkipAheadIterator<'a, K>>(self, iter: I) -> MapIterMutOnly<'a, K, V, I> {
        MapIterMutOnly::new(self, iter)
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

impl<'a, K: 'a + Ord, V: 'a> SkipAheadMapIterator<'a, K, (&'a K, &'a mut V)>
    for MapIterMut<'a, K, V>
{
    /// Skip ahead to the item in the iterator after the selector key.
    fn skip_past_key(&mut self, k: &K) -> &mut Self {
        let index_incr = after_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }

    /// Skip ahead to the item in the iterator at or after the selector key.
    fn skip_until_key(&mut self, k: &K) -> &mut Self {
        let index_incr = from_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        self.keys.get(self.index)
    }
}

macro_rules! define_mapitermut_filter {
    ( $doc:meta, $iter:ident ) => {
        #[$doc]
        pub struct $iter<'a, K, V, R>
        where
            K: Ord,
            R: SkipAheadIterator<'a, K>,
        {
            l_iter: MapIterMut<'a, K, V>,
            r_iter: R,
        }

        impl<'a, K, V, R> $iter<'a, K, V, R>
        where
            K: Ord,
            R: SkipAheadIterator<'a, K>,
        {
            pub(crate) fn new(l_iter: MapIterMut<'a, K, V>, r_iter: R) -> Self {
                Self { l_iter, r_iter }
            }
        }
    };
}

define_mapitermut_filter!(
    doc = "Iterator over the contents of a MapIterMut excepting those whose
    keys are in the provided key iterator.",
    MapIterMutExcept
);

impl<'a, K, V, R> Iterator for MapIterMutExcept<'a, K, V, R>
where
    K: Ord,
    R: SkipAheadIterator<'a, K>,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.index += 1;
                            return Some((l_key, self.l_iter.iter_mut.next().unwrap()));
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
                        }
                        Ordering::Equal => {
                            self.l_iter.index += 1;
                            self.l_iter.iter_mut.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    self.l_iter.index += 1;
                    return Some((l_key, self.l_iter.iter_mut.next().unwrap()));
                }
            } else {
                return None;
            }
        }
    }
}

impl<'a, K, V, R> SkipAheadMapIterator<'a, K, (&'a K, &'a mut V)> for MapIterMutExcept<'a, K, V, R>
where
    K: 'a + Ord,
    R: SkipAheadIterator<'a, K>,
{
    fn skip_past_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_past_key(key);
        self.r_iter.skip_past(key);
        self
    }

    fn skip_until_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_until_key(key);
        self.r_iter.skip_until(key);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            return Some(l_key);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
                        }
                        Ordering::Equal => {
                            self.l_iter.index += 1;
                            self.l_iter.iter_mut.next();
                            self.r_iter.next();
                        }
                    }
                } else {
                    return Some(l_key);
                }
            } else {
                return None;
            }
        }
    }
}

define_mapitermut_filter!(
    doc = "Iterator over the contents of a MapIterMut excepting those whose
    keys are not in the provided key iterator.",
    MapIterMutOnly
);

impl<'a, K, V, R> Iterator for MapIterMutOnly<'a, K, V, R>
where
    K: Ord,
    R: SkipAheadIterator<'a, K>,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.skip_until_key(&r_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
                        }
                        Ordering::Equal => {
                            self.r_iter.next();
                            self.l_iter.index += 1;
                            return Some((l_key, self.l_iter.iter_mut.next().unwrap()));
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

impl<'a, K, V, R> SkipAheadMapIterator<'a, K, (&'a K, &'a mut V)> for MapIterMutOnly<'a, K, V, R>
where
    K: 'a + Ord,
    R: SkipAheadIterator<'a, K>,
{
    fn skip_past_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_past_key(key);
        self.r_iter.skip_past(key);
        self
    }

    fn skip_until_key(&mut self, key: &K) -> &mut Self {
        self.l_iter.skip_until_key(key);
        self.r_iter.skip_until(key);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_item) = self.r_iter.peek() {
                    match l_key.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_iter.skip_until_key(&r_item);
                        }
                        Ordering::Greater => {
                            self.r_iter.skip_until(&l_key);
                        }
                        Ordering::Equal => {
                            return Some(l_key);
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

impl<'a, K: Ord, V> SkipAheadMapIterator<'a, K, &'a V> for ValueIter<'a, K, V> {
    fn skip_past_key(&mut self, k: &K) -> &mut Self {
        self.index += after_index!(self.keys[self.index..], k);
        self
    }

    fn skip_until_key(&mut self, k: &K) -> &mut Self {
        self.index += from_index!(self.keys[self.index..], k);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        self.keys.get(self.index)
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

impl<'a, K: Ord, V: 'a> SkipAheadMapIterator<'a, K, &'a mut V> for ValueIterMut<'a, K, V> {
    /// Skip ahead past items in the iterator whose keys are less than
    /// or equal to the given key
    fn skip_past_key(&mut self, k: &K) -> &mut Self {
        let index_incr = after_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }

    /// Skip ahead past items in the iterator whose keys are less than
    /// the given key
    fn skip_until_key(&mut self, k: &K) -> &mut Self {
        let index_incr = from_index!(self.keys[self.index..], k);
        for _ in 0..index_incr {
            self.iter_mut.next();
        }
        self.index += index_incr;
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        self.keys.get(self.index)
    }
}

// Map Merge Iterator
/// Ordered Iterator over the merged output of two disjoint map Iterators.
pub struct MapMergeIter<'a, K, V, L, R>
where
    K: Ord,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
    l_iter: L,
    r_iter: R,
    phantom: PhantomData<(&'a K, &'a V)>,
}

pub trait MapIterMerge<'a, K, V>: SkipAheadMapIterator<'a, K, (&'a K, &'a V)> + Sized
where
    K: 'a + Ord,
    V: 'a,
{
    fn merge<I: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>>(
        self,
        other: I,
    ) -> MapMergeIter<'a, K, V, Self, I> {
        MapMergeIter::new(self, other)
    }
}

impl<'a, K, V, L, R> MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
    pub fn new(l_iter: L, r_iter: R) -> Self {
        Self {
            l_iter,
            r_iter,
            phantom: PhantomData,
        }
    }
}

impl<'a, K, V, L, R> Iterator for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_key) = self.l_iter.peek_key() {
                if let Some(r_key) = self.r_iter.peek_key() {
                    match l_key.cmp(&r_key) {
                        Ordering::Less => {
                            return self.l_iter.next();
                        }
                        Ordering::Greater => {
                            return self.r_iter.next();
                        }
                        Ordering::Equal => {
                            panic!("merged map Iterators are not disjoint");
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

impl<'a, K, V, L, R> SkipAheadMapIterator<'a, K, (&'a K, &'a V)> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord,
    V: 'a,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
    fn skip_past_key(&mut self, k: &K) -> &mut Self {
        self.l_iter.skip_past_key(k);
        self.r_iter.skip_past_key(k);
        self
    }

    fn skip_until_key(&mut self, k: &K) -> &mut Self {
        self.l_iter.skip_until_key(k);
        self.r_iter.skip_until_key(k);
        self
    }

    fn peek_key(&mut self) -> Option<&'a K> {
        if let Some(l_key) = self.l_iter.peek_key() {
            if let Some(r_key) = self.r_iter.peek_key() {
                match l_key.cmp(&r_key) {
                    Ordering::Less | Ordering::Equal => {
                        return Some(l_key);
                    }
                    Ordering::Greater => {
                        return Some(r_key);
                    }
                }
            } else {
                return Some(l_key);
            }
        } else {
            return self.r_iter.peek_key();
        }
    }
}

impl<'a, K, V, L, R> ToMap<'a, K, V> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
}

impl<'a, K, V, L, R> MapIterFilter<'a, K, V> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
}

impl<'a, K, V, L, R> MapIterMerge<'a, K, V> for MapMergeIter<'a, K, V, L, R>
where
    K: 'a + Ord + Clone,
    V: 'a + Clone,
    L: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
    R: SkipAheadMapIterator<'a, K, (&'a K, &'a V)>,
{
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordered_set::ord_set_iterators::SetIter;

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static VALUES: &[i32] = &[6, 5, 4, 3, 2, 1, 0];
    static LIST_1: &[&str] = &["b", "f", "l", "n", "o", "s", "z"];
    static VALUES_1: &[i32] = &[16, 15, 14, 13, 12, 11, 10];
    static LIST_2: &[&str] = &["d", "h", "j", "p", "t", "u", "y"];
    static VALUES_2: &[i32] = &[116, 115, 114, 113, 112, 111, 110];
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
    fn skip_past_key_works() {
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_past_key(&"g").next(),
            Some((&"i", &2))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_past_key(&"f").next(),
            Some((&"g", &3))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES)
                .skip_past_key(&"g")
                .to_map()
                .len(),
            3
        );
    }

    #[test]
    fn skip_until_works() {
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_until_key(&"g").next(),
            Some((&"g", &3))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES).skip_until_key(&"f").next(),
            Some((&"g", &3))
        );
        assert_eq!(
            MapIter::new(LIST, VALUES)
                .skip_until_key(&"f")
                .to_map()
                .len(),
            4
        );
    }

    #[test]
    fn map_iter_works() {
        let vec = MAP.to_vec();
        let map_iter = MapIter::new(LIST, VALUES);
        let result: Vec<(&str, i32)> = map_iter.map(|(x, y)| (x.clone(), y.clone())).collect();
        assert_eq!(result, vec);
        let mut map_iter = MapIter::new(LIST, VALUES);
        assert_eq!(map_iter.skip_past_key(&"g").next(), Some((&"i", &2)));
        let result: Vec<(&str, i32)> = map_iter.map(|(x, y)| (x.clone(), y.clone())).collect();
        assert_eq!(result, vec[5..].to_vec());
        let mut map_iter = MapIter::new(LIST, VALUES);
        assert_eq!(map_iter.skip_until_key(&"g").next(), Some((&"g", &3)));
        let result: Vec<(&str, i32)> = map_iter.map(|(x, y)| (x.clone(), y.clone())).collect();
        assert_eq!(result, vec[4..].to_vec());
    }

    #[test]
    fn map_iter_merge() {
        let map_iter_0 = MapIter::new(LIST, VALUES);
        let map_iter_1 = MapIter::new(LIST_1, VALUES_1);
        let map_iter_2 = MapIter::new(LIST_2, VALUES_2);
        let map = map_iter_0.merge(map_iter_1).merge(map_iter_2).to_map();
        assert!(map.is_valid());
        assert_eq!(LIST.len() + LIST_1.len() + LIST_2.len(), map.len());
        let map_iter_0 = MapIter::new(LIST, VALUES);
        let map_iter_1 = MapIter::new(LIST_1, VALUES_1);
        let map_iter_2 = MapIter::new(LIST_2, VALUES_2);
        let map = map_iter_0.merge(map_iter_1.merge(map_iter_2)).to_map();
        assert!(map.is_valid());
        assert_eq!(LIST.len() + LIST_1.len() + LIST_2.len(), map.len());
    }

    #[test]
    fn map_iter_except() {
        let set_iter = SetIter::new(&["e", "i", "k"]);
        let map = MapIter::new(LIST, VALUES).except(set_iter).to_map();
        assert_eq!(map.len(), 4);
        for s in &["e", "i", "k"] {
            assert!(!map.contains_key(&s));
        }
    }

    #[test]
    fn map_iter_only() {
        let set_iter = SetIter::new(&["e", "i", "k"]);
        let map = MapIter::new(LIST, VALUES).only(set_iter).to_map();
        assert_eq!(map.len(), 3);
        for s in &["e", "i", "k"] {
            assert!(map.contains_key(&s));
        }
    }

    #[test]
    fn map_iter_mut_except() {
        let ref_map = MapIter::new(LIST, VALUES).to_map();
        let mut map = MapIter::new(LIST, VALUES).to_map();
        let set_iter = SetIter::new(&["e", "i", "k"]);
        for (_, value) in map.iter_mut().except(set_iter) {
            *value += 10;
        }
        for ((ref_key, ref_value), (key, value)) in ref_map.iter().zip(map.iter()) {
            assert_eq!(ref_key, key);
            if ["e", "i", "k"].contains(key) {
                assert_eq!(*ref_value, *value);
            } else {
                assert_eq!(*ref_value + 10, *value);
            }
        }
    }

    #[test]
    fn map_iter_mut_only() {
        let ref_map = MapIter::new(LIST, VALUES).to_map();
        let mut map = MapIter::new(LIST, VALUES).to_map();
        let set_iter = SetIter::new(&["e", "i", "k"]);
        for (_, value) in map.iter_mut().only(set_iter) {
            *value += 10;
        }
        for ((ref_key, ref_value), (key, value)) in ref_map.iter().zip(map.iter()) {
            assert_eq!(ref_key, key);
            if ["e", "i", "k"].contains(key) {
                assert_eq!(*ref_value + 10, *value);
            } else {
                assert_eq!(*ref_value, *value);
            }
        }
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
            ValueIterMut::new(LIST, &mut values)
                .skip_past_key(&"g")
                .next(),
            Some(&mut 2_i32)
        );
        let result: Vec<i32> = ValueIterMut::new(LIST, &mut values)
            .skip_past_key(&"i")
            .map(|x| *x)
            .collect();
        assert_eq!(result, vec[5..].to_vec());
        assert_eq!(
            ValueIterMut::new(LIST, &mut values)
                .skip_until_key(&"g")
                .next(),
            Some(&mut 3_i32)
        );
        let result: Vec<i32> = ValueIterMut::new(LIST, &mut values)
            .skip_past_key(&"g")
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
        assert_eq!(value_iter.skip_past_key(&"g").next(), Some(&2_i32));
        let values: Vec<i32> = value_iter.cloned().collect();
        assert_eq!(values, vec[5..].to_vec());
        let mut value_iter = ValueIter::new(LIST, VALUES);
        assert_eq!(value_iter.skip_until_key(&"g").next(), Some(&3_i32));
        let values: Vec<i32> = value_iter.cloned().collect();
        assert_eq!(values, vec[4..].to_vec());
    }
}
