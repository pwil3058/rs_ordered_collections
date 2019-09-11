//! Sets and Maps that iterate over their contents in a defined order.

/// Creates an `OrderedSet`  containing the arguments.
#[macro_export]
macro_rules! ordered_set {
    ( $( $x:expr ),* ) => {
        {
            OrderedSet::from(vec![ $( $x ),*])
        }
    }
}

/// Creates an `OrderedMap` containing the arguments interpreted as key-value pairs.
#[macro_export]
macro_rules! ordered_map {
    ( $( ($k:expr, $v:expr) ),* ) => {
        {
            let mut map = OrderedMap::new();
            $(
                map.insert($k, $v);
            )*
            map
        }
    }
}

pub mod ordered_map;
pub mod ordered_set;

fn lower_bound_index<T, K>(members: &[T], bound: std::ops::Bound<&K>) -> usize
where
    K: Ord + Sized,
    T: Ord + std::borrow::Borrow<K>,
{
    use std::ops::Bound::*;
    match bound {
        Unbounded => 0,
        Included(item) => match members.binary_search_by_key(&item, |x| x.borrow()) {
            Ok(index) => index,
            Err(index) => index,
        },
        Excluded(item) => match members.binary_search_by_key(&item, |x| x.borrow()) {
            Ok(index) => index + 1,
            Err(index) => index,
        },
    }
}

fn upper_bound_index<T, K>(members: &[T], bound: std::ops::Bound<&K>) -> usize
where
    K: Ord + Sized,
    T: Ord + std::borrow::Borrow<K>,
{
    use std::ops::Bound::*;
    match bound {
        Unbounded => members.len(),
        Included(item) => match members.binary_search_by_key(&item, |x| x.borrow()) {
            Ok(index) => index + 1,
            Err(index) => index,
        },
        Excluded(item) => match members.binary_search_by_key(&item, |x| x.borrow()) {
            Ok(index) => index,
            Err(index) => index,
        },
    }
}

fn range_indices<T, K, R>(members: &[T], range: R) -> (usize, usize)
where
    K: Ord + Sized,
    R: std::ops::RangeBounds<K>,
    T: Ord + std::borrow::Borrow<K>,
{
    let start_index = lower_bound_index(members, range.start_bound());
    let end_index = upper_bound_index(members, range.end_bound());
    (start_index, end_index)
}

pub use ordered_map::OrderedMap;
pub use ordered_set::OrderedSet;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordered_set::ord_set_iterators::ToList;

    #[test]
    fn ordered_set_macro() {
        let ordered_set = ordered_set!(6, 3, 8, 2);
        assert!(ordered_set.contains(&3));
        assert_eq!(ordered_set.iter().to_list(), vec![2, 3, 6, 8]);
    }

    #[test]
    fn ordered_map_macro() {
        let ordered_map = ordered_map!(("k", 6), ("a", 3), ("c", 8), ("b", 2));
        assert!(ordered_map.contains_key(&"c"));
        assert_eq!(ordered_map.keys().to_list(), vec!["a", "b", "c", "k"]);
        let values: Vec<i32> = ordered_map.values().cloned().collect();
        assert_eq!(values, vec![3, 2, 8, 6]);
    }
}
