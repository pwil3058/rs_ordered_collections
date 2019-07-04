//! Sets implemented as a sorted list.
//! Useful for those situations when ordered iteration over a set's
//! contents is a frequent requirement.

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

pub mod iter_ops;
pub mod ordered_iterators;
pub mod ordered_map;
pub mod ordered_set;

/// An set of items of type T ordered according to Ord (with no duplicates)
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OrderedSet<T: Ord> {
    ordered_list: Vec<T>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OrderedMap<K: Ord, V> {
    keys: Vec<K>,
    values: Vec<V>,
}

#[cfg(test)]
mod tests {
    //use super::*;
}
