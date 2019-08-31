//! Sets and Maps that iterate over their contents in a defined order.

/// Creates an `OrderedSet`  containing the arguments.
#[macro_export]
macro_rules! ordered_set {
    ( $( $x:expr ),* ) => {
        {
            let mut set = OrderedSet::new();
            $(
                set.insert($x);
            )*
            set
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
