//! Sets implemented as a sorted list.
//! Useful for those situations when ordered iteration over a set's
//! contents is a frequent requirement.

pub mod iter_ops;
pub mod map_entry;
pub mod ordered_iterators;
pub mod ordered_map;
pub mod ordered_set;

pub use ordered_map::OrderedMap;
pub use ordered_set::OrderedSet;

/// Iterator enhancement to provide a skip ahead feature. This mechanism
/// is used to optimise implementation of set operation (difference, intersection, etc)
/// iterators.
pub trait SkipAheadIterator<'a, T: 'a + Ord, V: 'a>: Iterator<Item = V> {
    /// Skip ahead to the item in the iterator after the selector.
    fn skip_past(&mut self, t: &T) -> &mut Self;

    /// Skip ahead to the item in the iterator at or after the selector.
    fn skip_until(&mut self, t: &T) -> &mut Self;

    /// Return the next item in the iterator after the selector.
    fn next_after(&mut self, t: &T) -> Option<Self::Item> {
        self.skip_past(t).next()
    }

    /// Return the next item in the iterator at or after the selector.
    fn next_from(&mut self, t: &T) -> Option<Self::Item> {
        self.skip_until(t).next()
    }
}

#[cfg(test)]
mod tests {
    //use super::*;
}
