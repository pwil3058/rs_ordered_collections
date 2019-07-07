//! Sets implemented as a sorted list.
//! Useful for those situations when ordered iteration over a set's
//! contents is a frequent requirement.

pub mod ordered_map;
pub mod ordered_set;

pub use ordered_map::OrderedMap;
pub use ordered_set::OrderedSet;

/// Iterator enhancement to provide a skip ahead feature. This mechanism
/// is used to optimise implementation of set operation (difference, intersection, etc)
/// iterators.
pub trait SkipAheadIterator<'a, T: 'a + Ord>: Iterator<Item = &'a T> {
    /// Peek at the next item in the iterator
    fn peek(&mut self) -> Option<&'a T>;

    /// Skip ahead to the next item in the iterator after the given item.
    fn skip_past(&mut self, t: &T) -> &mut Self;

    /// Skip ahead to the next item in the iterator at or after the given item.
    fn skip_until(&mut self, t: &T) -> &mut Self;
}

#[cfg(test)]
mod tests {
    //use super::*;
}
