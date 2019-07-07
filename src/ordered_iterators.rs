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

use crate::OrderedSet;
pub use crate::SkipAheadIterator;

use crate::iter_ops::IterSetOperations;

pub trait ToList<'a, T>: Iterator<Item = &'a T>
where
    T: 'a + Clone,
{
    /// Create a Vec<T> list from the items in the Iterator's output
    fn to_list(&mut self) -> Vec<T> {
        self.cloned().collect()
    }
}

pub trait ToSet<'a, T>: ToList<'a, T>
where
    T: 'a + Ord + Clone,
{
    /// Create a OrderedSet<T> from the items in the Iterator's output
    fn to_set(&mut self) -> OrderedSet<T> {
        OrderedSet::<T> {
            ordered_list: self.to_list(),
        }
    }
}

/// Return true if the data stream from the Iterator is ordered and
/// contains no duplicates.  Useful for testing.
pub fn output_is_ordered_nodups<'a, T, I>(iter: &mut I) -> bool
where
    T: 'a + Ord,
    I: SkipAheadIterator<'a, T>,
{
    let mut o_previous = iter.next();
    while let Some(previous) = o_previous {
        if let Some(item) = iter.next() {
            if previous >= item {
                return false;
            }
            o_previous = Some(item);
        } else {
            o_previous = None;
        }
    }
    true
}

// SET ITERATOR

/// An Iterator over the items in an ordered list
pub struct SetIter<'a, T: Ord> {
    ordered_list: &'a [T],
    index: usize,
}

impl<'a, T: Ord> SetIter<'a, T> {
    pub fn new(ordered_list: &'a [T]) -> Self {
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
    fn skip_past(&mut self, t: &T) -> &mut Self {
        self.index += after_index!(self.ordered_list[self.index..], t);
        self
    }

    fn skip_until(&mut self, t: &T) -> &mut Self {
        self.index += from_index!(self.ordered_list[self.index..], t);
        self
    }

    fn peek(&mut self) -> Option<&'a T> {
        self.ordered_list.get(self.index)
    }
}

impl<'a, T: Ord + Clone> ToList<'a, T> for SetIter<'a, T> {}

impl<'a, T: Ord + Clone> ToSet<'a, T> for SetIter<'a, T> {}

impl<'a, T: Ord + Clone> IterSetOperations<'a, T> for SetIter<'a, T> {}

#[cfg(test)]
mod tests {
    use super::*;

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static LIST_UNORDERED: &[&str] = &["a", "c", "e", "z", "g", "i", "k", "m"];

    #[test]
    fn output_is_ordered_nodups_works() {
        assert!(output_is_ordered_nodups(&mut SetIter::new(LIST)));
        let rev: Vec<&str> = LIST.iter().rev().cloned().collect();
        assert!(!output_is_ordered_nodups(&mut SetIter::new(&rev)));
        assert!(!output_is_ordered_nodups(&mut SetIter::new(LIST_UNORDERED)));
        let rev: Vec<&str> = LIST_UNORDERED.iter().rev().cloned().collect();
        assert!(!output_is_ordered_nodups(&mut SetIter::new(&rev)));
        //assert!(output_is_ordered_nodups(&mut MapIter::new(MAP)));
    }

    #[test]
    fn set_iter_works() {
        let vec = LIST.to_vec();
        assert_eq!(SetIter::new(LIST).to_list(), vec);
        let mut set_iter = SetIter::new(LIST);
        assert_eq!(set_iter.skip_past(&"g").next(), Some(&"i"));
        assert_eq!(set_iter.to_list(), vec[5..].to_vec());
        let mut set_iter = SetIter::new(LIST);
        assert_eq!(set_iter.skip_until(&"g").next(), Some(&"g"));
        assert_eq!(set_iter.to_list(), vec[4..].to_vec());
    }

    #[test]
    fn skip_past_works() {
        assert_eq!(SetIter::new(LIST).skip_past(&"g").next(), Some(&"i"));
        assert_eq!(SetIter::new(LIST).skip_past(&"f").next(), Some(&"g"));
        assert_eq!(SetIter::new(LIST).skip_past(&"g").to_set().len(), 3);
    }

    #[test]
    fn skip_until_works() {
        assert_eq!(SetIter::new(LIST).skip_until(&"g").next(), Some(&"g"));
        assert_eq!(SetIter::new(LIST).skip_until(&"f").next(), Some(&"g"));
        assert_eq!(SetIter::new(LIST).skip_until(&"f").to_set().len(), 4);
    }

    #[test]
    fn iter_after_works() {
        let vec = LIST.to_vec();
        let mut iter_after = SetIter::new(&LIST[after_index!(LIST, &"g")..]);
        assert_eq!(iter_after.to_list(), vec[4..].to_vec());
        let mut iter_after = SetIter::new(&LIST[after_index!(LIST, &"f")..]);
        assert_eq!(iter_after.to_list(), vec[3..].to_vec());
    }

    #[test]
    fn iter_before_works() {
        let vec = LIST.to_vec();
        let mut iter_before = SetIter::new(&LIST[..from_index!(LIST, &"g")]);
        assert_eq!(iter_before.to_list(), vec[..3].to_vec());
        let mut iter_before = SetIter::new(&LIST[..from_index!(LIST, &"f")]);
        assert_eq!(iter_before.to_list(), vec[..3].to_vec());
    }

    #[test]
    fn iter_from_works() {
        let vec = LIST.to_vec();
        let mut iter_from = SetIter::new(&LIST[from_index!(LIST, &"g")..]);
        assert_eq!(iter_from.to_list(), vec[3..].to_vec());
        let mut iter_from = SetIter::new(&LIST[from_index!(LIST, &"f")..]);
        assert_eq!(iter_from.to_list(), vec[3..].to_vec());
    }

    #[test]
    fn iter_until_works() {
        let vec = LIST.to_vec();
        let mut iter_until = SetIter::new(&LIST[..after_index!(LIST, &"g")]);
        assert_eq!(iter_until.to_list(), vec[..4].to_vec());
        let mut iter_until = SetIter::new(&LIST[..after_index!(LIST, &"f")]);
        assert_eq!(iter_until.to_list(), vec[..3].to_vec());
    }
}
