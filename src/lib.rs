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

//! Sets implemented as a sorted list.
//! Useful for those situations when ordered iteration over a set's
//! contents is a frequent requirement.

extern crate rand;

use std::cmp::Ordering;
use std::iter::Iterator;

pub mod set_iterators;
pub mod iterators;
pub mod ordered_map;
pub mod ordered_set;

/// An set of items of type T ordered according to Ord (with no duplicates)
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OrderedSet<T: Ord> {
    ordered_list: Vec<T>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct OrderedMap<K: Ord, V> {
    ordered_list: Vec<(K, V)>,
}

pub fn are_disjoint<'a, T, L, R>(l_iter: &mut L, r_iter: &mut R) -> bool
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    let mut o_l_item = l_iter.next();
    let mut o_r_item = r_iter.next();

    loop {
        if let Some(l_item) = o_l_item {
            if let Some(r_item) = o_r_item {
                match l_item.cmp(&r_item) {
                    Ordering::Less => {
                        o_l_item = l_iter.next();
                    }
                    Ordering::Greater => {
                        o_r_item = r_iter.next();
                    }
                    Ordering::Equal => {
                        return false;
                    }
                }
            } else {
                return true;
            }
        } else {
            return true;
        }
    }
}

pub fn a_contains_b<'a, T, A, B>(a_iter: &mut A, b_iter: &mut B) -> bool
where
    T: 'a + Ord,
    A: Iterator<Item = &'a T>,
    B: Iterator<Item = &'a T>,
{
    let mut o_a_item = a_iter.next();
    let mut o_b_item = b_iter.next();

    while let Some(b_item) = o_b_item {
        if let Some(a_item) = o_a_item {
            match b_item.cmp(&a_item) {
                Ordering::Less => {
                    return false;
                }
                Ordering::Greater => {
                    o_a_item = a_iter.next();
                }
                Ordering::Equal => {
                    o_b_item = b_iter.next();
                    o_a_item = a_iter.next();
                }
            }
        } else {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn are_disjoint_works() {
        let list1 = vec!["a", "c", "e", "g", "i", "k", "m"];
        let list2 = vec!["b", "d", "f", "h", "j", "l", "n"];
        let list3 = vec!["e", "f", "x", "y", "z"];

        assert!(are_disjoint(&mut list1.iter(), &mut list2.iter()));
        assert!(!are_disjoint(&mut list1.iter(), &mut list3.iter()));
        assert!(!are_disjoint(&mut list3.iter(), &mut list2.iter()));
    }
}
