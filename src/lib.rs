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

extern crate rand;

pub mod iter_ops;
pub mod ordered_iterators;
pub mod ordered_map;
pub mod ordered_set;

/// An set of items of type T ordered according to Ord (with no duplicates)
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
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
