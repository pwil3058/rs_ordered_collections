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

pub mod list_map;
pub mod list_set;

pub mod iteration {
    ///! PairedIters are a generic object that provides a collection of
    ///! next() functions that are useful for creating iterators that
    ///! perform set like filtering on the contents of ordered collections.
    use std::cmp::Ordering;
    use std::iter::Iterator;

    pub struct PairedIters<'a, T, L, R>
    where
        T: 'a + Ord,
        L: Iterator<Item = &'a T>,
        R: Iterator<Item = &'a T>,
    {
        l_item: Option<L::Item>,
        r_item: Option<R::Item>,
        l_iter: L,
        r_iter: R,
    }

    impl<'a, T, L, R> PairedIters<'a, T, L, R>
    where
        T: 'a + Ord,
        L: Iterator<Item = &'a T>,
        R: Iterator<Item = &'a T>,
    {
        pub fn new(mut l_iter: L, mut r_iter: R) -> Self {
            Self {
                l_item: l_iter.next(),
                r_item: r_iter.next(),
                l_iter: l_iter,
                r_iter: r_iter,
            }
        }

        pub fn l_xor_r_next(&mut self) -> Option<&T> {
            loop {
                if let Some(l_item) = self.l_item {
                    if let Some(r_item) = self.r_item {
                        match l_item.cmp(&r_item) {
                            Ordering::Less => {
                                self.l_item = self.l_iter.next();
                                return Some(l_item);
                            }
                            Ordering::Greater => {
                                self.r_item = self.r_iter.next();
                                return Some(r_item);
                            }
                            Ordering::Equal => {
                                self.l_item = self.l_iter.next();
                                self.r_item = self.r_iter.next();
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

        pub fn are_disjoint_next(&mut self) -> bool {
            loop {
                if let Some(l_item) = self.l_item {
                    if let Some(r_item) = self.r_item {
                        match l_item.cmp(&r_item) {
                            Ordering::Less => {
                                self.l_item = self.l_iter.next();
                            }
                            Ordering::Greater => {
                                self.r_item = self.r_iter.next();
                            }
                            Ordering::Equal => {
                                return false;
                            }
                        }
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn it_works() {
            use std::slice::Iter;

            type Whatever<'a> = PairedIters::<'a, &'a str, Iter<'a, &'a str>, Iter<'a, &'a str>>;
        }
    }
}
