//Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.

use std::cmp::Ordering;

use crate::OrderedMap;
use crate::OrderedSet;

pub trait SetConversion<'a, T>: Iterator<Item = &'a T>
where
    T: 'a + Ord + Clone,
{
    /// Create a OrderedSet<T> from the items in the Iterator's output
    fn to_set(&mut self) -> OrderedSet<T> {
        OrderedSet::<T> {
            ordered_list: self.cloned().collect(),
        }
    }
}

macro_rules! define_set_operation {
    ( $iter_name:ident, $doc:meta ) => {
        #[$doc]
        pub struct $iter_name<'a, T: Ord> {
            l_set: &'a OrderedSet<T>,
            r_set: &'a OrderedSet<T>,
            l_index: usize,
            r_index: usize,
        }

        impl<'a, T: Ord> $iter_name<'a, T> {
            pub fn new(l_set: &'a OrderedSet<T>, r_set: &'a OrderedSet<T>) -> Self {
                Self {
                    l_set: l_set,
                    r_set: r_set,
                    l_index: 0,
                    r_index: 0,
                }
            }

            fn l_offset_to(&self, t: &T) -> usize {
                match self.l_set.ordered_list[self.l_index..].binary_search(t) {
                    Ok(index) => index,
                    Err(index) => index,
                }
            }

            fn r_offset_to(&self, t: &T) -> usize {
                match self.r_set.ordered_list[self.r_index..].binary_search(t) {
                    Ok(index) => index,
                    Err(index) => index,
                }
            }
        }

        impl<'a, T: Ord + Clone> SetConversion<'a, T> for $iter_name<'a, T> {}
    };
}

define_set_operation!(
    SSIntersection,
    doc = "An Iterator over the set intersection of two OrderedSets ordered according to Ord."
);

impl<'a, T: Ord> Iterator for SSIntersection<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_set.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_index += self.l_offset_to(r_item);
                        }
                        Ordering::Greater => {
                            self.r_index += self.r_offset_to(l_item);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                            return Some(l_item);
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

define_set_operation!(
    SSUnion,
    doc = "An Iterator over the set union of two OrderedSets ordered according to Ord."
);

impl<'a, T: Ord> Iterator for SSUnion<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_set.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_index += 1;
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_index += 1;
                            return Some(r_item);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                            return Some(l_item);
                        }
                    }
                } else {
                    self.l_index += 1;
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_set.ordered_list.get(self.r_index) {
                self.r_index += 1;
                return Some(r_item);
            } else {
                return None;
            }
        }
    }
}

define_set_operation!(
    SSDifference,
    doc = "An Iterator over the set difference of two OrderedSets ordered according to Ord
i.e. those items in the first set that do not appear in the second set."
);

impl<'a, T: Ord> Iterator for SSDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_set.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_index += 1;
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_index += self.r_offset_to(l_item);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                        }
                    }
                } else {
                    self.l_index += 1;
                    return Some(l_item);
                }
            } else {
                return None;
            }
        }
    }
}

define_set_operation!(
    SSSymmetricDifference,
    doc = "An Iterator over the set difference of two OrderedSets ordered according to Ord
i.e. those items in the first set that do not appear in the second set."
);

impl<'a, T: Ord> Iterator for SSSymmetricDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_set.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item) {
                        Ordering::Less => {
                            self.l_index += 1;
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_index += 1;
                            return Some(r_item);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                        }
                    }
                } else {
                    self.l_index += 1;
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_set.ordered_list.get(self.r_index) {
                self.r_index += 1;
                return Some(r_item);
            } else {
                return None;
            }
        }
    }
}

macro_rules! define_set_map_operation {
    ( $iter_name:ident, $doc:meta ) => {
        #[$doc]
        pub struct $iter_name<'a, T: Ord, V> {
            l_set: &'a OrderedSet<T>,
            r_map: &'a OrderedMap<T, V>,
            l_index: usize,
            r_index: usize,
        }

        impl<'a, T: Ord, V> $iter_name<'a, T, V> {
            pub fn new(l_set: &'a OrderedSet<T>, r_map: &'a OrderedMap<T, V>) -> Self {
                Self {
                    l_set: l_set,
                    r_map: r_map,
                    l_index: 0,
                    r_index: 0,
                }
            }

            fn l_offset_to(&self, t: &T) -> usize {
                match self.l_set.ordered_list[self.l_index..].binary_search(t) {
                    Ok(index) => index,
                    Err(index) => index,
                }
            }

            fn r_offset_to(&self, t: &T) -> usize {
                match self.r_map.ordered_list[self.r_index..].binary_search_by(|x| x.0.cmp(t)) {
                    Ok(index) => index,
                    Err(index) => index,
                }
            }
        }

        impl<'a, T: Ord + Clone, V> SetConversion<'a, T> for $iter_name<'a, T, V> {}
    };
}

define_set_map_operation!(
    SMIntersection,
    doc = "An Iterator over the set intersection of an OrderedSet and the keys of an OrderedMap
 ordered according to Ord."
);

impl<'a, T: Ord, V> Iterator for SMIntersection<'a, T, V> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_map.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item.0) {
                        Ordering::Less => {
                            self.l_index += self.l_offset_to(&r_item.0);
                        }
                        Ordering::Greater => {
                            self.r_index += self.r_offset_to(l_item);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                            return Some(l_item);
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

define_set_map_operation!(
    SMUnion,
    doc = "An Iterator over the set union of an OrderedSet and the keys of an OrderedMap
 ordered according to Ord."
);

impl<'a, T: Ord, V> Iterator for SMUnion<'a, T, V> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_map.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item.0) {
                        Ordering::Less => {
                            self.l_index += 1;
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_index += 1;
                            return Some(&r_item.0);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                            return Some(l_item);
                        }
                    }
                } else {
                    self.l_index += 1;
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_map.ordered_list.get(self.r_index) {
                self.r_index += 1;
                return Some(&r_item.0);
            } else {
                return None;
            }
        }
    }
}

define_set_map_operation!(
    SMDifference,
    doc = "An Iterator over the set difference of an OrderedSet and the keys of an OrderedMap
 ordered according to Ord."
);

impl<'a, T: Ord, V> Iterator for SMDifference<'a, T, V> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_map.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item.0) {
                        Ordering::Less => {
                            self.l_index += 1;
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_index += self.r_offset_to(l_item);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                        }
                    }
                } else {
                    self.l_index += 1;
                    return Some(l_item);
                }
            } else {
                return None;
            }
        }
    }
}

define_set_map_operation!(
    SMSymmetricDifference,
    doc = "An Iterator over the symmetric set difference of an OrderedSet and the keys of an OrderedMap
 ordered according to Ord."
);

impl<'a, T: Ord, V> Iterator for SMSymmetricDifference<'a, T, V> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(l_item) = self.l_set.ordered_list.get(self.l_index) {
                if let Some(r_item) = self.r_map.ordered_list.get(self.r_index) {
                    match l_item.cmp(&r_item.0) {
                        Ordering::Less => {
                            self.l_index += 1;
                            return Some(l_item);
                        }
                        Ordering::Greater => {
                            self.r_index += 1;
                            return Some(&r_item.0);
                        }
                        Ordering::Equal => {
                            self.l_index += 1;
                            self.r_index += 1;
                        }
                    }
                } else {
                    self.l_index += 1;
                    return Some(l_item);
                }
            } else if let Some(r_item) = self.r_map.ordered_list.get(self.r_index) {
                self.r_index += 1;
                return Some(&r_item.0);
            } else {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_intersection_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec!["b", "c", "e", "f", "h", "k", "m", "n", "o", "y"];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedSet { ordered_list: v2 };

        assert_eq!(
            SSIntersection::new(&s1, &s2).to_set().ordered_list,
            vec!["c", "h", "y"]
        );

        assert_eq!(
            SSIntersection::new(&s2, &s1).to_set().ordered_list,
            vec!["c", "h", "y"]
        );
    }

    #[test]
    fn set_union_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec!["b", "c", "e", "f", "h", "k", "m", "n", "o", "y"];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedSet { ordered_list: v2 };

        assert_eq!(
            SSUnion::new(&s1, &s2).to_set().ordered_list,
            vec![
                "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
                "x", "y", "z"
            ]
        );

        assert_eq!(
            SSUnion::new(&s2, &s1).to_set().ordered_list,
            vec![
                "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
                "x", "y", "z"
            ]
        );
    }

    #[test]
    fn set_difference_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec!["b", "c", "e", "f", "h", "k", "m", "n", "o", "y"];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedSet { ordered_list: v2 };

        assert_eq!(
            SSDifference::new(&s1, &s2).to_set().ordered_list,
            vec!["a", "d", "g", "i", "j", "l", "p", "x", "z"]
        );

        assert_eq!(
            SSDifference::new(&s2, &s1).to_set().ordered_list,
            vec!["b", "e", "f", "k", "m", "n", "o"]
        );
    }

    #[test]
    fn set_symmetric_difference_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec!["b", "c", "e", "f", "h", "k", "m", "n", "o", "y"];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedSet { ordered_list: v2 };

        let result = SSSymmetricDifference::new(&s1, &s2).to_set();
        assert_eq!(
            result.ordered_list,
            vec!["a", "b", "d", "e", "f", "g", "i", "j", "k", "l", "m", "n", "o", "p", "x", "z"]
        );

        assert_eq!(
            SSSymmetricDifference::new(&s2, &s1).to_set().ordered_list,
            vec!["a", "b", "d", "e", "f", "g", "i", "j", "k", "l", "m", "n", "o", "p", "x", "z"]
        );
    }

    #[test]
    fn set_map_intersection_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec![
            ("b", 0),
            ("c", 0),
            ("e", 0),
            ("f", 0),
            ("h", 0),
            ("k", 0),
            ("m", 0),
            ("n", 0),
            ("o", 0),
            ("y", 0),
        ];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedMap { ordered_list: v2 };

        assert_eq!(
            SMIntersection::new(&s1, &s2).to_set().ordered_list,
            vec!["c", "h", "y"]
        );
    }

    #[test]
    fn set_map_union_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec![
            ("b", 0),
            ("c", 0),
            ("e", 0),
            ("f", 0),
            ("h", 0),
            ("k", 0),
            ("m", 0),
            ("n", 0),
            ("o", 0),
            ("y", 0),
        ];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedMap { ordered_list: v2 };

        assert_eq!(
            SMUnion::new(&s1, &s2).to_set().ordered_list,
            vec![
                "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
                "x", "y", "z"
            ]
        );
    }

    #[test]
    fn set_map_difference_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec![
            ("b", 0),
            ("c", 0),
            ("e", 0),
            ("f", 0),
            ("h", 0),
            ("k", 0),
            ("m", 0),
            ("n", 0),
            ("o", 0),
            ("y", 0),
        ];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedMap { ordered_list: v2 };

        assert_eq!(
            SMDifference::new(&s1, &s2).to_set().ordered_list,
            vec!["a", "d", "g", "i", "j", "l", "p", "x", "z"]
        );
    }

    #[test]
    fn set_map_symmetric_difference_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec![
            ("b", 0),
            ("c", 0),
            ("e", 0),
            ("f", 0),
            ("h", 0),
            ("k", 0),
            ("m", 0),
            ("n", 0),
            ("o", 0),
            ("y", 0),
        ];
        let s1 = OrderedSet { ordered_list: v1 };
        let s2 = OrderedMap { ordered_list: v2 };

        assert_eq!(
            SMSymmetricDifference::new(&s1, &s2).to_set().ordered_list,
            vec!["a", "b", "d", "e", "f", "g", "i", "j", "k", "l", "m", "n", "o", "p", "x", "z"]
        );
    }
}
