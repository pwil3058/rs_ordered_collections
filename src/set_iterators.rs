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

use crate::OrderedSet;

struct SSIntersection<'a, T: Ord> {
    l_set: &'a OrderedSet<T>,
    r_set: &'a OrderedSet<T>,
    l_index: usize,
    r_index: usize,
}

impl<'a, T: Ord> SSIntersection<'a, T> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let v1 = vec!["a", "c", "d", "g", "h", "i", "j", "l", "p", "x", "y", "z"];
        let v2 = vec!["b", "c", "e", "f", "h", "k", "m", "n", "o", "y"];
        let s1 = OrderedSet{ ordered_list: v1 };
        let s2 = OrderedSet{ ordered_list: v2 };

        let intersection = SSIntersection::new(&s1, &s2);
        let result: Vec<&str> = intersection.cloned().collect();
        assert_eq!(result, vec!["c", "h", "y"]);

        assert_eq!(2 + 2, 4);
    }
}
