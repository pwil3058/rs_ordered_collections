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

///! Iterators over the output of pairs of ordered Iterators applying
///! various filters. If the Iterators contain no duplicates as well
///! as bing sorted then the filter will produce set operations.
use std::cmp::Ordering;

pub fn output_is_ordered_nodups<'a, T, I>(iter: &mut I) -> bool
where
    T: 'a + Ord,
    I: Iterator<Item = &'a T>,
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

pub struct XorIterator<'a, T, L, R>
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

impl<'a, T, L, R> XorIterator<'a, T, L, R>
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
}

impl<'a, T, L, R> Iterator for XorIterator<'a, T, L, R>
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
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
}

impl<'a, T, L, R> XorIterator<'a, T, L, R>
where
    T: 'a + Ord,
    L: Iterator<Item = &'a T>,
    R: Iterator<Item = &'a T>,
{
    pub fn xor<I: Iterator<Item = &'a T>>(self, iter: I) -> XorIterator<'a, T, XorIterator<'a, T, L, R>, I> {
        XorIterator::new(self, iter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    static LIST_0: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];
    static LIST_1: &[&str] = &["b", "d", "f", "h", "i", "k", "m"];
    static LIST_2: &[&str] = &[
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
    ];
    static LIST_UNORDERED: &[&str] = &["a", "c", "e", "z", "g", "i", "k", "m"];

    #[test]
    fn output_is_ordered_nodups_works() {
        assert!(output_is_ordered_nodups(&mut LIST_0.iter()));
        assert!(!output_is_ordered_nodups(&mut LIST_0.iter().rev()));
        assert!(!output_is_ordered_nodups(&mut LIST_UNORDERED.iter()));
        assert!(!output_is_ordered_nodups(&mut LIST_UNORDERED.iter().rev()));
    }

    #[test]
    fn xor_iterator_works() {
        let mut xor_iter = XorIterator::new(LIST_0[..3].iter(), LIST_1[..2].iter());
        assert_eq!(xor_iter.next(), Some(&"a"));
        let result: Vec<&str> = XorIterator::new(LIST_0[..3].iter(), LIST_1[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["a", "b", "c", "d", "e"]);
        let result: Vec<&str> = XorIterator::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["b", "c", "e"]);
        let result: Vec<&str> = XorIterator::new(LIST_0[..3].iter(), LIST_2[..2].iter())
            .xor(LIST_1[..3].iter())
            .cloned()
            .collect();
        assert_eq!(result, vec!["c", "d", "e", "f"]);
    }
}
