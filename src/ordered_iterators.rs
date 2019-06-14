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

pub trait OrderedIterator<'a, T: 'a + Ord> : Iterator<Item=&'a T> {
    fn next_after(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value > target {
                return Some(value)
            }
        }
        None
    }

    fn next_before(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value < target {
                return Some(value)
            }
        }
        None
    }

    fn next_from(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value >= target {
                return Some(value)
            }
        }
        None
    }

    fn next_until(&mut self, target: &T) -> Option<&'a T> {
        while let Some(value) = self.next() {
            if value <= target {
                return Some(value)
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::slice::Iter;

    impl<'a, T: 'a + Ord> OrderedIterator<'a, T> for Iter<'a, T> {}

    static LIST: &[&str] = &["a", "c", "e", "g", "i", "k", "m"];

    #[test]
    fn next_before_works() {
        assert_eq!(LIST.iter().next_before(&"g"), Some(&"a"));
        assert_eq!(LIST.iter().next_before(&"a"), None);
        let mut iter = LIST.iter();
        assert_eq!(iter.next_before(&"c"), Some(&"a"));
        assert_eq!(iter.next_before(&"c"), None);
    }

    #[test]
    fn next_until_works() {
        assert_eq!(LIST.iter().next_until(&"g"), Some(&"a"));
        assert_eq!(LIST.iter().next_until(&"a"), Some(&"a"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_until(&"a"), Some(&"a"));
        assert_eq!(iter.next_until(&"a"), None);
    }

    #[test]
    fn next_from_works() {
        assert_eq!(LIST.iter().next_from(&"g"), Some(&"g"));
        assert_eq!(LIST.iter().next_from(&"a"), Some(&"a"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_from(&"m"), Some(&"m"));
        assert_eq!(iter.next_from(&"m"), None);
    }

    #[test]
    fn next_after_works() {
        assert_eq!(LIST.iter().next_after(&"g"), Some(&"i"));
        assert_eq!(LIST.iter().next_after(&"a"), Some(&"c"));
        let mut iter = LIST.iter();
        assert_eq!(iter.next_after(&"k"), Some(&"m"));
        assert_eq!(iter.next_after(&"k"), None);
    }
}
