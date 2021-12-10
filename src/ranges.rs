use std::ops::{Bound, RangeBounds};
use ranges::GenericRange;
use crate::Val;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Ranges {
    inner: ranges::Ranges<Val>,
}

impl Ranges {
    pub fn new(from: Bound<Val>, to: Bound<Val>) -> Self {
        Self {
            inner: ranges::Ranges::from((from, to)),
        }
    }

    #[inline]
    pub fn intersection<R: Into<Ranges>>(&mut self, other: R) {
        let left = std::mem::replace(&mut self.inner, Default::default());
        self.inner = left & other.into().inner;
    }

    #[inline]
    pub fn contains(&self, val: Val) -> bool {
        self.inner.contains(&val)
    }

    #[inline]
    pub fn remove<R: RangeBounds<Val>>(&mut self, range: R) {
        self.inner.remove(GenericRange::new_with_bounds(
            range.start_bound().cloned(),
            range.end_bound().cloned(),
        ));
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        let mut total = 0;

        for i in self.inner.as_slice() {
            let min = match i.start_bound() {
                Bound::Included(val) => *val,
                Bound::Excluded(val) => val + 1,
                Bound::Unbounded => unreachable!(),
            };

            let max = match i.end_bound() {
                Bound::Included(val) => *val,
                Bound::Excluded(val) => val - 1,
                Bound::Unbounded => unreachable!(),
            };

            total += max - min + 1;
        }

        total as _
    }

    pub fn get_bounds(&self) -> Option<(Val, Val)> {
        let slice = self.inner.as_slice();
        let first = slice.get(0)?.start_bound();
        let last = slice.get(slice.len() - 1)?.end_bound();

        let min = match first {
            Bound::Included(val) => *val,
            Bound::Excluded(val) => val + 1,
            Bound::Unbounded => unreachable!(),
        };

        let max = match last {
            Bound::Included(val) => *val,
            Bound::Excluded(val) => val - 1,
            Bound::Unbounded => unreachable!(),
        };

        Some((min, max))
    }

    #[inline]
    pub fn insert(&mut self, from: Bound<Val>, to: Bound<Val>) {
        self.inner.insert(GenericRange::new_with_bounds(from, to));
    }

    pub fn iter(&self) -> impl Iterator<Item = Val> + '_ {
        self.inner
            .as_slice()
            .iter()
            .map(|x| x.into_iter())
            .flatten()
    }
}

impl<T: Into<ranges::Ranges<Val>>> From<T> for Ranges {
    fn from(range: T) -> Self {
        Self {
            inner: range.into(),
        }
    }
}
