//! Iterate over the bits set in a word.
//!
//! A `BitIter` may be constructed from any integral value.
//!
//! A `BitIter` may be constructed from any integral value, and returns the positions of the `1`
//! bits in ascending order.
//!
//! `BitIter` implements `DoubleEndedIterator`, so you can iterate over the positions of the set
//! bits in descending order too.
//!
//! ## Example
//!
//! ```rust
//! # use bit_iter::*;
//! let x : u32 = 0x10001;
//!
//! for (b, _) in BitIter::from(x) {
//!     println!("Bit {} is set.", b);
//! }
//!
//! println!("In reverse order:");
//!
//! for (b, _) in BitIter::from(x).rev() {
//!     println!("Bit {} is set.", b);
//! }
//! ```
//!
//! Output:
//!
//! ```text
//! Bit 0 is set.
//! Bit 16 is set.
//! In reverse order:
//! Bit 16 is set.
//! Bit 0 is set.
//! ```

#![no_std]
#![doc(html_root_url = "https://docs.rs/bit-iter/1.1.1")]

use core::{
    iter::{ExactSizeIterator, FusedIterator},
    mem::size_of,
};

#[cfg(test)]
mod tests;

/// An iterator which returns the positions of the set bits in a word, in ascending order.
///
/// ## Examples
///
/// Construct a `BitIter` from an integer:
///
/// ```rust
/// # use bit_iter::*;
/// let mut iter = BitIter::from(0b10000001);
/// assert_eq!(iter.next(), Some((0u32, 1 << 0)));
/// assert_eq!(iter.next(), Some((7u32, 1 << 7)));
/// assert_eq!(iter.next(), None);
/// ```
///
/// Iterate over the bits in an integer in ascending order:
///
/// ```rust
/// # use bit_iter::*;
/// let v : Vec<(u32, i32)> = BitIter::from(0b10000001).collect();
/// assert_eq!(v, vec![(0, 1 << 0), (7, 1 << 7)]);
/// ```
///
/// `BitIter` implements `DoubleEndedIterator`, so you can also get the set bit positions in
/// descending order:
///
/// ```rust
/// # use bit_iter::*;
/// let v : Vec<(u32, i32)> = BitIter::from(0b10000001).rev().collect();
/// assert_eq!(v, vec![(7, 1 << 7), (0, 1 << 0)]);
/// ```
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct BitIter<T>(T);

macro_rules! iter_impl {
    ($($t:ty)*) => {$(
        /// `From` implementation for `BitIter`.
        impl From<$t> for BitIter<$t> {
            /// Construct a BitIter value.
            #[inline]
            fn from(value: $t) -> Self {
                Self(value)
            }
        }

        /// `Iterator` implementation for `BitIter`.
        impl Iterator for BitIter<$t> {
            type Item = (u32, $t);

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                if self.0 != 0 {
                    let trailing = self.0.trailing_zeros();
                    let bit = self.0 & self.0.wrapping_neg();
                    self.0 &= self.0.wrapping_sub(1);
                    Some((trailing, bit))
                } else {
                    None
                }
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                let sz = self.0.count_ones() as usize;
                (sz, Some(sz))
            }

            #[inline]
            fn count(self) -> usize {
                self.0.count_ones() as usize
            }

            #[inline]
            fn last(self) -> Option<Self::Item> {
                if self.0 != 0 {
                    let leading = self.0.leading_zeros();
                    Some((8 * size_of::<$t>() as u32 - 1 - leading, (1 as $t).rotate_right(1).rotate_right(leading)))
                } else {
                    None
                }
            }

            #[inline]
            fn nth(&mut self, n: usize) -> Option<Self::Item> {
                let mut i = 0;
                while self.0 != 0 && i < n {
                    self.0 &= self.0.wrapping_sub(1);
                    i += 1;
                }
                self.next()
            }

            #[inline]
            fn fold<B, F>(mut self, init: B, mut f: F) -> B
            where
                F: FnMut(B, Self::Item) -> B
            {
                let mut accum = init;
                while self.0 != 0 {
                    accum = f(accum, (self.0.trailing_zeros(), self.0 & self.0.wrapping_neg()));
                    self.0 &= self.0.wrapping_sub(1);
                }
                accum
            }

            #[inline]
            fn max(self) -> Option<Self::Item> {
                self.last()
            }

            #[inline]
            fn min(self) -> Option<Self::Item> {
                if self.0 != 0 {
                    Some((self.0.trailing_zeros(), self.0 & self.0.wrapping_neg()))
                } else {
                    None
                }
            }
        }

        /// `FusedIterator` implementation for `BitIter`.
        impl FusedIterator for BitIter<$t> {}

        /// `DoubleEndedIterator` implementation for `BitIter`.
        impl DoubleEndedIterator for BitIter<$t> {
            #[inline]
            fn next_back(&mut self) -> Option<Self::Item> {
                if self.0 != 0 {
                    let leading = self.0.leading_zeros();
                    let highest = 8 * size_of::<$t>() as u32 - 1 - leading;
                    let bit = (1 as $t).rotate_right(1).rotate_right(leading);
                    self.0 ^= bit;
                    Some((highest, bit))
                } else {
                    None
                }
            }
        }

        /// `ExactSizeIterator` implementation for `BitIter`.
        impl ExactSizeIterator for BitIter<$t> {
            #[inline]
            fn len(&self) -> usize {
                self.0.count_ones() as usize
            }
        }
    )*}
}

iter_impl! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
