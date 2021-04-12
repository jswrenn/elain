//! Set the minimum alignments of types using const generics, rather
//! than `#[repr(align(N))]`.
//!
//! ## Basic Use
//! The type [`Align<N>`](Align) is a zero-sized-type with alignment
//! equal to `N`:
//! ```
//! use elain::Align;
//! use core::mem::{align_of, align_of_val};
//!
//! assert_eq!(align_of::<Align<1>>(), 1);
//! assert_eq!(align_of::<Align<2>>(), 2);
//! assert_eq!(align_of::<Align<4>>(), 4);
//!
//! const FOO_ALIGN: usize = 8;
//!
//! #[repr(C)]
//! struct Foo {
//!     _align: Align<FOO_ALIGN>,
//! }
//!
//! let foo: Foo = Foo { _align: Align::NEW };
//!
//! assert_eq!(align_of_val(&foo), 8);
//! ```
//!
//! Valid alignments are powers of two less-than-or-equal to 2<sup>28</sup>.
//! Supplying an *invalid* alignment to [`Align`] is a type error:
//! ```compile_fail
//! use elain::Align;
//!
//! struct Foo(Align<3>); // Compile Error
//! ```
//!
//! ## Generic Use
//! Because only *some* integers are valid alignments, supplying the
//! alignment of a type generically requires some extra work:
//! ```compile_fail
//! use elain::Align;
//!
//! #[repr(C)]
//! struct Foo<const N: usize> {
//!     _align: Align<N>,
//! }
//! ```
//! To resolve this error, add a `where` bound like so, using the
//! [`Alignment`] trait to check that [`Align<N>`](Align) is valid.
//!
//! ```
//! use elain::{Align, Alignment};
//! use core::mem::align_of;
//!
//! #[repr(C)]
//! struct Foo<const MIN_ALIGNMENT: usize>
//! where
//!     Align<MIN_ALIGNMENT>: Alignment
//! {
//!     _align: Align<MIN_ALIGNMENT>,
//!     bar: u8,
//!     baz: u16,
//! }
//!
//! assert_eq!(align_of::<Foo<1>>(), 2);
//! assert_eq!(align_of::<Foo<2>>(), 2);
//! assert_eq!(align_of::<Foo<4>>(), 4);
//! ```
#![no_std]
use core::{
    cmp::{PartialOrd, Ordering},
    fmt::{self, Debug},
    hash::{Hash, Hasher},
};

/// A zero-sized-type aligned to `N`. Compound types containing a
/// field `Align<N>` with have an alignment of *at least* `N`.
///
/// ```
/// use elain::Align;
/// use core::mem::{align_of, align_of_val};
///
/// assert_eq!(align_of::<Align<1>>(), 1);
/// assert_eq!(align_of::<Align<2>>(), 2);
/// assert_eq!(align_of::<Align<4>>(), 4);
///
/// const FOO_ALIGN: usize = 8;
///
/// #[repr(C)]
/// struct Foo {
///     _align: Align<FOO_ALIGN>,
/// }
///
/// let foo: Foo = Foo { _align: Align::NEW };
///
/// assert_eq!(align_of_val(&foo), 8);
/// ```
// NB: `Eq` and `PartialEq` are derived so that `Align` also
// implements `StructuralEq` and `PartialStructuralEq`, which makes
// `Align` usable as a const generic type. Just in case.
#[derive(Eq, PartialEq)]
#[repr(transparent)]
pub struct Align<const N: usize>([<Self as private::Sealed>::Archetype; 0])
where
    Self: Alignment;


impl<const N: usize> Align<N>
where
    Self: Alignment
{
    /// An instance of `Align<N>`.
    /// ```
    /// use elain::Align;
    /// use core::mem::{align_of, align_of_val};
    ///
    /// #[repr(C)]
    /// struct Foo {
    ///     _align: Align<8>,
    /// }
    ///
    /// let foo: Foo = Foo { _align: Align::NEW };
    ///
    /// assert_eq!(align_of_val(&foo), 8);
    /// ```
    pub const NEW: Self = Self([]);
}

/// Implemented for all [`Align<N>`](Align) where `N` is a
/// valid alignment (i.e., a power of two less-than-or-equal to
/// 2<sup>28</sup>).
///
/// ```
/// use elain::{Align, Alignment};
/// use core::mem::align_of;
///
/// #[repr(C)]
/// struct Foo<const MIN_ALIGNMENT: usize>
/// where
///     Align<MIN_ALIGNMENT>: Alignment
/// {
///     _align: Align<MIN_ALIGNMENT>,
///     bar: u8,
///     baz: u16,
/// }
///
/// assert_eq!(align_of::<Foo<1>>(), 2);
/// assert_eq!(align_of::<Foo<2>>(), 2);
/// assert_eq!(align_of::<Foo<4>>(), 4);
/// ```
pub unsafe trait Alignment: private::Sealed {}

mod private {
    /// This trait is used internally to map an `Align<N>` to a unit
    /// struct of alignment N.
    pub trait Sealed {
        /// A zero-sized type of particular alignment.
        type Archetype: Copy + Eq + PartialEq + Send + Sync + Unpin;
    }

    impl Sealed for super::Align<        1> { type Archetype = Align1;         }
    impl Sealed for super::Align<        2> { type Archetype = Align2;         }
    impl Sealed for super::Align<        4> { type Archetype = Align4;         }
    impl Sealed for super::Align<        8> { type Archetype = Align8;         }
    impl Sealed for super::Align<       16> { type Archetype = Align16;        }
    impl Sealed for super::Align<       32> { type Archetype = Align32;        }
    impl Sealed for super::Align<       64> { type Archetype = Align64;        }
    impl Sealed for super::Align<      128> { type Archetype = Align128;       }
    impl Sealed for super::Align<      256> { type Archetype = Align256;       }
    impl Sealed for super::Align<      512> { type Archetype = Align512;       }
    impl Sealed for super::Align<     1024> { type Archetype = Align1024;      }
    impl Sealed for super::Align<     2048> { type Archetype = Align2048;      }
    impl Sealed for super::Align<     4096> { type Archetype = Align4096;      }
    impl Sealed for super::Align<     8192> { type Archetype = Align8192;      }
    impl Sealed for super::Align<    16384> { type Archetype = Align16384;     }
    impl Sealed for super::Align<    32768> { type Archetype = Align32768;     }
    impl Sealed for super::Align<    65536> { type Archetype = Align65536;     }
    impl Sealed for super::Align<   131072> { type Archetype = Align131072;    }
    impl Sealed for super::Align<   262144> { type Archetype = Align262144;    }
    impl Sealed for super::Align<   524288> { type Archetype = Align524288;    }
    impl Sealed for super::Align<  1048576> { type Archetype = Align1048576;   }
    impl Sealed for super::Align<  2097152> { type Archetype = Align2097152;   }
    impl Sealed for super::Align<  4194304> { type Archetype = Align4194304;   }
    impl Sealed for super::Align<  8388608> { type Archetype = Align8388608;   }
    impl Sealed for super::Align< 16777216> { type Archetype = Align16777216;  }
    impl Sealed for super::Align< 33554432> { type Archetype = Align33554432;  }
    impl Sealed for super::Align< 67108864> { type Archetype = Align67108864;  }
    impl Sealed for super::Align<134217728> { type Archetype = Align134217728; }
    impl Sealed for super::Align<268435456> { type Archetype = Align268435456; }

    // NB: It'd be great if these could be void enums, as doing so
    // greatly simplifies the expansion of derived traits.
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(        1))] pub struct Align1         {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(        2))] pub struct Align2         {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(        4))] pub struct Align4         {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(        8))] pub struct Align8         {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(       16))] pub struct Align16        {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(       32))] pub struct Align32        {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(       64))] pub struct Align64        {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(      128))] pub struct Align128       {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(      256))] pub struct Align256       {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(      512))] pub struct Align512       {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(     1024))] pub struct Align1024      {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(     2048))] pub struct Align2048      {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(     4096))] pub struct Align4096      {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(     8192))] pub struct Align8192      {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(    16384))] pub struct Align16384     {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(    32768))] pub struct Align32768     {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(    65536))] pub struct Align65536     {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(   131072))] pub struct Align131072    {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(   262144))] pub struct Align262144    {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(   524288))] pub struct Align524288    {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(  1048576))] pub struct Align1048576   {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(  2097152))] pub struct Align2097152   {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(  4194304))] pub struct Align4194304   {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(  8388608))] pub struct Align8388608   {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align( 16777216))] pub struct Align16777216  {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align( 33554432))] pub struct Align33554432  {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align( 67108864))] pub struct Align67108864  {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(134217728))] pub struct Align134217728 {}
    #[derive(Copy, Clone, Eq, PartialEq)] #[repr(align(268435456))] pub struct Align268435456 {}
}

// NB: While these impls could be reduced to a single:
//    unsafe impl<const N: usize> Alignment for Align<N>
//    where
//        Self: private::Sealed
//    {}
// …leaving them enumerated makes explicit what alignments are valid.
unsafe impl Alignment for Align<        1> {}
unsafe impl Alignment for Align<        2> {}
unsafe impl Alignment for Align<        4> {}
unsafe impl Alignment for Align<        8> {}
unsafe impl Alignment for Align<       16> {}
unsafe impl Alignment for Align<       32> {}
unsafe impl Alignment for Align<       64> {}
unsafe impl Alignment for Align<      128> {}
unsafe impl Alignment for Align<      256> {}
unsafe impl Alignment for Align<      512> {}
unsafe impl Alignment for Align<     1024> {}
unsafe impl Alignment for Align<     2048> {}
unsafe impl Alignment for Align<     4096> {}
unsafe impl Alignment for Align<     8192> {}
unsafe impl Alignment for Align<    16384> {}
unsafe impl Alignment for Align<    32768> {}
unsafe impl Alignment for Align<    65536> {}
unsafe impl Alignment for Align<   131072> {}
unsafe impl Alignment for Align<   262144> {}
unsafe impl Alignment for Align<   524288> {}
unsafe impl Alignment for Align<  1048576> {}
unsafe impl Alignment for Align<  2097152> {}
unsafe impl Alignment for Align<  4194304> {}
unsafe impl Alignment for Align<  8388608> {}
unsafe impl Alignment for Align< 16777216> {}
unsafe impl Alignment for Align< 33554432> {}
unsafe impl Alignment for Align< 67108864> {}
unsafe impl Alignment for Align<134217728> {}
unsafe impl Alignment for Align<268435456> {}


// NB: These traits are implemented explicitly, rather than derived,
// because their implementations do not depend on `Align`'s field.

impl<const N: usize> Copy for Align<N>
where
    Self: Alignment
{}

impl<const N: usize> Clone for Align<N>
where
    Self: Alignment
{
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<const N: usize> Debug for Align<N>
where
    Self: Alignment
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(core::any::type_name::<Self>())
    }
}

impl<const N: usize> Default for Align<N>
where
    Self: Alignment
{
    #[inline(always)]
    fn default() -> Self {
        Self([])
    }
}

impl<const N: usize> Hash for Align<N>
where
    Self: Alignment
{
    #[inline(always)]
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

impl<const N: usize> Ord for Align<N>
where
    Self: Alignment
{
    #[inline(always)]
    fn cmp(&self, _: &Self) -> Ordering {
        Ordering::Equal
    }
}

impl<const N: usize> PartialOrd<Self> for Align<N>
where
    Self: Alignment
{
    #[inline(always)]
    fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
        Some(Ordering::Equal)
    }
}
