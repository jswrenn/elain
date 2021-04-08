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
//! struct Foo<const N: usize> {
//!     _align: Align<N>,
//! }
//! ```
//! To resolve this error, add a `where` bound like so, using the
//! [`Alignment`] trait to check that `Align<N>` is valid.
//!
//! ```
//! use elain::{Align, Alignment};
//! use core::mem::align_of;
//!
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
use core::hash::Hash;
use core::fmt::Debug;

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
/// struct Foo {
///     _align: Align<FOO_ALIGN>,
/// }
///
/// let foo: Foo = Foo { _align: Align::NEW };
///
/// assert_eq!(align_of_val(&foo), 8);
/// ```
#[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[repr(transparent)]
pub struct Align<const N: usize>(<Self as Alignment>::Archetype)
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
    /// let foo: Foo = Foo { _align: Align::new() };
    ///
    /// assert_eq!(align_of_val(&foo), 8);
    /// ```
    pub const NEW: Self = Self(<Self as Alignment>::ARCHETYPE);
}

/// Implemented for all `Align<N>` where `N` is a valid alignment
/// (i.e., a power of two less-than-or-equal to 2<sup>28</sup>).
///
/// ```
/// use elain::{Align, Alignment};
/// use core::mem::align_of;
///
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
pub unsafe trait Alignment: private::Sealed {
    /// A zero-sized type of particular alignment.
    type Archetype
      : Debug
      + Default
      + Copy
      + Clone
      + Hash
      + Eq
      + PartialEq<Self::Archetype>
      + Ord
      + PartialOrd<Self::Archetype>;

    /// An instance of zero-sized types.
    const ARCHETYPE: Self::Archetype;
}

mod private {
    pub trait Sealed {}

    impl Sealed for super::Align<        1> {}
    impl Sealed for super::Align<        2> {}
    impl Sealed for super::Align<        4> {}
    impl Sealed for super::Align<        8> {}
    impl Sealed for super::Align<       16> {}
    impl Sealed for super::Align<       32> {}
    impl Sealed for super::Align<       64> {}
    impl Sealed for super::Align<      128> {}
    impl Sealed for super::Align<      256> {}
    impl Sealed for super::Align<      512> {}
    impl Sealed for super::Align<     1024> {}
    impl Sealed for super::Align<     2048> {}
    impl Sealed for super::Align<     4096> {}
    impl Sealed for super::Align<     8192> {}
    impl Sealed for super::Align<    16384> {}
    impl Sealed for super::Align<    32768> {}
    impl Sealed for super::Align<    65536> {}
    impl Sealed for super::Align<   131072> {}
    impl Sealed for super::Align<   262144> {}
    impl Sealed for super::Align<   524288> {}
    impl Sealed for super::Align<  1048576> {}
    impl Sealed for super::Align<  2097152> {}
    impl Sealed for super::Align<  4194304> {}
    impl Sealed for super::Align<  8388608> {}
    impl Sealed for super::Align< 16777216> {}
    impl Sealed for super::Align< 33554432> {}
    impl Sealed for super::Align< 67108864> {}
    impl Sealed for super::Align<134217728> {}
    impl Sealed for super::Align<268435456> {}

    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(        1))] pub struct Alignment1;        
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(        2))] pub struct Alignment2;        
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(        4))] pub struct Alignment4;        
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(        8))] pub struct Alignment8;        
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(       16))] pub struct Alignment16;       
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(       32))] pub struct Alignment32;       
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(       64))] pub struct Alignment64;       
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(      128))] pub struct Alignment128;      
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(      256))] pub struct Alignment256;      
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(      512))] pub struct Alignment512;      
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(     1024))] pub struct Alignment1024;     
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(     2048))] pub struct Alignment2048;     
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(     4096))] pub struct Alignment4096;     
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(     8192))] pub struct Alignment8192;     
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(    16384))] pub struct Alignment16384;    
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(    32768))] pub struct Alignment32768;    
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(    65536))] pub struct Alignment65536;    
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(   131072))] pub struct Alignment131072;   
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(   262144))] pub struct Alignment262144;   
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(   524288))] pub struct Alignment524288;   
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(  1048576))] pub struct Alignment1048576;  
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(  2097152))] pub struct Alignment2097152;  
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(  4194304))] pub struct Alignment4194304;  
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(  8388608))] pub struct Alignment8388608;  
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align( 16777216))] pub struct Alignment16777216; 
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align( 33554432))] pub struct Alignment33554432; 
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align( 67108864))] pub struct Alignment67108864; 
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(134217728))] pub struct Alignment134217728;
    #[derive(Debug, Default, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)] #[repr(C, align(268435456))] pub struct Alignment268435456;
}

unsafe impl Alignment for Align<        1> { type Archetype = private::Alignment1;         const ARCHETYPE: Self::Archetype = private::Alignment1;         }
unsafe impl Alignment for Align<        2> { type Archetype = private::Alignment2;         const ARCHETYPE: Self::Archetype = private::Alignment2;         }
unsafe impl Alignment for Align<        4> { type Archetype = private::Alignment4;         const ARCHETYPE: Self::Archetype = private::Alignment4;         }
unsafe impl Alignment for Align<        8> { type Archetype = private::Alignment8;         const ARCHETYPE: Self::Archetype = private::Alignment8;         }
unsafe impl Alignment for Align<       16> { type Archetype = private::Alignment16;        const ARCHETYPE: Self::Archetype = private::Alignment16;        }
unsafe impl Alignment for Align<       32> { type Archetype = private::Alignment32;        const ARCHETYPE: Self::Archetype = private::Alignment32;        }
unsafe impl Alignment for Align<       64> { type Archetype = private::Alignment64;        const ARCHETYPE: Self::Archetype = private::Alignment64;        }
unsafe impl Alignment for Align<      128> { type Archetype = private::Alignment128;       const ARCHETYPE: Self::Archetype = private::Alignment128;       }
unsafe impl Alignment for Align<      256> { type Archetype = private::Alignment256;       const ARCHETYPE: Self::Archetype = private::Alignment256;       }
unsafe impl Alignment for Align<      512> { type Archetype = private::Alignment512;       const ARCHETYPE: Self::Archetype = private::Alignment512;       }
unsafe impl Alignment for Align<     1024> { type Archetype = private::Alignment1024;      const ARCHETYPE: Self::Archetype = private::Alignment1024;      }
unsafe impl Alignment for Align<     2048> { type Archetype = private::Alignment2048;      const ARCHETYPE: Self::Archetype = private::Alignment2048;      }
unsafe impl Alignment for Align<     4096> { type Archetype = private::Alignment4096;      const ARCHETYPE: Self::Archetype = private::Alignment4096;      }
unsafe impl Alignment for Align<     8192> { type Archetype = private::Alignment8192;      const ARCHETYPE: Self::Archetype = private::Alignment8192;      }
unsafe impl Alignment for Align<    16384> { type Archetype = private::Alignment16384;     const ARCHETYPE: Self::Archetype = private::Alignment16384;     }
unsafe impl Alignment for Align<    32768> { type Archetype = private::Alignment32768;     const ARCHETYPE: Self::Archetype = private::Alignment32768;     }
unsafe impl Alignment for Align<    65536> { type Archetype = private::Alignment65536;     const ARCHETYPE: Self::Archetype = private::Alignment65536;     }
unsafe impl Alignment for Align<   131072> { type Archetype = private::Alignment131072;    const ARCHETYPE: Self::Archetype = private::Alignment131072;    }
unsafe impl Alignment for Align<   262144> { type Archetype = private::Alignment262144;    const ARCHETYPE: Self::Archetype = private::Alignment262144;    }
unsafe impl Alignment for Align<   524288> { type Archetype = private::Alignment524288;    const ARCHETYPE: Self::Archetype = private::Alignment524288;    }
unsafe impl Alignment for Align<  1048576> { type Archetype = private::Alignment1048576;   const ARCHETYPE: Self::Archetype = private::Alignment1048576;   }
unsafe impl Alignment for Align<  2097152> { type Archetype = private::Alignment2097152;   const ARCHETYPE: Self::Archetype = private::Alignment2097152;   }
unsafe impl Alignment for Align<  4194304> { type Archetype = private::Alignment4194304;   const ARCHETYPE: Self::Archetype = private::Alignment4194304;   }
unsafe impl Alignment for Align<  8388608> { type Archetype = private::Alignment8388608;   const ARCHETYPE: Self::Archetype = private::Alignment8388608;   }
unsafe impl Alignment for Align< 16777216> { type Archetype = private::Alignment16777216;  const ARCHETYPE: Self::Archetype = private::Alignment16777216;  }
unsafe impl Alignment for Align< 33554432> { type Archetype = private::Alignment33554432;  const ARCHETYPE: Self::Archetype = private::Alignment33554432;  }
unsafe impl Alignment for Align< 67108864> { type Archetype = private::Alignment67108864;  const ARCHETYPE: Self::Archetype = private::Alignment67108864;  }
unsafe impl Alignment for Align<134217728> { type Archetype = private::Alignment134217728; const ARCHETYPE: Self::Archetype = private::Alignment134217728; }
unsafe impl Alignment for Align<268435456> { type Archetype = private::Alignment268435456; const ARCHETYPE: Self::Archetype = private::Alignment268435456; }
