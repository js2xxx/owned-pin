//! Types that own and pin data to its location in memory.
//!
//! While the [`Pin<P>`] wrapper in Rust's standard library enables pinning data
//! in memory, it has no guarantee of "owning" the pinned data, which prevents
//! the usage to semantically-but-not-concerning-memory moving the ownership of
//! the pinned data:
//!
//! ```rust,no_run
//! use core::pin::{Pin, pin};
//! use core::marker::PhantomPinned;
//!
//! fn try_to_take_the_ownership_of<T>(pinned: Pin<&mut T>) {}
//!
//! let mut value = pin!(PhantomPinned);
//! // The caller can reborrow the value...
//! try_to_take_the_ownership_of(value.as_mut());
//! // ... so the same pinned data can be used twice,
//! // thus unable to guarantee the move semantics.
//! try_to_take_the_ownership_of(value.as_mut());
//! ```
//!
//! Function implementors may use `unsafe` keyword to state the contract of
//! moving the ownership of the data. However, this remedy significantly
//! increases the difficulty of maintaining the code.
//!
//! In practice, this is because there is no such smart pointer that owns data
//! by holding a unique reference to some other location on the stack.
//!
//! Thus, we introduce the [`OnStack<T>`] smart pointer, which does the work
//! mentioned above in a memory-safe way, and a type alias [`OPin<T>`] =
//! `Pin<OnStack<T>>`, which both enable the example above to work as desired:
//!
//! ```rust,compile_fail
//! use owned_pin::{OPin, opin};
//! use core::marker::PhantomPinned;
//!
//! // `OPin<'a, T>` equals to `Pin<OnStack<'a, T>>`.
//! fn take_the_ownership_of<T>(owned_and_pinned: OPin<T>) {}
//!
//! let value = opin!(PhantomPinned);
//! // The `as_mut` method of `OPin` actually returns `Pin<&mut T>`...
//! take_the_ownership_of(value);
//! // ... so the value itself cannot be used again.
//! // The line below causes rustc to emit `E0382`.
//! take_the_ownership_of(value);
//! ```
//!
//! # `Unpin`
//!
//! `Pin<OnStack<T>>`'s moving semantics provides it with more functionality
//! than an ordinary `Pin<&mut T>`. For example, owning an `Unpin`ned data means
//! we can move out the raw data from this wrapper:
//!
//! ```rust
//! use owned_pin::{OPin, opin, unpin};
//!
//! fn take_the_ownership_of(pointer: OPin<String>) {
//!     // Wow! the unpinned ownership is now ours!
//!     let string: String = unpin(pointer);
//!     println!("{string}");
//! }
//!
//! take_the_ownership_of(opin!(String::from("Hello")));
//! ```
//!
//! This magic works safe and sound thanks to the full potential of
//! [`ManuallyDrop`], implying that the wrapped pointer actually points to a
//! `ManuallyDrop<T>`.
//!
//! Note that `Pin<Box<T>>` does all the things above as good as `OPin<T>`, and
//! the former can even be `'static` if `T` is `'static`. Nevertheless,
//! additional heap memory is consumed the achieve the result, which is
//! unrecommendable in memory-constraint scenarios.
//!
//! # Relationship with R-value references in C++
//!
//! This crate is in fact inspired by R-value references in C++, and `OPin<T>`
//! behaves more similar to R-value references than the original move semantics
//! in Rust and the `Pin<&mut T>` wrapper. However, there is still no "default
//! value" left when some data is `OPin`ned or moved out, guaranteeing the
//! memory safety requirements of Rust.
//!
//! The more detailed comparison is yet to be discussed.
//!
//! # Utilities
//!
//! Beside introducing the new `OnStack` type, we have also built some basic
//! data structures that can be pinned onto the stack, demonstrating some of its
//! potential by the way:
//!
//! - [`Arsc<P>`](sync::Arsc): an intrusive & thread-safe reference-counting
//!   pointer **wrapper**.
//!
//! Other utilities are currently under development.

#![no_std]
#![allow(internal_features)]
#![feature(allocator_api)]
#![feature(allow_internal_unstable)]
#![feature(coerce_unsized)]
#![feature(coroutine_trait)]
#![feature(dispatch_from_dyn)]
#![feature(exclusive_wrapper)]
#![feature(error_generic_member_access)]
#![feature(error_in_core)]
#![feature(fn_traits)]
#![feature(receiver_trait)]
#![feature(tuple_trait)]
#![feature(unboxed_closures)]
#![feature(unsize)]
#![cfg_attr(feature = "alloc", feature(new_uninit))]

mod pointer;
#[cfg(target_has_atomic = "ptr")]
pub mod sync;

#[doc(hidden)]
pub use core::{
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    pin::Pin,
};
use core::{ops::Deref, ptr::NonNull};

#[doc(hidden)]
pub use pinned_init::{init, pin_init};

pub use self::pointer::OnStack;

#[cfg(feature = "alloc")]
extern crate alloc;

/// A wrapper that both owns and pins data on the stack.
pub type OPin<'a, T> = Pin<OnStack<'a, T>>;

/// Represents a smart pointer whose pointed data can be safely moved out by
/// [`into_inner`](IntoInner::into_inner).
///
/// Implementing this trait proves the smart pointer owns its pointed data.
pub trait IntoInner: Unpin + Deref {
    /// Move out the desired target, and call the possible dropping function of
    /// the additional metadata held by the pointer.
    fn into_inner(self) -> Self::Target;

    /// Move out the desired target, and call the possible dropping function of
    /// the additional metadata held by the pointer.
    fn try_unwrap(this: Self) -> Result<Self::Target, Self>
    where
        Self::Target: Sized,
        Self: Sized,
    {
        Ok(this.into_inner())
    }
}

/// Smart pointers that can convert themselves into raw forms, and is able to
/// convert raw forms back to themselves.
///
/// # Safety
///
/// The implementor of this trait must enable any valid raw form to be converted
/// back to its corresponding valid smart pointer.
pub unsafe trait RawConvertable: Deref {
    /// The additional metadata needed to be converted back.
    type Metadata: Sized;

    /// Converts a smart pointer into its raw form.
    fn into_raw(this: Self) -> (NonNull<Self::Target>, Self::Metadata);

    /// Converts the raw form of a smart pointer back.
    ///
    /// # Safety
    ///
    /// `pointer` and `metadata` must be the ones that is previously returned
    /// from the same call of [`into_raw`](RawConvertable::into_raw).
    unsafe fn from_raw(pointer: NonNull<Self::Target>, metadata: Self::Metadata) -> Self;
}

/// Smart pointers that can convert their uninitialized forms into initialized
/// forms.
///
/// # Safety
///
/// The implementor of this trait must enable any valid uninitialized form to
/// convert to its corresponding valid initialized form.
pub unsafe trait Uninit: Deref
where
    <Self as Deref>::Target: Sized,
{
    type Uninit: Deref<Target = MaybeUninit<Self::Target>>;

    /// Converts to its initialized form.
    ///
    /// # Safety
    ///
    /// See [`MaybeUninit::assume_init`] for more information.
    unsafe fn assume_init(this: Self::Uninit) -> Self;
}

unsafe impl<T> Uninit for ManuallyDrop<T> {
    type Uninit = ManuallyDrop<MaybeUninit<T>>;

    unsafe fn assume_init(this: Self::Uninit) -> Self {
        ManuallyDrop::new(unsafe { ManuallyDrop::into_inner(this).assume_init() })
    }
}

#[cfg(feature = "alloc")]
mod alloc2 {
    use alloc::{boxed::Box, rc::Rc, sync::Arc};
    use core::{alloc::Allocator, mem::MaybeUninit, ptr::NonNull};

    use crate::{IntoInner, RawConvertable, Uninit};

    impl<T, A: Allocator + 'static> IntoInner for Box<T, A> {
        fn into_inner(self) -> T {
            *self
        }
    }

    impl<T, A: Allocator> IntoInner for Rc<T, A> {
        fn into_inner(self) -> T {
            Rc::into_inner(self).unwrap()
        }

        fn try_unwrap(this: Self) -> Result<T, Self> {
            Rc::try_unwrap(this)
        }
    }

    impl<T, A: Allocator> IntoInner for Arc<T, A> {
        fn into_inner(self) -> T {
            Arc::into_inner(self).unwrap()
        }

        fn try_unwrap(this: Self) -> Result<T, Self> {
            Arc::try_unwrap(this)
        }
    }

    // SAFETY: The implementation of `Box`es is correct.
    unsafe impl<T, A: Allocator> RawConvertable for Box<T, A> {
        type Metadata = A;

        /// See [`Box::into_raw_with_allocator`] for more information.
        fn into_raw(this: Self) -> (NonNull<T>, A) {
            let (ptr, alloc) = Box::into_raw_with_allocator(this);
            // SAFETY: The pointer to the heap memory is always not-null, whether its
            // dangling for ZSTs for not.
            (unsafe { NonNull::new_unchecked(ptr) }, alloc)
        }

        /// See [`Box::from_raw_in`] for more information.
        unsafe fn from_raw(pointer: NonNull<T>, metadata: A) -> Self {
            // SAFETY: The safety requirement is upheld by the caller.
            unsafe { Box::from_raw_in(pointer.as_ptr(), metadata) }
        }
    }

    // SAFETY: The implementation of `Rc`s is correct.
    unsafe impl<T, A: Allocator + Clone> RawConvertable for Rc<T, A> {
        type Metadata = A;

        /// See [`Rc::into_raw`] and [`Rc::allocator`] for more information.
        fn into_raw(this: Self) -> (NonNull<T>, A) {
            let alloc = Rc::allocator(&this).clone();
            let ptr = Rc::into_raw(this);
            // SAFETY: The pointer to the heap memory is always not-null, whether its
            // dangling for ZSTs for not.
            (unsafe { NonNull::new_unchecked(ptr.cast_mut()) }, alloc)
        }

        /// See [`Rc::from_raw_in`] for more information.
        unsafe fn from_raw(pointer: NonNull<T>, metadata: A) -> Self {
            // SAFETY: The safety requirement is upheld by the caller.
            unsafe { Rc::from_raw_in(pointer.as_ptr(), metadata) }
        }
    }

    // SAFETY: The implementation of `Rc`s is correct.
    unsafe impl<T, A: Allocator + Clone> RawConvertable for Arc<T, A> {
        type Metadata = A;

        /// See [`Rc::into_raw`] and [`Rc::allocator`] for more information.
        fn into_raw(this: Self) -> (NonNull<T>, A) {
            let alloc = Arc::allocator(&this).clone();
            let ptr = Arc::into_raw(this);
            // SAFETY: The pointer to the heap memory is always not-null, whether its
            // dangling for ZSTs for not.
            (unsafe { NonNull::new_unchecked(ptr.cast_mut()) }, alloc)
        }

        /// See [`Rc::from_raw_in`] for more information.
        unsafe fn from_raw(pointer: NonNull<T>, metadata: A) -> Self {
            // SAFETY: The safety requirement is upheld by the caller.
            unsafe { Arc::from_raw_in(pointer.as_ptr(), metadata) }
        }
    }

    unsafe impl<T, A: Allocator> Uninit for Box<T, A> {
        type Uninit = Box<MaybeUninit<T>, A>;

        unsafe fn assume_init(this: Self::Uninit) -> Self {
            Box::<MaybeUninit<T>, A>::assume_init(this)
        }
    }

    unsafe impl<T, A: Allocator + Clone> Uninit for Rc<T, A> {
        type Uninit = Rc<MaybeUninit<T>, A>;

        unsafe fn assume_init(this: Self::Uninit) -> Self {
            Rc::<MaybeUninit<T>, A>::assume_init(this)
        }
    }

    unsafe impl<T, A: Allocator + Clone> Uninit for Arc<T, A> {
        type Uninit = Arc<MaybeUninit<T>, A>;

        unsafe fn assume_init(this: Self::Uninit) -> Self {
            Arc::<MaybeUninit<T>, A>::assume_init(this)
        }
    }
}

/// Moves out the underlying pinned value, if it is `Unpin`.
///
/// See the example in the documentation of [`opin`] for more information.
pub fn unpin<P>(pinned: Pin<P>) -> P::Target
where
    P: Deref + IntoInner,
    P::Target: Unpin + Sized,
{
    Pin::into_inner(pinned).into_inner()
}

/// Attempts to move out the underlying pinned value, if it is `Unpin`.
///
/// When the underlying pointer fails to unwrap the value, the original pinned
/// pointer is returned, wrapped in [`Err`].
///
/// See the example in the documentation of [`opin`] for more information.
pub fn try_unpin<P>(pinned: Pin<P>) -> Result<P::Target, Pin<P>>
where
    P: Deref + IntoInner,
    P::Target: Unpin + Sized,
{
    P::try_unwrap(Pin::into_inner(pinned)).map_err(Pin::new)
}
