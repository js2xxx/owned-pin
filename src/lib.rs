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
//! Thus, we introduce the [`OPin<T, P>`] wrapper, which both "own" and
//! "pin" the data in the memory, enabling the example above to work as desired:
//!
//! ```rust,compile_fail
//! use owned_pin::{OPin, opin};
//! use core::marker::PhantomPinned;
//!
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
//! `OPin<T, P>`'s moving semantics provides it with more functionality than
//! `Pin<P>`. For example, owning an `Unpin`ned data means we can move out the
//! raw data from this wrapper:
//!
//! ```rust
//! use owned_pin::{OPin, opin};
//!
//! fn take_the_ownership_of(pointer: OPin<String>) {
//!     // Wow! the unpinned ownership is now ours!
//!     let string: String = OPin::unpin(pointer);
//!     println!("{string}");
//! }
//!
//! take_the_ownership_of(opin!(String::from("Hello")));
//! ```
//!
//! This magic works safe and sound thanks to the full potential of
//! [`ManuallyDrop`], implying that the wrapped pointer actually points to a
//! `ManuallyDrop<T>`. This means if users want to provide their own pointer,
//! the resulting type signature would be something lengthy like `OPin<'static,
//! T, Box<ManuallyDrop<T>>>`.
//!
//! This is sadly compulsory by far, due to the little support of generic type
//! constructors in Rust (while generic associated types can achieve this by
//! defining a type family trait, the implementors of custom pointers should
//! also implement that trait, which is unwilling for them to depend on this
//! crate just for this sake).
//!
//! # Relationship with R-value references in C++
//!
//! This crate is in fact inspired by R-value references in C++, and `OPin<T,
//! P>` behaves more similar to R-value references than the original move
//! semantics in Rust and the `Pin<P>` wrapper. However, there is still no
//! "default value" left when some data is `OPin`ned or moved out, guaranteeing
//! the memory safety requirements of Rust.
//!
//! The more detailed comparison is yet to be discussed.
//!
//! # Third-party utilities
//!
//! So far, all the third-party crates that provide utilities of pinned data,
//! such as [`pin-project`](https://crates.io/crates/pin-project), have been
//! focused only on the `Pin<P>` wrapper, with which the
//! [`as_mut`](OPin::as_mut) method of every `OPin` can safely provide. Hence,
//! users of `OPin`s can integrate this crate with such utilities trivially.
#![no_std]
#![allow(internal_features)]
#![feature(allocator_api)]
#![feature(allow_internal_unsafe)]
#[cfg(feature = "alloc")]
mod boxed;

#[doc(hidden)]
pub use core::{marker::PhantomData, mem::ManuallyDrop};
use core::{
    mem::{self},
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr,
};

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
pub use self::boxed::*;

/// An owned and pinned pointer.
///
/// This is a wrapper around a kind of pointer which makes that pointer "own"
/// and "pin" its value in place, preventing the value referenced by that
/// pointer from being moved unless it implements [`Unpin`].
///
/// Unlike [`Pin<P>`], which can reborrow itself to a shorter lifetime of
/// `Pin<&T>` or `Pin<&mut T>`, this wrapper makes the pointer "own" its value,
/// and thus cannot reborrow itself. This enables the wrapper to manually
/// ["transfer"](OPin::unpin) the ownership of the value to any desired place if
/// the value is `Unpin`, working like an R-value reference in C++.
///
/// `OPin<'_, T, P>` is guaranteed to have the same memory layout and ABI as
/// `P`.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct OPin<'a, T, P = &'a mut ManuallyDrop<T>>
where
    T: ?Sized,
    P: DerefMut<Target = ManuallyDrop<T>> + 'a,
{
    #[doc(hidden)]
    pub pointer: P,
    #[doc(hidden)]
    pub marker: PhantomData<&'a mut ()>,
}

impl<'a, T, P> OPin<'a, T, P>
where
    T: ?Sized,
    P: DerefMut<Target = ManuallyDrop<T>> + 'a,
{
    /// Construct a new `OPin` from a **OWNED** pointer to `ManuallyDrop<T>`.
    ///
    /// Note that there's no alternative like `OPin::new` even if `T` implements
    /// [`Unpin`], because the ownership of the value is semantically moved into
    /// this structure and cannot be used again even after this `OPin` drops.
    ///
    /// # Safety
    ///
    /// The value bebind the pointer must not be used anymore once this function
    /// is called, which is a stronger restriction than [`Pin::new_unchecked`].
    /// If such requirement is not satisfied, that is a violation of the API
    /// contract and may lead to undefined behavior in later (safe) operations.
    pub unsafe fn new_unchecked(pointer: P) -> Self {
        OPin {
            pointer,
            marker: PhantomData,
        }
    }

    /// Get a pinned shared reference from this pinned pointer.
    ///
    /// See [`Pin::as_ref`] for more information.
    pub fn as_ref(&self) -> Pin<&T> {
        // SAFETY: The underlying reference is semantically pinned.
        unsafe { Pin::new_unchecked(&self.pointer) }
    }

    /// Get a pinned mutable reference from this pinned pointer.
    ///
    /// See [`Pin::as_mut`] for more information.
    pub fn as_mut(&mut self) -> Pin<&mut T>
    where
        P: DerefMut<Target = ManuallyDrop<T>>,
    {
        // SAFETY: The underlying pointer is semantically pinned.
        unsafe { Pin::new_unchecked(&mut self.pointer) }
    }
}

impl<'a, T, P> Deref for OPin<'a, T, P>
where
    T: ?Sized,
    P: DerefMut<Target = ManuallyDrop<T>> + 'a,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.pointer.deref()
    }
}

impl<'a, T, P> OPin<'a, T, P>
where
    T: Unpin,
    P: DerefMut<Target = ManuallyDrop<T>> + 'a,
{
    /// Move out the underlying value, if it is `Unpin`.
    pub fn unpin(this: OPin<'a, T, P>) -> T {
        // SAFETY: The underlying pointer OWNS its value by the contract stated in
        // `OPin::new_unchecked`, and the value is `Unpin`.
        unsafe {
            let mut pointer = ptr::read(&this.pointer);
            // Forgetting the `OPin` prevents the pointer from double dropping.
            mem::forget(this);
            // The value inside the pointer won't be dropped twice since we only move out
            // the value once.
            ManuallyDrop::take(pointer.deref_mut())
        }
    }

    /// Consume the object and return the underlying pointer.
    ///
    /// The returned pointer actually points to a [`ManuallyDrop<T>`], so the
    /// user should manually drop the value inside the pointer, since we cannot
    /// deduce the type information and transmutes it to some pointer type that
    /// can automatically drop the pointed value.
    pub fn into_inner(this: OPin<'a, T, P>) -> P {
        // SAFETY: The underlying pointer OWNS its value by the contract stated in
        // `OPin::new_unchecked`, and the value is `Unpin`.
        unsafe {
            let pointer = ptr::read(&this.pointer);
            // Forgetting the `OPin` prevents the pointer from double dropping.
            mem::forget(this);
            pointer
        }
    }
}

impl<'a, T, P> DerefMut for OPin<'a, T, P>
where
    T: ?Sized + Unpin,
    P: DerefMut<Target = ManuallyDrop<T>> + 'a,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.pointer.deref_mut()
    }
}

impl<'a, T, P> Drop for OPin<'a, T, P>
where
    T: ?Sized,
    P: DerefMut<Target = ManuallyDrop<T>> + 'a,
{
    fn drop(&mut self) {
        // SAFETY: The underlying pointer OWNS its value by the contract stated in
        // `OPin::new_unchecked`.
        unsafe { ManuallyDrop::drop(self.pointer.deref_mut()) }
    }
}

/// Pin a value onto the current calling stack.
///
/// If the value is `Unpin`, the user can safety [move out](OPin::unpin) the
/// value and use it again.
///
/// # Examples
///
/// ```rust
/// use owned_pin::{opin, OPin};
///
/// // Pins the value onto the stack.
/// let pinned = opin!(String::from("Hello!"));
/// // Retrieves back the data because `String` is `Unpin`.
/// let string = OPin::unpin(pinned);
/// ```
#[macro_export]
#[allow_internal_unsafe]
macro_rules! opin {
    ($value:expr) => {
        $crate::OPin {
            pointer: &mut $crate::ManuallyDrop::new($value),
            marker: $crate::PhantomData,
        }
    };
}
