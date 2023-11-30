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
#![no_std]
#![allow(internal_features)]
#![feature(allocator_api)]
#![feature(allow_internal_unstable)]
#![feature(coerce_unsized)]
#![feature(coroutine_trait)]
#![feature(exclusive_wrapper)]
#![feature(error_generic_member_access)]
#![feature(error_in_core)]
#![feature(fn_traits)]
#![feature(dispatch_from_dyn)]
#![feature(tuple_trait)]
#![feature(unboxed_closures)]
#![feature(unsize)]

mod pointer;

#[doc(hidden)]
pub use core::{
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    pin::Pin,
};
use core::{ops::Deref, sync::Exclusive};

pub use self::pointer::OnStack;

#[cfg(feature = "alloc")]
extern crate alloc;

/// A wrapper that both owns and pins data on the stack.
pub type OPin<'a, T> = Pin<OnStack<'a, T>>;

/// Represents a smart pointer whose pointed data can be safely moved out by
/// [`into_inner`](IntoInner::into_inner).
///
/// This trait doesn't require [`Deref`], because some smart pointers like `Rc`
/// shares its reference and may returns an option of the underlying data.
pub trait IntoInner {
    type Target;

    /// Move out the desired target, and call the possible dropping function of
    /// the additional metadata held by the pointer.
    fn into_inner(self) -> Self::Target;
}

impl<T> IntoInner for ManuallyDrop<T> {
    type Target = T;

    fn into_inner(self) -> Self::Target {
        ManuallyDrop::into_inner(self)
    }
}

impl<T> IntoInner for Exclusive<T> {
    type Target = T;

    fn into_inner(self) -> Self::Target {
        self.into_inner()
    }
}

#[cfg(feature = "alloc")]
mod alloc2 {
    use alloc::{boxed::Box, rc::Rc, sync::Arc};
    use core::alloc::Allocator;

    use crate::IntoInner;

    impl<T, A: Allocator> IntoInner for Box<T, A> {
        type Target = T;

        fn into_inner(self) -> T {
            *self
        }
    }

    impl<T, A: Allocator> IntoInner for Rc<T, A> {
        type Target = Option<T>;

        fn into_inner(self) -> Self::Target {
            Rc::into_inner(self)
        }
    }

    impl<T, A: Allocator> IntoInner for Arc<T, A> {
        type Target = Option<T>;

        fn into_inner(self) -> Self::Target {
            Arc::into_inner(self)
        }
    }
}

/// Constructs a smart pointer [on the current calling stack](OnStack) from the
/// value.
///
/// Unlike other pointers like `Box<T>`, this returned pointer consumes no
/// additional memory on the heap, at the cost of restricted lifetime of the
/// current calling context.
///
/// This pointer serves no additional functionality, unless used with [`Pin`].
///
/// # Examples
///
/// ```rust
/// // Basic usage
/// use owned_pin::{on_stack, IntoInner};
///
/// let pointer = on_stack!(String::from("Hello!"));
/// let string = IntoInner::into_inner(pointer);
/// assert_eq!(string, "Hello!");
/// ```
///
/// ```rust
/// // Pinning the pointer
/// use owned_pin::{on_stack, OnStack};
///
/// let pointer = on_stack!(String::from("Hello!"));
/// let pinned = OnStack::into_pin(pointer);
/// // Use this pinned pointer while keeping the semantic ownership.
/// ```
#[macro_export]
macro_rules! on_stack {
    ($value:expr) => {
        $crate::OnStack {
            inner: &mut $crate::ManuallyDrop::new($value),
            marker: $crate::PhantomData,
        }
    };
}

/// Constructs an uninitialized smart pointer [on the current calling
/// stack](OnStack).
///
/// This macro is the shorthand for
/// [`on_stack!(MaybeUninit::uninit())`](on_stack); users can specify the
/// desired type in the argument of this macro.
///
/// The user can later write this pointer with a value to obtain the initialized
/// result.
///
/// # Examples
///
/// ```rust
/// use owned_pin::{uninit_on_stack, OnStack};
///
/// let uninit = uninit_on_stack!(String);
/// let pointer = OnStack::write(uninit, "Hello!".into());
/// assert_eq!(*pointer, "Hello!");
/// ```
#[macro_export]
macro_rules! uninit_on_stack {
    ($ty:ty) => {
        $crate::on_stack!($crate::MaybeUninit::<$ty>::uninit())
    };
    () => {
        $crate::on_stack!($crate::MaybeUninit::uninit())
    };
}

/// Pins a value onto the current calling stack.
///
/// If the value is `Unpin`, the user can safety [move out](unpin) the value and
/// use it again.
///
/// # Examples
///
/// ```rust
/// use owned_pin::{opin, unpin};
///
/// // Pins the value onto the stack.
/// let pinned = opin!(String::from("Hello!"));
/// // Retrieves back the data because `String` is `Unpin`.
/// let string: String = unpin(pinned);
/// assert_eq!(string, "Hello!");
/// ```
#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
macro_rules! opin {
    ($value:expr) => {
        $crate::Pin {
            pointer: $crate::OnStack {
                inner: &mut $crate::ManuallyDrop::new($value),
                marker: $crate::PhantomData,
            },
        }
    };
}

/// Moves out the underlying pinned value, if it is `Unpin`.
///
/// See the example in the documentation of [`opin`] for more information.
pub fn unpin<P>(pinned: Pin<P>) -> <P as IntoInner>::Target
where
    P: Deref + IntoInner,
    <P as Deref>::Target: Unpin + Sized,
{
    Pin::into_inner(pinned).into_inner()
}
