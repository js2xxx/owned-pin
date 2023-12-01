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
pub mod sync;

#[doc(hidden)]
pub use core::{
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    pin::Pin,
};
use core::{ops::Deref, ptr::NonNull, sync::Exclusive};

pub use self::pointer::OnStack;

#[cfg(feature = "alloc")]
extern crate alloc;

/// A wrapper that both owns and pins data on the stack.
pub type OPin<'a, T> = Pin<OnStack<'a, T>>;

/// Represents a smart pointer whose pointed data can be safely moved out by
/// [`into_inner`](IntoInner::into_inner).
///
/// Implementing this trait proves the smart pointer owns its pointed data.
///
/// This trait doesn't require [`Deref`], because some smart pointers like `Rc`
/// shares its reference and may returns an option of the underlying data.
pub trait IntoInner {
    type Target;

    /// Move out the desired target, and call the possible dropping function of
    /// the additional metadata held by the pointer.
    fn into_inner(self) -> Self::Target;
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

impl<T> IntoInner for ManuallyDrop<T> {
    type Target = T;

    fn into_inner(self) -> Self::Target {
        ManuallyDrop::into_inner(self)
    }
}

unsafe impl<T> Uninit for ManuallyDrop<T> {
    type Uninit = ManuallyDrop<MaybeUninit<T>>;

    unsafe fn assume_init(this: Self::Uninit) -> Self {
        ManuallyDrop::new(unsafe { ManuallyDrop::into_inner(this).assume_init() })
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
    use core::{alloc::Allocator, mem::MaybeUninit, ptr::NonNull};

    use crate::{IntoInner, RawConvertable, Uninit};

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
/// desired type in the arguments of this macro.
///
/// The user can either write this pointer with a value to obtain the
/// initialized result, or use an [in-place initializer](OnStack::init).
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
    ($($ty:ty)?) => {
        $crate::on_stack!($crate::MaybeUninit$(::<$ty>)?::uninit())
    };
}

/// Initializes an owned value directly on the stack using an initializer of
/// [`Init`](pinned_init::Init).
///
/// # Examples
///
/// ```rust
/// use owned_pin::init_on_stack;
///
/// // This value is directly written to
/// // the target place, instead of being
/// // temporary place on the stack.
/// init_on_stack!(let x = [0; 100]);
/// assert_eq!(*x, [0; 100]);
/// ```
#[macro_export]
#[cfg(feature = "pinned-init")]
macro_rules! init_on_stack {
    (let $value:tt $(: $ty:ty)? = $init:expr) => {
        let __uninit = $crate::uninit_on_stack!();
        let $value = $crate::OnStack::init(__uninit, $init).unwrap();
    };
}

/// Attempts to initialize an owned value directly on the stack using an
/// initializer of [`Init`](pinned_init::Init).
///
/// # Examples
///
/// ```rust
/// use owned_pin::try_init_on_stack;
///
/// // This value is directly written to
/// // the target place, instead of being
/// // temporary place on the stack.
/// try_init_on_stack!(let x = [0; 100]);
/// assert_eq!(*x.unwrap(), [0; 100]);
/// ```
#[macro_export]
#[cfg(feature = "pinned-init")]
macro_rules! try_init_on_stack {
    (let $value:tt $(: $ty:ty)? = $init:expr) => {
        let __uninit = $crate::uninit_on_stack!();
        let $value = $crate::OnStack::init(__uninit, $init);
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
            pointer: $crate::on_stack!($value),
        }
    };
}

/// Pins an uninitialized value onto the current calling stack.
///
/// This macro is the shorthand for [`opin!(MaybeUninit::uninit())`](opin);
/// users can specify the desired type in the arguments of this macro.
///
/// To initialize this value, the [`pin_init`](OnStack::pin_init) method should
/// be used in most cases.
///
/// See [`pinned-init`](pinned_init) crate for how to directly initialize a
/// pinned value.
#[macro_export]
macro_rules! opin_uninit {
    ($($ty:ty)?) => {
        $crate::opin!($crate::MaybeUninit$(::<$ty>)?::uninit())
    };
}

/// Initializes and pins an owned value directly on the stack using an
/// initializer of [`PinInit`](pinned_init::PinInit).
///
/// # Examples
///
/// ```rust
/// use owned_pin::{opin_init, OPin};
/// use pinned_init::pin_data;
///
/// #[pin_data]
/// struct A {
///     x: u32
/// }
///
/// opin_init!(let a = A { x: 64 });
/// assert_eq!(a.x, 64);
/// ```
#[macro_export]
#[cfg(feature = "pinned-init")]
macro_rules! opin_init {
    (let $value:tt $(: $ty:ty)? = $init:expr) => {
        let __uninit = $crate::opin_uninit!($($ty:ty)?);
        let $value = $crate::OnStack::pin_init(__uninit, $init).unwrap();
    };
}

/// Attempts to initialize and pin an owned value directly on the stack using an
/// initializer of [`PinInit`](pinned_init::PinInit).
///
/// # Examples
///
/// ```rust
/// use owned_pin::{try_opin_init, OPin};
/// use pinned_init::pin_data;
///
/// #[pin_data]
/// struct A {
///     x: u32
/// }
///
/// try_opin_init!(let a = A { x: 64 });
/// assert_eq!(a.unwrap().x, 64);
#[macro_export]
#[cfg(feature = "pinned-init")]
macro_rules! try_opin_init {
    (let $value:tt $(: $ty:ty)? = $init:expr) => {
        let __uninit = $crate::opin_uninit!($($ty:ty)?);
        let $value = $crate::OnStack::pin_init(__uninit, $init);
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
