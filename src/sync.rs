//! This module deals with intrusive & thread-safe reference-counting pointers.
//!
//! See the [`Arsc<P>`] documentation for more details.
//!
//! **Note**: This module is only available on platforms that support atomic
//! loads and stores of pointers. This may be detected at compile time using
//! `#[cfg(target_has_atomic = "ptr")]`.

#[cfg(feature = "pinned-init")]
use core::alloc::AllocError;
use core::{
    error::Error,
    fmt,
    hash::Hash,
    mem::{self, ManuallyDrop},
    ops::{CoerceUnsized, Deref, DerefMut},
    panic::UnwindSafe,
    pin::Pin,
    ptr::{self, NonNull},
    sync::atomic::{self, AtomicUsize, Ordering::*},
};

pub use owned_pin_macros::RefCounted;
#[cfg(feature = "pinned-init")]
use pinned_init::InPlaceInit;

pub use crate::{apin, arsc_on_stack};
#[cfg(feature = "pinned-init")]
pub use crate::{apin_init, arsc_init_on_stack, arsc_try_init_on_stack, try_apin_init};
use crate::{IntoInner, OnStack, RawConvertable};

const REF_COUNT_MAX: usize = (isize::MAX) as usize;
#[cfg(target_pointer_width = "64")]
const REF_COUNT_SATURATED: usize = 0xC000_0000_0000_0000;
#[cfg(target_pointer_width = "32")]
const REF_COUNT_SATURATED: usize = 0xC000_0000;

/// An intrusive reference counter.
///
/// Users should place this structure into their own type, and implement
/// [`RefCounted`] to enable the support for intrusive ref-counting.
///
/// The ways to initialize a `RefCount` is only to use its
/// [`new`](RefCount::new) method or use the [`Default`] trait.
///
/// For users who want some `unsafe` hints, when some type including this
/// structure wants to implement `Clone`, a new instance of `RefCount` should be
/// assigned to the cloned value, or undefined behavior will happen in place.
/// Hence, no "byte copying" should be considered.
#[derive(Debug)]
pub struct RefCount {
    count: AtomicUsize,
}

impl RefCount {
    /// Creates a new intrusive reference counter.
    ///
    /// The user should not and cannot modify this structure by any means.
    pub const fn new() -> Self {
        RefCount {
            count: AtomicUsize::new(1),
        }
    }

    /// Retrives the current reference count.
    ///     
    /// The user should not and cannot modify this structure by any means.
    pub fn get(&self) -> usize {
        self.count.load(Acquire)
    }
}

impl Default for RefCount {
    fn default() -> Self {
        Self::new()
    }
}

/// Types that is intrusively ref-countable.
///
/// Implmementing this trait enables every smart pointer `P` of this type to be
/// wrapped in [`Arsc<P>`], making it to be an Atomic Reference Strongly Counted
/// smart pointer.
///
/// Users usually don't want to implement this trait manually, and use a derive
/// macro instead:
///
/// ```rust
/// use owned_pin::sync::{RefCount, RefCounted};
///
/// #[derive(RefCounted)]
/// struct A {
///     // Only one field should be marked `#[count_on]`.
///     #[count_on]
///     rc: RefCount,
///     _x: i32,
/// }
///
/// #[derive(RefCounted)]
/// enum B {
///     // Only one field should be marked `#[count_on]`...
///     _X(u8, #[count_on] A),
///     _Y {
///         y: &'static str,
///         // ... in each variant of the enum.
///         #[count_on]
///         a: A,
///     },
/// }
///
/// // Unions don't support deriving this trait.
/// ```
///
/// # Safety
///
/// `ref_count` must return a static offset in the memory layout of the
/// implementor type.
pub unsafe trait RefCounted {
    /// Gets the reference counter stored within this type.
    fn ref_count(&self) -> &RefCount;
}

unsafe impl RefCounted for RefCount {
    fn ref_count(&self) -> &RefCount {
        self
    }
}

/// A type wrapper represents an [`Arsc`] pointer pinned onto the stack.
///
/// See [the type level documentation](Arsc) for more information.
pub type APin<'a, T> = Pin<Arsc<OnStack<'a, T>>>;

/// A wrapper that enables thread-safe Atomic Reference Strongly Counting on
/// arbitrary smart pointers.
///
/// Like `Arc<T>` in the Rust standard library, `Arsc<P>` provides shared
/// ownership of a value of type `T` where `P: Deref<Target = T>`.
///
/// Unlike `Arc<T>`, the actual storage position of `T`, including the one of
/// its reference counter, depends on the actual implementation of `P`.
///
/// # Examples
///
/// Allocating memory on the heap:
///
/// ```rust
/// # #[cfg(feature = "alloc")]
/// # {
///
/// use owned_pin::sync::{Arsc, ArscExt, RefCount, RefCounted};
///
/// #[derive(RefCounted)]
/// struct A {
///     value: &'static str,
///     #[count_on]
///     rc: RefCount,
/// }
///
/// let arsc: Arsc<Box<A>> = Box::arsc(A {
///     value: "Hello!",
///     rc: RefCount::new(),
/// });
/// let cloned = arsc.clone();
///
/// assert!(Arsc::ptr_eq(&arsc, &cloned));
///
/// # }
/// ```
///
/// Pin it onto the stack using [`apin`]:
///
/// ```rust
/// use owned_pin::sync::{Arsc, RefCount, RefCounted, apin};
/// use owned_pin::OnStack;
///
/// #[derive(RefCounted)]
/// struct A {
///     value: &'static str,
///     #[count_on]
///     rc: RefCount,
/// }
///
/// // `arsc` is `Pin<Arsc<OnStack<A>>>`.
/// apin!(let arsc = A {
///     value: "Hello!",
///     rc: RefCount::new(),
/// });
/// // All the clones share the same lifetime.
/// let cloned = arsc.clone();
/// ```
#[repr(transparent)]
pub struct Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    #[doc(hidden)]
    pub pointer: ManuallyDrop<P>,
}

unsafe impl<P> Send for Arsc<P>
where
    P: Deref + Send + Sync,
    P::Target: RefCounted,
{
}

unsafe impl<P> Sync for Arsc<P>
where
    P: Deref + Send + Sync,
    P::Target: RefCounted,
{
}

impl<P> UnwindSafe for Arsc<P>
where
    P: Deref + UnwindSafe,
    P::Target: RefCounted,
{
}

impl<P> Unpin for Arsc<P>
where
    P: Deref + Unpin,
    P::Target: RefCounted,
{
}

impl<P> Error for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + Error,
{
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.deref().source()
    }

    fn provide<'a>(&'a self, request: &mut core::error::Request<'a>) {
        self.deref().provide(request)
    }
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    unsafe fn from_pointer(inner: P) -> Arsc<P> {
        Arsc {
            pointer: ManuallyDrop::new(inner),
        }
    }

    unsafe fn into_pointer(mut this: Arsc<P>) -> P {
        unsafe {
            let inner = ManuallyDrop::take(&mut this.pointer);
            mem::forget(this);
            inner
        }
    }
}

/// Creates an [`Arsc`] pointer on the current calling stack.
///
/// The syntax of this macro is different from the syntax of
/// [`on_stack`](crate::on_stack), due to its own implementation and the
/// restriction on lifetime extensions of temporary values in Rust.
///
/// # Examples
///
/// ```rust
/// use owned_pin::sync::{Arsc, RefCount, RefCounted, arsc_on_stack};
/// use owned_pin::OnStack;
///
/// #[derive(RefCounted)]
/// struct A {
///     value: &'static str,
///     #[count_on]
///     rc: RefCount,
/// }
///
/// // `arsc` is `Arsc<OnStack<A>>`.
/// arsc_on_stack!(let arsc = A {
///     value: "Hello!",
///     rc: RefCount::new(),
/// });
/// // All the clones share the same lifetime.
/// let cloned = arsc.clone();
/// assert!(Arsc::ptr_eq(&arsc, &cloned));
/// ```
#[macro_export]
macro_rules! arsc_on_stack {
    (let $value:ident = $init:expr) => {
        let __on_stack = $crate::on_stack!($init);
        let $value = $crate::sync::Arsc {
            pointer: $crate::ManuallyDrop::new(__on_stack),
        };
    };
}

/// Creates and pins an [`Arsc`] pointer on the current calling stack.
///
/// The syntax of this macro is different from the syntax of
/// [`opin`](crate::opin), due to its own implementation and the restriction on
/// lifetime extensions of temporary values in Rust.
///
/// # Examples
///
/// ```rust
/// use owned_pin::sync::{Arsc, RefCount, RefCounted, apin};
/// use owned_pin::OnStack;
///
/// #[derive(RefCounted)]
/// struct A {
///     value: &'static str,
///     #[count_on]
///     rc: RefCount,
/// }
///
/// // `arsc` is `Pin<Arsc<OnStack<A>>>`.
/// apin!(let arsc = A {
///     value: "Hello!",
///     rc: RefCount::new(),
/// });
/// // All the clones share the same lifetime.
/// let cloned = arsc.clone();
/// ```
#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
macro_rules! apin {
    (let $value:ident = $init:expr) => {
        $crate::arsc_on_stack!(let __of_arsc = $init);
        let $value = $crate::Pin { pointer: __of_arsc };
    };
}

/// An extension trait on smart pointers which own its pointed data, and whose
/// actual storage is on a static place in memory.
///
/// See the [`arsc`](ArscExt::arsc) and [`apin`](ArscExt::apin) method
/// for more information.
pub trait ArscExt: Deref + From<<Self as Deref>::Target> + IntoInner
where
    <Self as Deref>::Target: RefCounted + Sized,
{
    /// Creates an [`Arsc`] based on the storage of this smart pointer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "alloc")]
    /// # {
    ///
    /// use owned_pin::sync::{Arsc, ArscExt, RefCount, RefCounted};
    ///
    /// #[derive(RefCounted)]
    /// struct A {
    ///     value: &'static str,
    ///     #[count_on]
    ///     rc: RefCount,
    /// }
    ///
    /// // `Box<T: RefCounted>` implements `ArscExt`.
    /// let arsc: Arsc<Box<A>> = Box::arsc(A {
    ///     value: "Hello!",
    ///     rc: RefCount::new(),
    /// });
    /// let cloned = arsc.clone();
    ///
    /// assert!(Arsc::ptr_eq(&arsc, &cloned));
    ///
    /// # }
    /// ```
    fn arsc(value: <Self as Deref>::Target) -> Arsc<Self> {
        Arsc::from(value)
    }

    /// Creates and pins an [`Arsc`] based on the storage of this smart pointer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "alloc")]
    /// # {
    ///
    /// use owned_pin::sync::{Arsc, ArscExt, RefCount, RefCounted};
    /// use std::pin::Pin;
    ///
    /// #[derive(RefCounted)]
    /// struct A {
    ///     value: &'static str,
    ///     #[count_on]
    ///     rc: RefCount,
    /// }
    ///
    /// // `Box<T: RefCounted>` implements `ArscExt`.
    /// let arsc: Pin<Arsc<Box<A>>> = Box::apin(A {
    ///     value: "Hello!",
    ///     rc: RefCount::new(),
    /// });
    /// let cloned = arsc.clone();
    ///
    /// # }
    /// ```
    fn apin(value: <Self as Deref>::Target) -> Pin<Arsc<Self>> {
        // The inner pointer pins it owned data in memory by the contract in `Unpin`.
        unsafe { Pin::new_unchecked(Arsc::from(value)) }
    }
}

impl<T> ArscExt for T
where
    T: Deref + From<<Self as Deref>::Target> + IntoInner,
    <T as Deref>::Target: RefCounted + Sized,
{
}

#[cfg(feature = "pinned-init")]
impl<P, T> InPlaceInit<T> for Arsc<P>
where
    P: Deref<Target = T> + InPlaceInit<T> + IntoInner,
    T: RefCounted,
{
    fn try_pin_init<E>(init: impl pinned_init::PinInit<T, E>) -> Result<Pin<Self>, E>
    where
        E: From<AllocError>,
    {
        Ok(Self::into_pin(P::try_pin_init(init)?))
    }

    fn try_init<E>(init: impl pinned_init::Init<T, E>) -> Result<Self, E>
    where
        E: From<AllocError>,
    {
        Ok(Self::new(P::try_init(init)?))
    }
}

/// Attempts to initialize an [`Arsc`] pointer on the current calling stack.
///
/// # Examples
///
/// ```rust
/// use owned_pin::sync::{RefCount, RefCounted, arsc_try_init_on_stack};
///
/// #[derive(RefCounted)]
/// struct Large {
///     x: [u64; 100],
///     #[count_on]
///     rc: RefCount,
/// }
///
/// // This value is directly written to the target place,
/// // instead of being temporarily placed on the stack.
/// arsc_try_init_on_stack!(let l = Large {
///     x <- [0; 100],
///     rc: RefCount::new(),
/// });
/// assert_eq!(l.unwrap().x, [0; 100]);
/// ```
#[macro_export]
#[cfg(feature = "pinned-init")]
macro_rules! arsc_try_init_on_stack {
    (let $value:ident $(:$ty:ty)? = $($init:tt)*) => {
        $crate::try_init_on_stack!(let __init $(:$ty)? = $($init)*);
        let $value = __init.map(|__p| $crate::sync::Arsc {
            pointer: $crate::ManuallyDrop::new(__p)
        });
    };
}

/// Initializes an [`Arsc`] pointer on the current calling stack using an
/// initializer of [`Init`](pinned_init::Init).
///
/// # Examples
///
/// ```rust
/// use owned_pin::sync::{RefCount, RefCounted, arsc_init_on_stack};
///
/// #[derive(RefCounted)]
/// struct Large {
///     x: [u64; 100],
///     #[count_on]
///     rc: RefCount,
/// }
///
/// // This value is directly written to the target place,
/// // instead of being temporarily placed on the stack.
/// arsc_init_on_stack!(let l = Large {
///     x <- [0; 100],
///     rc: RefCount::new(),
/// });
/// assert_eq!(l.x, [0; 100]);
/// ```
#[macro_export]
#[cfg(feature = "pinned-init")]
macro_rules! arsc_init_on_stack {
    (let $value:ident $(:$ty:ty)? = $($init:tt)*) => {
        $crate::init_on_stack!(let __init $(:$ty)? = $($init)*);
        let $value = $crate::sync::Arsc {
            pointer: $crate::ManuallyDrop::new(__init)
        };
    };
}

/// Attempts to initialize and pin an [`Arsc`] pointer on the current calling
/// stack.
///
/// # Examples
///
/// ```rust
/// use owned_pin::sync::{try_apin_init, RefCounted, RefCount};
/// use pinned_init::pin_data;
///
/// #[pin_data]
/// #[derive(RefCounted)]
/// struct A {
///     x: u32,
///     #[count_on]
///     rc: RefCount,
/// }
///
/// try_apin_init!(let a = A { x: 64, rc: RefCount::new() });
/// assert_eq!(a.unwrap().x, 64);
#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
#[cfg(feature = "pinned-init")]
macro_rules! try_apin_init {
    (let $value:ident $(:$ty:ty)? = $($init:tt)*) => {
        $crate::try_opin_init!(let __opin $(:$ty)? = $($init)*);
        let $value = __opin.map(|p| $crate::Pin {
            pointer: $crate::sync::Arsc {
                pointer: $crate::ManuallyDrop::new(p.pointer)
            }
        });
    };
}

/// Initializes and pins an [`Arsc`] pointer on the current calling stack.
///
/// # Examples
///
/// ```rust
/// use owned_pin::sync::{apin_init, RefCounted, RefCount};
/// use pinned_init::pin_data;
///
/// #[pin_data]
/// #[derive(RefCounted)]
/// struct A {
///     x: u32,
///     #[count_on]
///     rc: RefCount,
/// }
///
/// apin_init!(let a = A { x: 64, rc: RefCount::new() });
/// assert_eq!(a.x, 64);
#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
#[cfg(feature = "pinned-init")]
macro_rules! apin_init {
    (let $value:ident $(:$ty:ty)? = $($init:tt)*) => {
        $crate::opin_init!(let __opin $(:$ty)? = $($init)*);
        let $value = $crate::Pin {
            pointer: $crate::sync::Arsc {
                pointer: $crate::ManuallyDrop::new(__opin.pointer)
            }
        };
    };
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    /// Wraps a smart pointer into an `Arsc<P>`.
    ///
    /// For safe construction methods, see [`new`](Arsc::new),
    /// [`arsc`](ArscExt::arsc) and [`apin`](ArscExt::apin) methods for general
    /// pointers, and [`arsc_on_stack`] and [`apin`] macros for pointers on the
    /// stack.
    ///
    /// # Safety
    ///
    /// `pointer` must owns its pointed data, thus guaranteeing the [`RefCount`]
    /// inside the data is left untouched by other possible `Arsc`s, or is
    /// restored to default by [`try_unwrap`](Arsc::try_unwrap).
    pub unsafe fn new_unchecked(pointer: P) -> Self {
        unsafe { Arsc::from_pointer(pointer) }
    }

    /// Wraps a smart pointer into an `Arsc<P>`.
    ///
    /// This function is safe because `P` owns its data, guaranteeing the
    /// [`RefCount`] inside the data is left untouched by other possible
    /// `Arsc`s, or is restored to default by [`try_unwrap`](Arsc::try_unwrap).
    ///
    /// For direct construction methods from values, see [`arsc`](ArscExt::arsc)
    /// and [`apin`](ArscExt::apin) methods for general pointers, and
    /// [`arsc_on_stack`] and [`apin`] macros for pointers on the stack.
    pub fn new(pointer: P) -> Self
    where
        P: IntoInner,
    {
        // SAFETY: `pointer` owns its data.
        unsafe { Arsc::new_unchecked(pointer) }
    }

    /// Wraps a pinned smart pointer into an `Pin<Arsc<P>>`.
    ///
    /// This function is safe because `P` owns its data, guaranteeing the
    /// [`RefCount`] inside the data is left untouched by other possible
    /// `Arsc`s.
    ///
    /// For direct construction methods from pinned values, see
    /// [`apin`](ArscExt::apin) method and [`apin`] macro.
    pub fn into_pin(pointer: Pin<P>) -> Pin<Self>
    where
        P: IntoInner,
    {
        // SAFETY: The data inside `pointer` is untouched, thus kept pinned.
        unsafe { Pin::new_unchecked(Self::new(Pin::into_inner_unchecked(pointer))) }
    }

    /// Attempts to unwrap the underlying smart pointer.
    ///
    /// Returns the original `Arsc` wrapped in `Err` if the current reference
    /// count is greater than 1.
    ///
    /// The [`RefCount`] residing in the unwrapped smart pointer will be
    /// restored to default, enabling it to be rewrapped in another `Arsc`.
    pub fn try_unwrap_pointer(this: Self) -> Result<P, Self> {
        let ref_count: &RefCount = this.pointer.ref_count();
        if ref_count
            .count
            .compare_exchange(1, 0, Relaxed, Relaxed)
            .is_err()
        {
            return Err(this);
        }

        atomic::fence(Acquire);

        ref_count.count.store(1, Relaxed);
        Ok(unsafe { Arsc::into_pointer(this) })
    }

    /// Attempts to unwrap the underlying data in the smart pointer.
    ///
    /// Returns the original `Arsc` wrapped in `Err` if the current reference
    /// count is greater than 1.
    ///
    /// The [`RefCount`] residing in the unwrapped data will be restored to
    /// default, enabling it to be rewrapped in another `Arsc`.
    pub fn try_unwrap(this: Self) -> Result<P::Target, Self>
    where
        P: IntoInner,
        P::Target: Sized,
    {
        let ref_count: &RefCount = this.pointer.ref_count();
        if ref_count
            .count
            .compare_exchange(1, 0, Relaxed, Relaxed)
            .is_err()
        {
            return Err(this);
        }

        atomic::fence(Acquire);

        ref_count.count.store(1, Relaxed);
        unsafe {
            let pointer = Arsc::into_pointer(this);
            P::try_unwrap(pointer).map_err(|p| Self::from_pointer(p))
        }
    }

    /// Attempts to unwrap the underlying data in the smart pointer.
    ///
    /// Returns `None` if the current reference count is greater than 1.
    ///
    /// The [`RefCount`] residing in the unwrapped data will be restored to
    /// default, enabling it to be rewrapped in another `Arsc`.
    pub fn into_inner(this: Self) -> Option<P::Target>
    where
        P: IntoInner,
        P::Target: Sized,
    {
        Arsc::try_unwrap(this).ok()
    }

    /// Provides a raw pointer to the data.
    ///
    /// The counts are not affected in any way and the `Arsc` is not consumed.
    /// The pointer is valid for as long as there are strong counts in the
    /// `Arsc`.
    pub fn as_ptr(this: &Self) -> *const P::Target {
        &**this.pointer
    }

    /// Returns `true` if the two `Arsc`s point to the same allocation in a vein
    /// similar to [`ptr::eq`]. This function ignores the metadata of  `dyn
    /// Trait` pointers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "alloc")]
    /// # {
    ///
    /// use owned_pin::sync::{Arsc, ArscExt, RefCount, RefCounted};
    ///
    /// #[derive(RefCounted)]
    /// struct A {
    ///     value: &'static str,
    ///     #[count_on]
    ///     rc: RefCount,
    /// }
    ///
    /// let arsc: Arsc<Box<A>> = Box::arsc(A {
    ///     value: "Hello!",
    ///     rc: RefCount::new(),
    /// });
    /// let cloned = arsc.clone();
    ///
    /// assert!(Arsc::ptr_eq(&arsc, &cloned));
    ///
    /// # }
    /// ```
    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        Self::as_ptr(a) == Self::as_ptr(b)
    }
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    /// Coerce the `Arsc<P>` into `Arsc<Q>` if `P` is [`CoerceUnsized<Q>`].
    ///
    /// This is written manually because of the lack of derived implementation
    /// of `CoerceUnsized` in `ManuallyDrop<T>`.
    pub fn coerce_unsized<Q>(this: Self) -> Arsc<Q>
    where
        Q: Deref,
        Q::Target: RefCounted,
        P: CoerceUnsized<Q>,
    {
        unsafe { Arsc::from_pointer(Self::into_pointer(this)) }
    }
}

impl<P> Arsc<P>
where
    P: DerefMut,
    P::Target: RefCounted,
{
    /// Returns a mutable reference into the given `Arsc`, without any check.
    ///
    /// See also [`get_mut`](Arsc::get_mut), which is safe and does appropriate
    /// checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure the exclusiveness of the mutable reference.
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut P::Target {
        &mut this.pointer
    }

    /// Returns a mutable reference into the given `Arsc`, if the pointer
    /// currently holds the unique reference.
    ///
    /// See also [`make_mut`](Arsc::make_mut), which will
    /// [`clone`](Clone::clone) the inner value when there are other `Arc`
    /// pointers.
    pub fn get_mut(this: &mut Self) -> Option<&mut P::Target> {
        let ref_count: &RefCount = this.pointer.ref_count();
        if ref_count
            .count
            .compare_exchange(1, 0, Relaxed, Relaxed)
            .is_err()
        {
            None
        } else {
            atomic::fence(Acquire);

            ref_count.count.store(1, Relaxed);

            // SAFETY: The exclusiveness is checked above.
            Some(unsafe { Self::get_mut_unchecked(this) })
        }
    }
}

impl<P> Arsc<P>
where
    P: DerefMut + From<P::Target> + IntoInner,
    P::Target: RefCounted + Clone,
{
    /// Makes a mutable reference into the given `Arsc`.
    ///
    /// Like `Arc::make_mut`, if there are other `Arsc` pointers to the same
    /// allocation, then `make_mut` will [`clone`](Clone::clone) the inner
    /// value to a new allocation to ensure unique ownership.  This is also
    /// referred to as clone-on-write.
    ///
    /// See also [`get_mut`](Arsc::get_mut), which will fail rather than cloning
    /// the inner value.
    pub fn make_mut(this: &mut Self) -> &mut P::Target {
        let ref_count: &RefCount = this.pointer.ref_count();
        if ref_count
            .count
            .compare_exchange(1, 0, Relaxed, Relaxed)
            .is_err()
        {
            *this = Arsc::from((**this).clone());
        } else {
            atomic::fence(Acquire);

            ref_count.count.store(1, Relaxed);
        }
        unsafe { Arsc::get_mut_unchecked(this) }
    }
}

unsafe impl<P> RawConvertable for Arsc<P>
where
    P: Deref + RawConvertable,
    P::Target: RefCounted,
{
    type Metadata = P::Metadata;

    fn into_raw(this: Self) -> (NonNull<P::Target>, P::Metadata) {
        P::into_raw(unsafe { Self::into_pointer(this) })
    }

    unsafe fn from_raw(pointer: NonNull<P::Target>, metadata: P::Metadata) -> Self {
        // SAFETY: The contract is satisfied by the caller.
        unsafe { Self::from_pointer(P::from_raw(pointer, metadata)) }
    }
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    /// Gets the number of `Arsc` pointers to the same underlying smart pointer.
    ///
    /// # Safety
    ///
    /// This method by itself is safe, but using it correctly requires extra
    /// care. Another thread can change the reference count at any time,
    /// including potentially between calling this method and acting on the
    /// result.
    pub fn count(this: &Self) -> usize {
        this.pointer.ref_count().count.load(Acquire)
    }
}

impl<P> Arsc<P>
where
    P: Deref + RawConvertable,
    P::Target: RefCounted,
{
    /// Increments the reference count on the `Arsc<P>` associated with the
    /// provided pointer by one.
    ///
    /// # Safety
    ///
    /// The pointer must have been obtained through `Arsc::into_raw`, and the
    /// associated `Arsc` instance must be valid (i.e. the reference count must
    /// be at least 1) for the duration of this method, and `pointer` must point
    /// to a block of memory managed by `P`.
    pub unsafe fn incrememt_count(pointer: NonNull<P::Target>, metadata: P::Metadata) {
        let arsc = unsafe { ManuallyDrop::new(Self::from_raw(pointer, metadata)) };
        let _cloned: ManuallyDrop<_> = arsc.clone();
    }

    /// Decrements the reference count on the `Arsc<P>` associated with the
    /// provided pointer by one.
    ///
    /// # Safety
    ///
    /// The pointer must have been obtained through `Arsc::into_raw`, and the
    /// associated `Arsc` instance must be valid (i.e. the reference count must
    /// be at least 1) when invoking this method, and `pointer` must point
    /// to a block of memory managed by `P`. This method can be used to release
    /// the final `Arsc` and backing storage, but **should not** be called
    /// after the final `Arsc` has been released.
    pub unsafe fn decrement_count(pointer: NonNull<P::Target>, metadata: P::Metadata) {
        drop(unsafe { Self::from_raw(pointer, metadata) });
    }
}

impl<P> Deref for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    type Target = P::Target;

    fn deref(&self) -> &Self::Target {
        &self.pointer
    }
}

impl<P> Clone for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    fn clone(&self) -> Self {
        let ref_count: &RefCount = self.pointer.ref_count();
        let count = ref_count.count.fetch_add(1, Relaxed);

        if count >= REF_COUNT_MAX {
            ref_count.count.store(REF_COUNT_SATURATED, Relaxed);
        }

        // SAFETY: The reference count is just incremented, and the newly copied pointer
        // is stored in a new `ManuallyDrop`, thus preventing it from double dropping.
        unsafe {
            let pointer = ptr::read(&*self.pointer);
            Self::from_pointer(pointer)
        }
    }
}

impl<P> Drop for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    fn drop(&mut self) {
        let ref_count: &RefCount = self.pointer.ref_count();

        let count = ref_count.count.fetch_sub(1, Release);

        if count >= REF_COUNT_MAX {
            ref_count.count.store(REF_COUNT_SATURATED, Relaxed);
        } else if count == 1 {
            atomic::fence(Acquire);

            // SAFETY: No more references are available.
            unsafe { ManuallyDrop::drop(&mut self.pointer) };
        }
    }
}

impl<P> PartialEq for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<P> Eq for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + Eq,
{
}

impl<P> PartialOrd for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<P> Ord for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.deref().cmp(other)
    }
}

impl<P> fmt::Display for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<P> fmt::Debug for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<P> fmt::Pointer for Arsc<P>
where
    P: Deref + fmt::Pointer,
    P::Target: RefCounted,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&*self.pointer, f)
    }
}

impl<P> Hash for Arsc<P>
where
    P: Deref,
    P::Target: RefCounted + Hash,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<P> Default for Arsc<P>
where
    P: Deref + Default,
    P::Target: RefCounted,
{
    fn default() -> Self {
        Arsc {
            pointer: ManuallyDrop::new(P::default()),
        }
    }
}

impl<P, T> From<T> for Arsc<P>
where
    P: Deref<Target = T> + From<T> + IntoInner,
    T: RefCounted,
{
    fn from(value: T) -> Self {
        Arsc::new(P::from(value))
    }
}
