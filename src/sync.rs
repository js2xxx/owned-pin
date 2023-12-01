use core::{
    alloc::AllocError,
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

use pinned_init::InPlaceInit;

use crate::{IntoInner, RawConvertable};

const REF_COUNT_MAX: usize = (isize::MAX) as usize;
#[cfg(target_pointer_width = "64")]
const REF_COUNT_SATURATED: usize = 0xC000_0000_0000_0000;
#[cfg(target_pointer_width = "32")]
const REF_COUNT_SATURATED: usize = 0xC000_0000;

/// An intrusive reference counter.
///
/// Users should place this structure into their own type, and implement
/// [`RefCounted`] to enable the support for intrusive ref-counting.
#[derive(Debug, Default)]
pub struct RefCount {
    count: AtomicUsize,
}

/// Types that is intrusively ref-countable.
///
/// # Safety
///
/// `ref_count` must return a static offset in the memory layout of the
/// implementor type.
pub unsafe trait RefCounted {
    fn ref_count(&self) -> &RefCount;
}

unsafe impl RefCounted for RefCount {
    fn ref_count(&self) -> &RefCount {
        self
    }
}

/// A wrapper that enables reference counting on arbitrary smart pointers.
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
    P: Deref,
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
    unsafe fn from_inner(inner: P) -> Arsc<P> {
        Arsc {
            pointer: ManuallyDrop::new(inner),
        }
    }

    unsafe fn into_inner(mut this: Arsc<P>) -> P {
        unsafe {
            let inner = ManuallyDrop::take(&mut this.pointer);
            mem::forget(this);
            inner
        }
    }
}

#[macro_export]
macro_rules! arsc_on_stack {
    (let $value:ident = $init:expr) => {
        let __on_stack = $crate::on_stack!($init);
        let $value = $crate::sync::Arsc {
            pointer: $crate::ManuallyDrop::new(__on_stack),
        };
    };
}

#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
macro_rules! apin {
    (let $value:ident = $init:expr) => {
        $crate::arsc_on_stack!(let __of_arsc = $init);
        let $value = $crate::Pin { pointer: __of_arsc };
    };
}

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

#[macro_export]
macro_rules! arsc_try_init_on_stack {
    (let $value:ident $(:$ty:ty)? = $init:expr) => {
        $crate::try_init_on_stack!(let __init $(:$ty)? = $init);
        let $value = __init.map(|__p| $crate::sync::Arsc {
            pointer: ManuallyDrop::new(__p)
        });
    };
}

#[macro_export]
macro_rules! arsc_init_on_stack {
    (let $value:ident $(:$ty:ty)? = $init:expr) => {
        $crate::init_on_stack!(let __init $(:$ty)? = $init);
        let $value = $crate::sync::Arsc {
            pointer: ManuallyDrop::new(__init)
        };
    };
}

#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
macro_rules! try_apin_init {
    (let $value:ident $(:$ty:ty)? = $init:expr) => {
        $crate::try_opin_init!(let __opin $(:$ty)? = $init);
        let $value = __opin.map(|p| $crate::Pin {
            pointer: $crate::sync::Arsc {
                pointer: ManuallyDrop::new(p.pointer)
            }
        });
    };
}

#[macro_export]
#[allow_internal_unstable(unsafe_pin_internals)]
macro_rules! apin_init {
    (let $value:ident $(:$ty:ty)? = $init:expr) => {
        $crate::opin_init!(let __opin $(:$ty)? = $init);
        let $value = $crate::Pin {
            pointer: $crate::sync::Arsc {
                pointer: ManuallyDrop::new(__opin.pointer)
            }
        };
    };
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    /// # Safety
    ///
    /// `pointer` must owns its pointee.
    pub unsafe fn new_unchecked(pointer: P) -> Self {
        unsafe { Arsc::from_inner(pointer) }
    }

    pub fn new(pointer: P) -> Self
    where
        P: IntoInner,
    {
        // SAFETY: `pointer` owns its data.
        unsafe { Arsc::new_unchecked(pointer) }
    }

    pub fn into_pin(pointer: Pin<P>) -> Pin<Self>
    where
        P: IntoInner,
    {
        unsafe { Pin::new_unchecked(Self::new(Pin::into_inner_unchecked(pointer))) }
    }

    pub fn try_unwrap(this: Self) -> Result<<P as IntoInner>::Target, Self>
    where
        P: IntoInner,
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
            let pointer = Self::into_inner(this);
            Ok(pointer.into_inner())
        }
    }

    pub fn as_ptr(this: &Self) -> *const P::Target {
        &**this.pointer
    }

    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        Self::as_ptr(a) == Self::as_ptr(b)
    }
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    /// This is written manually because of the lack of `CoerceUnsized`
    /// implementation derivation in `ManuallyDrop<T>`.
    pub fn coerce_unsized<Q>(this: Self) -> Arsc<Q>
    where
        Q: Deref,
        Q::Target: RefCounted,
        P: CoerceUnsized<Q>,
    {
        unsafe { Arsc::from_inner(Self::into_inner(this)) }
    }
}

impl<P> Arsc<P>
where
    P: DerefMut,
    P::Target: RefCounted,
{
    /// # Safety
    ///
    /// The caller must ensure the exclusiveness of the mutable reference.
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut P::Target {
        &mut this.pointer
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut P::Target> {
        let ref_count: &RefCount = this.pointer.ref_count();
        if ref_count
            .count
            .compare_exchange(1, 0, Relaxed, Relaxed)
            .is_err()
        {
            None
        } else {
            ref_count.count.store(1, Relaxed);

            // SAFETY: The exclusiveness is checked above.
            Some(unsafe { Self::get_mut_unchecked(this) })
        }
    }
}

unsafe impl<P> RawConvertable for Arsc<P>
where
    P: Deref + RawConvertable,
    P::Target: RefCounted,
{
    type Metadata = P::Metadata;

    fn into_raw(this: Self) -> (NonNull<P::Target>, P::Metadata) {
        P::into_raw(unsafe { Self::into_inner(this) })
    }

    unsafe fn from_raw(pointer: NonNull<P::Target>, metadata: P::Metadata) -> Self {
        // SAFETY: The contract is satisfied by the caller.
        unsafe { Self::from_inner(P::from_raw(pointer, metadata)) }
    }
}

impl<P> Arsc<P>
where
    P: Deref,
    P::Target: RefCounted,
{
    pub fn count(this: &Self) -> usize {
        this.pointer.ref_count().count.load(Acquire)
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
            Self::from_inner(pointer)
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
