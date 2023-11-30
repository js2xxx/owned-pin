use core::{
    any::Any,
    borrow::{Borrow, BorrowMut},
    error::Error,
    fmt,
    future::Future,
    hash::Hasher,
    iter::FusedIterator,
    marker::{PhantomData, Tuple, Unsize},
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::{CoerceUnsized, Coroutine, CoroutineState, Deref, DerefMut, DispatchFromDyn},
    panic::UnwindSafe,
    pin::Pin,
    ptr,
    task::{Context, Poll},
};

use crate::IntoInner;

/// A pointer type that uniquely owns its data on the stack. but via the
/// implementation of a mutable reference to its `ManuallyDrop` wrapped form.
///
/// This object behaves just like `Box<T>`, aside from the fact that its pointed
/// value is stored somewhere else on the stack, while the storage place itself
/// is directly unreachable.
///
/// See [the module level documentation](crate) for more information.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct OnStack<'a, T: ?Sized> {
    #[doc(hidden)]
    pub inner: &'a mut ManuallyDrop<T>,
    #[doc(hidden)]
    pub marker: PhantomData<T>,
}

impl<'a, T: ?Sized + fmt::Debug> fmt::Debug for OnStack<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OnStack")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<'a, T: ?Sized> fmt::Pointer for OnStack<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&((&**self) as *const T), f)
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for OnStack<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.inner).fmt(f)
    }
}

impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<OnStack<'a, U>> for OnStack<'a, T> {}

impl<'a, T: ?Sized, U: ?Sized> DispatchFromDyn<OnStack<'a, U>> for OnStack<'a, T> where T: Unsize<U> {}

impl<'a, T: ?Sized + UnwindSafe> UnwindSafe for OnStack<'a, T> {}

impl<'a, T: ?Sized> Unpin for OnStack<'a, T> {}

impl<'a, T: ?Sized> OnStack<'a, T> {
    /// Constructs an owned reference to somewhere on the stack.
    ///
    /// For safe construction methods, see [`on_stack`](crate::on_stack).
    ///
    /// # Safety
    ///
    /// `inner` must own its referent, a.k.a. not being (in)directly reborrowed
    /// from other references, and must not be used anymore anywhere else.
    pub unsafe fn new_unchecked(inner: &'a mut ManuallyDrop<T>) -> Self {
        OnStack {
            inner,
            marker: PhantomData,
        }
    }

    /// Consumes the `OnStack` pointer, returning a wrapped raw pointer, which
    /// will be properly aligned and non-null.
    ///
    /// This function behaves just like `Box::into_raw`, aside from the fact
    /// that the pointer's lifetime is discarded as well.
    pub fn into_raw(pointer: Self) -> *mut T {
        OnStack::leak(pointer)
    }

    /// Constructs an `OnStack` pointer from a raw pointer.
    ///
    /// # Safety
    ///
    /// Beside the basic requirement stated in
    /// [`new_unchecked`](OnStack::new_unchecked), the caller must also ensure
    /// the satisfaction of creating a unique & valid reference from this
    /// pointer.
    pub unsafe fn from_raw(pointer: *mut T) -> Self {
        // SAFETY: The contract is satisfied above.
        unsafe { OnStack::new_unchecked(&mut *(pointer as *mut ManuallyDrop<T>)) }
    }

    /// Converts a `OnStack<T>` into a `Pin<OnStack<T>>`. If `T` does not
    /// implement Unpin, then `*pointer` will be pinned in memory and unable
    /// to be moved.
    ///
    /// See [`opin`](crate::opin) for methods that directly pin values.
    pub fn into_pin(pointer: Self) -> Pin<OnStack<'a, T>> {
        // It's not possible to move or replace the insides of a `Pin<OnStack<T>>`
        // when `T: !Unpin`, so it's safe to pin it directly without any additional
        // requirements.
        unsafe { Pin::new_unchecked(pointer) }
    }

    /// Consumes and leaks the `OnStack` pointer, returning a mutable reference,
    /// `&'a mut T`.
    ///
    /// Unlike `Box::leak`, this function cannot chose its own lifetime,
    /// because the pointer itself is constrained by a certain lifetime.
    ///
    /// Like `Box::leak`, the destructor of the value will not be run.
    pub fn leak(pointer: Self) -> &'a mut T {
        unsafe {
            let ret = ptr::read(&pointer.inner);
            mem::forget(pointer);
            ret
        }
    }
}

impl<'a, T> OnStack<'a, MaybeUninit<T>> {
    /// Converts to an initialized `OnStack` pointer.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`], it is up to the caller to
    /// guarantee that the value really is in an initialized state. Calling
    /// this when the content is not yet fully initialized causes immediate
    /// undefined behavior.
    pub unsafe fn assume_init(self) -> OnStack<'a, T> {
        // SAFETY: `&mut MaybeUninit<T>` shares the same memory layout as `&mut T`.
        unsafe { mem::transmute(self) }
    }

    /// Writes the value and converts to an initialized `OnStack` pointer.
    pub fn write(mut pointer: Self, value: T) -> OnStack<'a, T> {
        (*pointer).write(value);
        // SAFETY: We just wrote a valid value onto the storage place.
        unsafe { pointer.assume_init() }
    }
}

impl<'a> OnStack<'a, dyn Any> {
    /// Attempts to downcast the `OnStack` pointer to a concrete type.
    pub fn downcast<T: Any>(self) -> Result<OnStack<'a, T>, Self> {
        if self.is::<T>() {
            Ok(unsafe { self.downcast_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Downcasts the `OnStack` pointer to a concrete type.
    ///
    /// # Safety
    ///
    /// The contained value must be of type `T`. Calling this method
    /// with the incorrect type is *undefined behavior*.
    pub unsafe fn downcast_unchecked<T: Any>(self) -> OnStack<'a, T> {
        debug_assert!(self.is::<T>());
        // SAFETY: `self` is `T`.
        unsafe {
            let raw = Self::into_raw(self);
            OnStack::from_raw(raw.cast::<T>())
        }
    }
}

impl<'a, T: ?Sized> Deref for OnStack<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

impl<'a, T: ?Sized> DerefMut for OnStack<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'a, T: ?Sized> AsRef<T> for OnStack<'a, T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized> AsMut<T> for OnStack<'a, T> {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<'a, T: ?Sized> Borrow<T> for OnStack<'a, T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized> BorrowMut<T> for OnStack<'a, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<'a, T> IntoInner for OnStack<'a, T> {
    type Target = T;

    fn into_inner(self) -> T {
        // SAFETY: We own this place of memory according to the contract in
        // `new_unchecked` function.
        unsafe {
            let value = ManuallyDrop::take(&mut *self.inner);
            // Prevent the drop function to be called.
            mem::forget(self);
            value
        }
    }
}

impl<'a, T: ?Sized> Drop for OnStack<'a, T> {
    fn drop(&mut self) {
        // SAFETY: We own this place of memory according to the contract in
        // `new_unchecked` function.
        unsafe { ManuallyDrop::drop(self.inner) }
    }
}

impl<'a, T: ?Sized + Future + Unpin> Future for OnStack<'a, T> {
    type Output = T::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        Pin::new(&mut **self.inner).poll(cx)
    }
}

impl<'a, A, T: ?Sized + Coroutine<A> + Unpin> Coroutine<A> for OnStack<'a, T> {
    type Yield = T::Yield;
    type Return = T::Return;

    fn resume(mut self: Pin<&mut Self>, arg: A) -> CoroutineState<Self::Yield, Self::Return> {
        Pin::new(&mut **self.inner).resume(arg)
    }
}

impl<'a, T: ?Sized + Iterator> Iterator for OnStack<'a, T> {
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, T: ?Sized + DoubleEndedIterator> DoubleEndedIterator for OnStack<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, T: ?Sized + FusedIterator> FusedIterator for OnStack<'a, T> {}

impl<'a, T: ?Sized + ExactSizeIterator> ExactSizeIterator for OnStack<'a, T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, T: ?Sized + Error> Error for OnStack<'a, T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.inner.source()
    }

    fn provide<'b>(&'b self, request: &mut core::error::Request<'b>) {
        self.inner.provide(request);
    }
}

impl<'a, A: Tuple, T: FnOnce<A>> FnOnce<A> for OnStack<'a, T> {
    type Output = T::Output;

    extern "rust-call" fn call_once(self, args: A) -> Self::Output {
        self.into_inner().call_once(args)
    }
}

impl<'a, A: Tuple, T: FnMut<A>> FnMut<A> for OnStack<'a, T> {
    extern "rust-call" fn call_mut(&mut self, args: A) -> Self::Output {
        (self.inner).call_mut(args)
    }
}

impl<'a, A: Tuple, T: Fn<A>> Fn<A> for OnStack<'a, T> {
    extern "rust-call" fn call(&self, args: A) -> Self::Output {
        (self.inner).call(args)
    }
}

impl<T: ?Sized + Hasher> Hasher for OnStack<'_, T> {
    fn finish(&self) -> u64 {
        self.inner.finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        self.inner.write(bytes)
    }

    fn write_u8(&mut self, i: u8) {
        self.inner.write_u8(i)
    }

    fn write_u16(&mut self, i: u16) {
        self.inner.write_u16(i)
    }

    fn write_u32(&mut self, i: u32) {
        self.inner.write_u32(i)
    }

    fn write_u64(&mut self, i: u64) {
        self.inner.write_u64(i)
    }

    fn write_u128(&mut self, i: u128) {
        self.inner.write_u128(i)
    }

    fn write_usize(&mut self, i: usize) {
        self.inner.write_usize(i)
    }

    fn write_i8(&mut self, i: i8) {
        self.inner.write_i8(i)
    }

    fn write_i16(&mut self, i: i16) {
        self.inner.write_i16(i)
    }

    fn write_i32(&mut self, i: i32) {
        self.inner.write_i32(i)
    }

    fn write_i64(&mut self, i: i64) {
        self.inner.write_i64(i)
    }

    fn write_i128(&mut self, i: i128) {
        self.inner.write_i128(i)
    }

    fn write_isize(&mut self, i: isize) {
        self.inner.write_isize(i)
    }
}

impl<'a, T: ?Sized> From<OnStack<'a, T>> for Pin<OnStack<'a, T>> {
    fn from(value: OnStack<'a, T>) -> Self {
        OnStack::into_pin(value)
    }
}
