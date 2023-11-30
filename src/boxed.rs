use alloc::boxed::Box;
use core::{
    alloc::{AllocError, Allocator},
    mem::{self, ManuallyDrop},
    ops::DerefMut,
};

use crate::OPin;

/// The safe extension trait for integrating `OPin`s with [`Box`]s.
pub trait BoxOPin: DerefMut<Target = ManuallyDrop<Self::Boxed>> + Sized {
    type Boxed;
    type Unpinned: DerefMut<Target = Self::Boxed> + Sized;

    /// Pin an owned value onto the heap.
    fn opin(value: Self::Boxed) -> OPin<'static, Self::Boxed, Self>;

    /// Try to pin an owned value onto the heap.
    fn try_opin(value: Self::Boxed) -> Result<OPin<'static, Self::Boxed, Self>, AllocError>;

    /// Converts a `Box<T>` into a `OPin<'static, T, Box<ManuallyDrop<T>>`. If
    /// `T` does not implement [`Unpin`], then the value will be pinned in
    /// memory and unable to be moved.
    ///
    /// This method doesn't exist when using a customed allocator, because the
    /// memory layout of `Box<T, A>` may not be the same as
    /// `Box<ManuallyDrop<T>, A>`, this preventing the transmutation.
    fn into_opin(pointer: Self::Unpinned) -> OPin<'static, Self::Boxed, Self>;

    /// Converts a `OPin<'static, T, Box<ManuallyDrop<T>>` into a `Box<T>` if
    /// `T` is [`Unpin`].
    ///
    /// This method doesn't exist when using a customed allocator, because the
    /// memory layout of `Box<T, A>` may not be the same as
    /// `Box<ManuallyDrop<T>, A>`, this preventing the transmutation.
    fn unpin(pinned: OPin<'static, Self::Boxed, Self>) -> Self::Unpinned
    where
        Self::Boxed: Unpin;
}

impl<T> BoxOPin for Box<ManuallyDrop<T>> {
    type Boxed = T;
    type Unpinned = Box<T>;

    fn opin(value: T) -> OPin<'static, T, Self> {
        // SAFETY: The value is pinned on the heap, which is inaccessible from other
        // places.
        unsafe { OPin::new_unchecked(Box::new(ManuallyDrop::new(value))) }
    }

    fn try_opin(value: T) -> Result<OPin<'static, T, Self>, AllocError> {
        // SAFETY: The value is pinned on the heap, which is inaccessible from other
        // places.
        Ok(unsafe { OPin::new_unchecked(Box::try_new(ManuallyDrop::new(value))?) })
    }

    fn into_opin(pointer: Box<T>) -> OPin<'static, Self::Boxed, Self> {
        // SAFETY: The layout of `Box<ManuallyDrop<T>>` is the same as `Box<T>`; the
        // value is pinned on the heap, which is inaccessible from other places.
        unsafe { OPin::new_unchecked(mem::transmute(pointer)) }
    }

    fn unpin(pinned: OPin<'static, Self::Boxed, Self>) -> Self::Unpinned
    where
        Self::Boxed: Unpin,
    {
        // SAFETY: The layout of `Box<ManuallyDrop<T>>` is the same as `Box<T>`.
        unsafe { mem::transmute(OPin::into_inner(pinned)) }
    }
}

/// The safe extension trait for integrating `OPin`s with [`Box`]s with a custom
/// allocator.
pub trait BoxOPinIn: DerefMut<Target = ManuallyDrop<Self::Boxed>> + Sized {
    type Boxed;
    type Unpinned: DerefMut<Target = Self::Boxed> + Sized;
    type Alloc: Allocator;

    /// Pin an owned value onto the heap.
    fn opin_in(value: Self::Boxed, alloc: Self::Alloc) -> OPin<'static, Self::Boxed, Self>;

    /// Try to pin an owned value onto the heap.
    fn try_opin_in(
        value: Self::Boxed,
        alloc: Self::Alloc,
    ) -> Result<OPin<'static, Self::Boxed, Self>, AllocError>;
}

impl<T, A: Allocator> BoxOPinIn for Box<ManuallyDrop<T>, A> {
    type Boxed = T;
    type Unpinned = Box<T, A>;
    type Alloc = A;

    fn opin_in(value: T, alloc: A) -> OPin<'static, T, Self> {
        // SAFETY: The value is pinned on the heap, which is inaccessible from other
        // places.
        unsafe { OPin::new_unchecked(Box::new_in(ManuallyDrop::new(value), alloc)) }
    }

    fn try_opin_in(value: T, alloc: A) -> Result<OPin<'static, T, Self>, AllocError> {
        // SAFETY: The value is pinned on the heap, which is inaccessible from other
        // places.
        Ok(unsafe { OPin::new_unchecked(Box::try_new_in(ManuallyDrop::new(value), alloc)?) })
    }
}
