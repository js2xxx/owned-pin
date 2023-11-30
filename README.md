Owned Pin

This crate deals with data which is owned by some entity but (maybe) immovable in memory.

See [the documentation](https://docs.rs/owned-pin/) for more information.

# Examples

With `Pin<P>` only, we cannot guarantee the move semantics of the value.

```rust,no_run
use core::pin::{Pin, pin};
use core::marker::PhantomPinned;

fn try_to_take_the_ownership_of<T>(pinned: Pin<&mut T>) {}

let mut value = pin!(PhantomPinned);
// The caller can reborrow the value...
try_to_take_the_ownership_of(value.as_mut());
// ... so the same pinned data can be used twice,
// thus unable to guarantee the move semantics.
try_to_take_the_ownership_of(value.as_mut());
```

But with the [`OPin<T, P>`] wrapper, which both "own" and "pin" the data in the memory, enabling the example above to work as desired:

```rust,compile_fail
use owned_pin::{OPin, opin};
use core::marker::PhantomPinned;

fn take_the_ownership_of<T>(owned_and_pinned: OPin<T>) {}

let value = opin!(PhantomPinned);
// The `as_mut` method of `OPin` actually returns `Pin<&mut T>`...
take_the_ownership_of(value);
// ... so the value itself cannot be used again.
// The line below causes rustc to emit `E0382`.
// take_the_ownership_of(value);
```