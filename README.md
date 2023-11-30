# Owned Pin

[![Cargo](https://img.shields.io/crates/v/owned-pin.svg)](https://crates.io/crates/owned-pin)
[![Documentation](https://docs.rs/owned-pin/badge.svg)](https://docs.rs/owned-pin)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](https://github.com/js2xxx/owned-pin)

This crate deals with data that is owned by some entity but (maybe) immovable in memory. It is inspired by R-value references in C++.

See [the documentation](https://docs.rs/owned-pin/) for more information.

## Examples

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

In practice, this is because there is no such smart pointer that owns data by holding a unique reference to some other location on the stack.

Thus, we introduce the `OnStack<T>` smart pointer and an alias of `OPin<T>` = `Pin<OnStack<T>>`, which both "own" and "pin" the data on the stack, enabling the example above to work as desired:

```rust,compile_fail
use owned_pin::{OPin, opin};
use core::marker::PhantomPinned;

fn take_the_ownership_of<T>(owned_and_pinned: OPin<T>) {}

let value = opin!(PhantomPinned);
// The `as_mut` method of `OPin` actually
// returns a `Pin<&mut T>`...
take_the_ownership_of(value);
// ... so the value itself cannot be used again.
// The line below causes rustc to emit `E0382`.
// take_the_ownership_of(value);
```

With data that implements `Unpin`, we can even move it out from the wrapper safe and sound:

```rust
use owned_pin::{opin, unpin};

// Pins the value onto the stack.
let pinned = opin!(String::from("Hello!"));
// Retrieves back the data because `String` is `Unpin`.
let string: String = unpin(pinned);
```

## License

MIT OR Apache-2.0