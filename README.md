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

## Motivation: To Use R-value References of C++ in Rust

[中文版 (Chinese version)](https://zhuanlan.zhihu.com/p/670313432)

This crate is inspired by R-value references in C++, and `OPin<T>` behaves more similarly to R-value references than the original move semantics in Rust and the `Pin<&mut T>` wrapper.

## Rust (original) v.s. C++

In the original move semantics of Rust, when a variable is moved to another scope, its storage place on the stack becomes immediately invalid.

```rust,ignore
fn take_the_ownership_of(s: String) {
    let _ = s;
}

let a = String::from("Hello!");
take_the_ownership_of(a);
```

In the example above, when `a` is moved into the function, the original storage place of `a` on the original call stack, a.k.a. the storage place of pointer to the heap, length and capacity in the inner representation of `String`, becomes invalid and inaccessible immediately.

However, the move semantics in C++, delay this invalidation until the moved reference (R-value reference) of the original value is assigned to a new variable:

```cpp,ignore
void take_the_ownership_of(std::string&&);

std::string a("Hello!");
// The original storage place of `a` keeps
// containing the valid value...
take_the_ownership_of(std::move(a));

void take_the_ownership_of(std::string&& s) {
    // ... until this actual assignment.
    std::string moved(std::forward<std::string>(s));
    // The usage of `s` before the assignment
    // doesn't invalidate the original storage
    // place.
}
```

In a conclusive comparison, the original move semantics of Rust copy the value on the stack eagerly on each move operation if not optimized, while the C++ version splits the operation of "Moving the ownership semantically" and "Copying data on the stack", which theoretically reduces the frequency of the latter operation.

## `owned-pin` v.s. C++

This crate's implementation aims to imitate the move semantics of C++:

```rust
use owned_pin::{OPin, opin, unpin};

let a = String::from("Hello!");
// The original storage place of `a` keeps
// containing the valid value...
take_the_ownership_of(opin!(a));

fn take_the_ownership_of(s: OPin<String>) {
    // ... until this actual `unpin`ning.
    let moved = unpin(s);
    // The usage of `s` before the unpinning
    // doesn't invalidate the original storage
    // place.
}
```

This is achieved by the [`OnStack<T>`] smart pointer, which is a wrapper around `&mut ManuallyDrop<T>`. When an `OnStack<T>` goes out of scope silently, it calls the unsafe `ManuallyDrop::drop` function to release the referenced `T`, while `ManuallyDrop::take` is called when the inner value is intended to be moved out from the reference.

A short comparison between `OPin<T>` and C++'s R-value reference:

| `OPin<T>` in Rust                       | `T&&` in C++                                    |
| --------------------------------------- | ----------------------------------------------- |
| `let pinned = opin!(value);`            | `T&& rvalue = std::move(value);`                |
| `let another_pinned = pinned;`          | `T&& another_rvalue = std::forward<T>(rvalue);` |
| `let unpinned = unpin(another_pinned);` | `T assigned(std::forward<T>(another_rvalue));`  |

The last row assumes `T` is `Unpin` in Rust, and the move constructor of `T` is not deleted in C++.

In conclusion, this crate enables users to adopt the move semantics of C++ in Rust, which reduces the frequency of stack copying, while preserving the the full use of the compile-time borrow checker and drop checker of Rust.

## License

MIT OR Apache-2.0