# Zot
Provides `Option`-like enums for working with ordered collections of zero, one, or two items (`Zot`), or ordered collections of one or two items (`Ot`).
```
let zot = Zot::Two("one", "two");
assert_eq!(zot.last(), Some("two"));
let ot = Ot::One("just one");
assert!(ot.is_one());
```
Most functionality mimics `Option` with a few exceptions:
- Some new functions relating to the relative positions have been added:
    - `first` gets the singular element from `*::One` or the first element from `*::Two`. `Zot<T>` returns an `Option<T>`, with `Zot::Zero` returning `None`.
    - `second` gets the second element from `*::Two`. Both `Ot<T>` and `Zot<T>` return an `Option<T>`.
    - `last` gets the second element from `*::Two` or the singular element from `*::One`. `Zot<T>` returns an `Option<T>`, `Ot<T>` returns a `T`.
    - `*_mut`, `replace_*`, and `take_*` (`Zot` only) variations are also included.
- Some functions which don't have a clear analogue when working with 2 values are not included (e.g. `zip`).
- `map` requires a `FnMut` parameter instead of `FnOnce` as the function may need to be called twice.