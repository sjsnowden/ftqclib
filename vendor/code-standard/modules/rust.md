# Module — Rust

What the standard's requirements mean in Rust. Each item names the requirement it serves.

- 5.2: names as `OsString` or `&[u8]` (`std::os::unix::ffi::OsStrExt`), never `String`, for identity.
- 6.4: a failure to persist stops the process, not the thread: a panic in a thread that holds a lock poisons it, every
  later attempt to write panics, and the work being recorded carries on.
- 8.4: `std::thread::scope` where threads must end before the caller; no `process::exit` while threads can still write;
  bound the wait by a count of live tasks.
- 8.7: `Zeroizing` for every buffer that holds a secret, from the read of the file to the last write; `zeroize` or a
  volatile write where a scrub must happen.
- 9.1: `assert!` with a message for anything whose violation must not continue in release; `Result` and `?` at every
  boundary; `.unwrap()` only where the invariant is asserted immediately above, or in tests.
- 9.4: the simplest return type: `()` over `bool` over a value over `Option` over `Result`.
- Take `&T` for anything that is neither `Copy` nor consumed. `checked_*` or `saturating_*` on anything derived from
  input; `div_euclid`, `checked_div`, `div_ceil` where rounding matters.
- `#![forbid(unsafe_code)]` in every crate that can carry it; any `unsafe` carries the invariant that makes it sound.
- `rustfmt` defaults at 100 columns; `cargo clippy` clean, warnings included; `#[test]` beside the code, integration tests
  in `tests/`, a `cargo-fuzz` target for every parser. Compile-time assertions with `const` blocks.
- 10.9: a crate that holds a credential records the reason for each dependency in its `Cargo.toml`.

<!-- brief: Rust -->
Names as `OsStr` bytes; a failure to persist stops the process; `std::thread::scope`; `Zeroizing` for secrets; `Result`
and `?` at boundaries; `#![forbid(unsafe_code)]`; `cargo clippy` clean.
<!-- /brief -->
