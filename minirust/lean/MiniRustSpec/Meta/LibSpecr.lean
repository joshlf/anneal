/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# `libspecr` data types used by MiniRust data definitions

MiniRust's specification is written against the `libspecr` support crate
(version pinned in `minirust/minirust.lock.toml` as `upstream_libspecr`,
`0.1.41`; documentation at <https://docs.rs/libspecr/0.1.41>). The vendored
prelude says:

> "/// Documentation for libspecr can be found here: https://docs.rs/libspecr
> pub use libspecr::prelude::*;" (`spec/prelude/main.md`)

`libspecr` is not part of the MiniRust repository, so the translator cannot
consume it mechanically. This module hand-writes the *data representation* of
the `libspecr` types that MiniRust's `struct`/`enum` definitions mention, and
nothing else: no operations on these types live here (operations needed by the
interpretation live in `MiniRustSpec.Interp`, next to the semantics that use
them). The mapping from `libspecr` names to these definitions is the table
`builtin` in `crates/anneal-minirust-gen/src/shallow.rs`.

Representation choices (each is a modeling decision, stated so that it can be
audited):

* `Map` and `Set` are association lists. `libspecr` implements them as
  persistent hash maps/sets with unspecified iteration order; MiniRust code only
  relies on lookup, insertion, and removal, plus iteration in places where the
  order is irrelevant to the outcome.
* `Size` and `Align` store a `Nat` number of bytes, so non-negativity holds by
  construction. `libspecr` additionally guarantees that an `Align` is a power of
  two; that invariant is *not* enforced by the type here and must be stated
  where it matters.
* `Name` is an opaque identifier; `libspecr` builds names from `u32` indices
  (`Name::from_internal`), which we represent as a `Nat`.
* `DynWrite` is the output sink of `PrintStdout`/`PrintStderr`; we record the
  sequence of written strings.
-/

namespace MiniRustSpec.LibSpecr

/-- `libspecr::Name`: an opaque identifier (built from a `u32` index). -/
structure Name : Type where
  idx : Nat
  deriving DecidableEq

/-- `libspecr::Size`: a non-negative number of bytes. -/
structure Size : Type where
  bytes : Nat
  deriving DecidableEq

/-- `libspecr::Align`: an alignment in bytes (a power of two in `libspecr`; see
the module docs for why that invariant is not part of this type). -/
structure Align : Type where
  bytes : Nat
  deriving DecidableEq

/-- `libspecr::Signedness`. -/
inductive Signedness : Type where
  | Unsigned
  | Signed
  deriving DecidableEq

/-- `libspecr::Endianness`. -/
inductive Endianness : Type where
  | LittleEndian
  | BigEndian
  deriving DecidableEq

/-- `libspecr::Mutability`. -/
inductive Mutability : Type where
  | Mutable
  | Immutable
  deriving DecidableEq

/-- `libspecr::Map<K, V>` as an association list (first binding wins). -/
structure Map (K V : Type) : Type where
  entries : List (K × V)
  deriving DecidableEq

/-- `libspecr::Set<T>` as a list of elements. -/
structure Set (T : Type) : Type where
  elems : List T
  deriving DecidableEq

/-- `std::marker::PhantomData<T>`: a zero-sized marker. -/
structure PhantomData (T : Type) : Type where
  deriving DecidableEq

/-- `libspecr::DynWrite`: the sequence of strings written to the sink. -/
structure DynWrite : Type where
  written : List String

end MiniRustSpec.LibSpecr
