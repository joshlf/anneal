-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mvp
prelude
import Init.Data.List.Basic
-- Function identities need the foundation's string construction and equality.
-- Bootstrap already belongs to the authenticated foundation; this field needs
-- no additional checked-library admission.
import Init.Data.String.Bootstrap

/-!
This syntax owns the admitted, pointer-free scalar fragment of typed
`Runtime(PostCleanup)` MIR. It preserves blocks and statement order. Capture
must reject every compiler construct without a constructor here.

The pinned compiler describes the runtime dialect as "used for CTFE,
optimizations, and codegen" in `MirPhase`. The constructors below correspond
to its `Operand`, `Rvalue`, `StatementKind`, `TerminatorKind`, and `BinOp`:
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs

Enum values use logical variant indices, with an explicit table of compiler
discriminants. The compiler warns that "the value of the discriminant is not
the same thing as the variant index" at `Rvalue::Discriminant` in that source.
Only fieldless enums with an isize discriminant type are admitted.
-/

namespace Trusted.Mvp

/--
These constructors record the admitted cases of the pinned compiler's `TyKind`:

- `never` corresponds to `Never`, documented as "The never type `!`."
- `bool` corresponds to `Bool`, "The primitive boolean type."
- `int bits true` and `int bits false` correspond to `Int` and `Uint`, described
  as "A primitive signed integer type." and "A primitive unsigned integer type."
- `unit` corresponds only to an empty `Tuple`, described as "A tuple type."

https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L102-L126
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs#L247-L251

The empty-tuple correspondence follows `Ty::is_unit`:
"Tuple(tys) => tys.is_empty()".
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/sty.rs#L1131-L1136

Integer widths come from `IntTy::bit_width` and `UintTy::bit_width`. Their
pointer-sized cases return "IntTy::Isize => return None" and
"UintTy::Usize => return None". Capture uses the checked 64-bit target width
for those cases and admits fixed widths 8, 16, 32, and 64; wider types fail.
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ast_ir/src/lib.rs#L58-L68
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ast_ir/src/lib.rs#L134-L144

`enum id discriminants` corresponds to `TyKind::Adt`, documented as "Algebraic
data types (ADT)." Anneal admits only local, non-generic enums with no variant
fields and an isize discriminant type. The `id` records the crate-local
definition index; `discriminants` records compiler discriminant values in
variant-index order. The compiler's `discriminants` iterator uses
"self.variants().iter_enumerated()" and returns "(i, discr)".
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/adt.rs#L660-L679

The representation query defaults to
"self.int.unwrap_or(IntegerType::Pointer(true))", and the compiler documents
that "`Pointer(true)` means `isize`." Capture checks that representation and
each recorded discriminant's type before admitting the enum.
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L116-L119
https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L195-L204
-/
inductive Ty where
  | never
  | unit
  | bool
  | int (bits : Nat) (signed : Bool)
  | enum (id : Nat) (discriminants : List Nat)

/--
Slot assignments preserve integer signedness and nominal enum identity. Equal
payload bits or equal discriminant tables alone do not establish a type match.
-/
def Ty.beq : Ty → Ty → Bool
  | .never, .never | .unit, .unit | .bool, .bool => true
  | .int bits signed, .int bits' signed' =>
      (bits == bits') && (signed == signed')
  | .enum id discriminants, .enum id' discriminants' =>
      (id == id') && (discriminants == discriminants')
  | _, _ => false

instance : BEq Ty := ⟨Ty.beq⟩

/--
Raw constants retain their full natural-number encoding. A semantics consuming
this syntax must establish that fixed-width conversion preserves the encoding
and must enforce type-specific validity. Truncating first could silently discard
high bits and turn an invalid captured constant into an admitted one.
-/
inductive Operand where
  | copy (index : Nat)
  | move (index : Nat)
  | constant (ty : Ty) (bits : Nat)

inductive BinOp where
  | bitAnd | bitOr | bitXor | shl | shr
  | add | sub | mul | eq | ne | lt | le | gt | ge

inductive Rvalue where
  | unit
  | use (operand : Operand) (withRetag : Bool)
  | binary (op : BinOp) (left right : Operand)
  | discriminant (index : Nat)

inductive Statement where
  | assign (index : Nat) (value : Rvalue)
  | storageLive (index : Nat)
  | storageDead (index : Nat)
  | nop

inductive Terminator where
  | goto (block : Nat)
  | switchInt (operand : Operand) (targets : List (Nat × Nat)) (otherwise : Nat)
  | ret
  | unreachable

structure Block where
  statements : List Statement
  terminator : Terminator

structure Body where
  argCount : Nat
  isUnsafe : Bool
  localTys : List Ty
  blocks : List Block
  /--
  Captured function identity, used to bind reviewed caller requirements to this
  body. A compiler inventory position can change when unrelated items are added
  or reordered; attaching this key to the body keeps its contract association.

  The capture adapter owns the versioned `rust-path-v1::` semantic-path format
  for the pinned compiler and configured crate. It checks key uniqueness before
  publishing the authenticated captured subject. Renaming an item, changing its
  semantic owner, or changing the scheme requires reviewing specification keys;
  the format makes no stability promise across compiler pins.

  Selected functions beneath anonymous owners can retain order-derived path
  components, such as `closure#0`, already explicit in selected-scope roots.
  Their keys expose that selector; they do not promise persistent identity when
  those owners are reordered. A stronger guarantee needs reviewed stable anchors
  or an explicit binding protocol.
  -/
  identity : String

inductive VerificationScope where
  | unit
  | crate

structure Program where
  scope : VerificationScope
  bodies : List Body

end Trusted.Mvp
