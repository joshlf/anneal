import Trusted.Sequence
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Places
import Trusted.Rustc.V2026_08_01.MirAst.Rvalues
import Trusted.Rustc.V2026_08_01.MirAst.Body
import Trusted.Rustc.V2026_08_01.MirSemantics.State

namespace Trusted.Rustc.V2026_08_01.MirSemantics

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst

/-!
Scalar arithmetic, bitwise logic, logical and arithmetic bit shifts, signed and
unsigned overflow detection, two's-complement division and remainder, signed
comparisons, and integer cast helpers for `Runtime(PostCleanup)` MIR at
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#88`, `#100`, `#102`).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The unsigned integer types consist of:
>
> Type   Minimum   Maximum
> u8     0         2^8-1
> u16    0         2^16-1
> u32    0         2^32-1
> u64    0         2^64-1
> u128   0         2^128-1
> usize  0         2^32-1 or 2^64-1
>
> The signed two's complement integer types consist of:
>
> Type   Minimum            Maximum
> i8     -(2^7)             2^7-1
> i16    -(2^15)            2^15-1
> i32    -(2^31)            2^31-1
> i64    -(2^63)            2^63-1
> i128   -(2^127)           2^127-1
> isize  -(2^31) or -(2^63) 2^31-1 or 2^64-1"
-/

/--
Compute the unsigned modulus `2^(sizeBytes * 8) = 256^sizeBytes` for a scalar of
width `sizeBytes` using only `Init.Core` `Nat.mul`.
-/
def scalarModulus : Nat → Nat
  | .zero => 1
  | .succ k => Nat.mul 256 (scalarModulus k)

/--
Compute `2^k` for bit-shift scaling using only `Init.Core` `Nat.mul`.
-/
def scalarPow2 : Nat → Nat
  | .zero => 1
  | .succ k => Nat.mul 2 (scalarPow2 k)

/--
Reduce `val` modulo `modulus` (`2^(sizeBytes * 8)`).

When `val < modulus` (`Nat.ble modulus val = false`), `val` is already in
canonical range and is returned directly so symbolic values proven below
`modulus` reduce without requiring library division lemmas outside `Init.Core`.
-/
def wrapScalarBits (val modulus : Nat) : Nat :=
  match Nat.ble modulus val with
  | true => Nat.mod val modulus
  | false => val

/--
Encode a `Bool` as a 1-byte `ScalarInt` (`0x01` for `true`, `0x00` for `false`).

Reference (The Rust Reference, "Boolean type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>

> "An object with the boolean type has a size and alignment of 1 each."
>
> "The value false has the bit pattern 0x00 and the value true has the bit
> pattern 0x01. It is undefined behavior for an object with the boolean type to
> have any other bit pattern."
-/
def boolToScalar : Bool → ScalarInt
  | true => ⟨1, 1⟩
  | false => ⟨0, 1⟩

/--
Compute bitwise AND of `a` and `b` over `numBits` bits by structural recursion
on `numBits` using `Nat.div` and `Nat.mod` by `2`.

Reference (The Rust Reference, "Arithmetic and logical binary operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators>

> "Bitwise AND  `&`  Integer, bool"
-/
def bitwiseAndBits : Nat → Nat → Nat → Nat
  | .zero, _, _ => 0
  | .succ k, a, b =>
    let bitA := Nat.mod a 2
    let bitB := Nat.mod b 2
    let bit :=
      match Bool.and (Nat.beq bitA 1) (Nat.beq bitB 1) with
      | true => 1
      | false => 0
    Nat.add bit (Nat.mul 2 (bitwiseAndBits k (Nat.div a 2) (Nat.div b 2)))

/--
Compute bitwise OR of `a` and `b` over `numBits` bits by structural recursion
on `numBits` using `Nat.div` and `Nat.mod` by `2`.

Reference (The Rust Reference, "Arithmetic and logical binary operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators>

> "Bitwise OR   `|`  Integer, bool"
-/
def bitwiseOrBits : Nat → Nat → Nat → Nat
  | .zero, _, _ => 0
  | .succ k, a, b =>
    let bitA := Nat.mod a 2
    let bitB := Nat.mod b 2
    let bit :=
      match Bool.or (Nat.beq bitA 1) (Nat.beq bitB 1) with
      | true => 1
      | false => 0
    Nat.add bit (Nat.mul 2 (bitwiseOrBits k (Nat.div a 2) (Nat.div b 2)))

/--
Compute bitwise XOR of `a` and `b` over `numBits` bits by structural recursion
on `numBits` using `Nat.div` and `Nat.mod` by `2`.

Reference (The Rust Reference, "Arithmetic and logical binary operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators>

> "Bitwise XOR  `^`  Integer, bool"
-/
def bitwiseXorBits : Nat → Nat → Nat → Nat
  | .zero, _, _ => 0
  | .succ k, a, b =>
    let bitA := Nat.mod a 2
    let bitB := Nat.mod b 2
    let bit :=
      match Nat.beq bitA bitB with
      | true => 0
      | false => 1
    Nat.add bit (Nat.mul 2 (bitwiseXorBits k (Nat.div a 2) (Nat.div b 2)))

/--
Shift unsigned bit pattern `a` left by `shift` bits and wrap modulo `modulus`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1664-L1670>

> "/// The `<<` operator (shift left)
> ///
> /// The offset is given by `RHS.rem_euclid(LHS::BITS)`."
-/
def shiftLeftBits (a shift modulus : Nat) : Nat :=
  wrapScalarBits (Nat.mul a (scalarPow2 shift)) modulus

/--
Logical right shift of unsigned bit pattern `a` by `shift` bits (`a / 2^shift`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1673-L1682>

> "/// The `>>` operator (shift right)
> /// ...
> /// This is an arithmetic shift if the LHS is signed
> /// and a logical shift if the LHS is unsigned."
-/
def shiftRightUnsignedBits (a shift : Nat) : Nat :=
  Nat.div a (scalarPow2 shift)

/--
Test whether two's-complement bit pattern `bits` of byte width `sizeBytes` has
its sign bit set (`bits mod 2^(8 * sizeBytes) >= 2^(8 * sizeBytes - 1)`).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of:
>
> Type   Minimum            Maximum
> i8     -(2^7)             2^7-1
> i16    -(2^15)            2^15-1
> i32    -(2^31)            2^31-1
> i64    -(2^63)            2^63-1
> i128   -(2^127)           2^127-1"
-/
def isSignedNegative (bits sizeBytes : Nat) : Bool :=
  match Nat.beq sizeBytes 0 with
  | true => false
  | false =>
    let modulus := scalarModulus sizeBytes
    let halfModulus := Nat.div modulus 2
    let canonical := wrapScalarBits bits modulus
    Nat.ble halfModulus canonical

/--
Arithmetic right shift of two's-complement bit pattern `bits` of byte width
`sizeBytes` by `shift` bits.

When `isSignedNegative bits sizeBytes` holds, the shifted-in high bits up to
`sizeBytes * 8` are filled with `1`s; otherwise this reduces to logical right
shift (`shiftRightUnsignedBits`).

Reference (The Rust Reference, "Arithmetic and logical binary operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators>

> "Arithmetic right shift on signed integer types, logical right shift on
> unsigned integer types."
-/
def arithmeticShrBits (bits sizeBytes shift : Nat) : Nat :=
  let modulus := scalarModulus sizeBytes
  let canonical := wrapScalarBits bits modulus
  let logical := shiftRightUnsignedBits canonical shift
  match isSignedNegative canonical sizeBytes with
  | false => wrapScalarBits logical modulus
  | true =>
    let numBits := Nat.mul sizeBytes 8
    let highOnes := Nat.sub modulus (scalarPow2 (Nat.sub numBits shift))
    wrapScalarBits (Nat.add logical highOnes) modulus

/--
Signed two's-complement less-than comparison (`a < b`) at byte width
`sizeBytes`.

Reference (The Rust Reference, "Comparison operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#comparison-operators>

> "Comparison operators are defined for primitive integer, floating-point, bool,
> and char types, as well as for pointers and function pointers."
-/
def signedLt (a b sizeBytes : Nat) : Bool :=
  let modulus := scalarModulus sizeBytes
  let ca := wrapScalarBits a modulus
  let cb := wrapScalarBits b modulus
  match isSignedNegative ca sizeBytes, isSignedNegative cb sizeBytes with
  | true, false => true
  | false, true => false
  | _, _ => Bool.not (Nat.ble cb ca)

/--
Signed two's-complement less-than-or-equal comparison (`a <= b`) at byte width
`sizeBytes`.

Reference (The Rust Reference, "Comparison operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#comparison-operators>

> "Comparison operators are defined for primitive integer, floating-point, bool,
> and char types, as well as for pointers and function pointers."
-/
def signedLe (a b sizeBytes : Nat) : Bool :=
  Bool.not (signedLt b a sizeBytes)

/--
Two's-complement sign extension (or truncation when `dstBytes <= srcBytes`) of
`bits` from byte width `srcBytes` to `dstBytes`.

Reference (The Rust Reference, "Type cast expressions — Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from a smaller integer to a larger integer (e.g. u8 -> u32) will
> - zero-extend if the source is unsigned
> - sign-extend if the source is signed"
-/
def signExtendBits (bits srcBytes dstBytes : Nat) : Nat :=
  let srcMod := scalarModulus srcBytes
  let dstMod := scalarModulus dstBytes
  let canonical := wrapScalarBits bits srcMod
  match Nat.ble dstBytes srcBytes with
  | true => wrapScalarBits canonical dstMod
  | false =>
    match isSignedNegative canonical srcBytes with
    | false => canonical
    | true => Nat.add (Nat.sub dstMod srcMod) canonical

/--
Default empty `LayoutTable` on a 64-bit little-endian target for type queries
that do not require ADT layout-table entries.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L259-L264>

> "pub enum Endian {
>     Little,
>     Big,
> }"
-/
@[reducible]
def emptyLayoutTable : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := .nil }

/--
Extract the pointee `Ty` from a reference, raw pointer, or `Box<T>` type when
resolving a `ProjectionElem.deref` step.

Reference (The Rust Reference, "The Dereference Operator"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#the-dereference-operator>

> "The `*` (dereference) operator is also a unary prefix operator. When applied
> to a pointer it denotes the pointed-to location."
-/
@[reducible]
def pointeeTyOf (baseTy : Ty) : Option Ty :=
  match baseTy.kind with
  | .ref _ inner => .some { kind := inner, layoutIdx := 0 }
  | .rawPtr _ inner => .some { kind := inner, layoutIdx := 0 }
  | .adt defPath (inner :: .nil) =>
    match
      Bool.or
        (stringEq defPath "std::boxed::Box")
        (stringEq defPath "alloc::boxed::Box")
    with
    | true => .some { kind := inner, layoutIdx := 0 }
    | false => .none
  | _ => .none

/--
Extract the element `Ty` from an array `[T; N]` or slice `[T]` type when
resolving a `ProjectionElem.index` or `ProjectionElem.constantIndex` step.

Reference (The Rust Reference, "Array and slice indexing expressions"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/array-expr.html#array-and-slice-indexing-expressions>

> "Array and slice-typed expressions can be indexed with a usize index to access
> elements of the array or slice."
-/
@[reducible]
def elemTyOf (baseTy : Ty) : Option Ty :=
  match baseTy.kind with
  | .array elemKind _ => .some { kind := elemKind, layoutIdx := 0 }
  | .slice elemKind => .some { kind := elemKind, layoutIdx := 0 }
  | _ => .none

/--
Resolve the projected `Ty` reached by traversing `proj` starting from `baseTy`.

- `.nil` returns `.some baseTy`.
- `.field _ fieldTy`, `.opaqueCast castTy`, and `.unwrapUnsafeBinder innerTy`
  advance directly to the projection's embedded `Ty` and recurse on the tail.
- `.deref` extracts the pointee `Ty` of `.ref`, `.rawPtr`, or `Box<T>` via
  `pointeeTyOf` and recurses on the tail.
- `.index _` and `.constantIndex _ _ _` extract the element `Ty` of `.array` or
  `.slice` via `elemTyOf` and recurse on the tail.
- `.subslice _ _ _` and `.downcast _ _` preserve `baseTy` and recurse on the
  tail.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1127-L1168>

> "pub enum ProjectionElem<V, T> {
>     Deref,
>     Field(FieldIdx, T),
>     Index(V),
>     ConstantIndex { offset: u64, min_length: u64, from_end: bool },
>     Subslice { from: u64, to: u64, from_end: bool },
>     Downcast(Option<Symbol>, VariantIdx),
>     OpaqueCast(T),
>     UnwrapUnsafeBinder(T),
> }"
-/
@[reducible]
def resolveProjectedTy
    (layouts : LayoutTable)
    (baseTy : Ty)
    (proj : List ProjectionElem) :
    Option Ty :=
  match proj with
  | .nil => .some baseTy
  | .field _ fieldTy :: rest => resolveProjectedTy layouts fieldTy rest
  | .opaqueCast castTy :: rest => resolveProjectedTy layouts castTy rest
  | .unwrapUnsafeBinder innerTy :: rest =>
    resolveProjectedTy layouts innerTy rest
  | .deref :: rest =>
    match pointeeTyOf baseTy with
    | .some innerTy => resolveProjectedTy layouts innerTy rest
    | .none => .none
  | .index _ :: rest =>
    match elemTyOf baseTy with
    | .some elemTy => resolveProjectedTy layouts elemTy rest
    | .none => .none
  | .constantIndex _ _ _ :: rest =>
    match elemTyOf baseTy with
    | .some elemTy => resolveProjectedTy layouts elemTy rest
    | .none => .none
  | .subslice _ _ _ :: rest => resolveProjectedTy layouts baseTy rest
  | .downcast _ _ :: rest => resolveProjectedTy layouts baseTy rest

/--
Resolve the `Ty` of a `Place` `p` by looking up `p.local_` in `localDecls` and
walking `p.projection` via `resolveProjectedTy`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1264-L1270>

> "pub struct Place<'tcx> {
>     pub local: Local,
>     pub projection: &'tcx List<PlaceElem<'tcx>>,
> }"
-/
@[reducible]
def placeTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable := emptyLayoutTable)
    (p : Place) :
    Option Ty :=
  match get? localDecls p.local_ with
  | .some decl => resolveProjectedTy layouts decl.ty p.projection
  | .none => .none

/--
Resolve the `Ty` of an `Operand` `op` by resolving `placeTy` for `.copy p` and
`.move p` or returning `c.ty` for `.constant c`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1314-L1330>

> "pub enum Operand<'tcx> {
>     Copy(Place<'tcx>),
>     Move(Place<'tcx>),
>     Constant(Box<ConstOperand<'tcx>>),
> }"
-/
@[reducible]
def operandTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable := emptyLayoutTable)
    (op : Operand) :
    Option Ty :=
  match op with
  | .copy p => placeTy localDecls layouts p
  | .move p => placeTy localDecls layouts p
  | .constant c => .some c.ty

/--
Test whether `ty` is a signed integer type (`RigidTy.int _`).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"
-/
@[reducible]
def tyIsSigned (ty : Ty) : Bool :=
  match ty.kind with
  | .int _ => true
  | _ => false

/--
Test whether `p` resolves (across its full projection chain) to a signed integer
`Ty` in `localDecls`.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"
-/
@[reducible]
def placeIsSigned
    (localDecls : List LocalDecl)
    (p : Place)
    (layouts : LayoutTable := emptyLayoutTable) :
    Bool :=
  match placeTy localDecls layouts p with
  | .some ty => tyIsSigned ty
  | .none => false

/--
Test whether `op` has a signed integer type according to `operandTy` (resolving
`.copy p` and `.move p` across arbitrary projection chains in `localDecls`, or
inspecting `c.ty` for `.constant c`).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"
-/
@[reducible]
def operandIsSigned
    (localDecls : List LocalDecl)
    (op : Operand)
    (layouts : LayoutTable := emptyLayoutTable) :
    Bool :=
  match operandTy localDecls layouts op with
  | .some ty => tyIsSigned ty
  | .none => false

/--
Evaluate `UnOp.not` (`!x`) on a scalar operand `sc` with resolved operand type
`optTy`.

- When `optTy` is `.some { kind := .bool, .. }`: inverts `0` (`false`) to `1`
  (`true`) and `1` (`true`) to `0` (`false`) at width `1` byte; any other bit
  pattern is undefined behavior (`.ub`).
- When `optTy` is `.some { kind := .uint _, .. }` or
  `.some { kind := .int _, .. }` (or when `optTy` is `.none` on a multi-byte or
  non-boolean scalar): computes the bitwise complement
  `(2^(8 * sc.sizeBytes) - 1) - (sc.bits mod 2^(8 * sc.sizeBytes))` at byte
  width `sc.sizeBytes`.

Reference (The Rust Reference, "Negation operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#negation-operators>

> "These are the last two unary operators. This table summarizes the behavior
> of them on primitive types and which traits are used to overload these
> operators for other types. Remember that signed integers are always
> represented using two's complement. The operands of all of these operators
> are evaluated in value expression context so are moved or copied.
>
> * Negation `-`: Signed integer, Floating-point (`std::ops::Neg`)
> * Not `!`: Integer, `bool` (`std::ops::Not`) — Bitwise NOT (inverts the
>   individual bits) for integer types; logical NOT (inverts the boolean value)
>   for `bool`."

Reference (The Rust Reference, "Boolean type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>

> "The value false has the bit pattern 0x00 and the value true has the bit
> pattern 0x01. It is undefined behavior for an object with the boolean type to
> have any other bit pattern."
-/
def evalUnaryNot
    (sc : ScalarInt)
    (optTy : Option Ty)
    (locals : List LocalSlot)
    (mem : Memory) :
    RvalueEvalResult :=
  match optTy with
  | .some ty =>
    match ty.kind with
    | .bool =>
      match Nat.beq sc.sizeBytes 1 with
      | false => .ub
      | true =>
        match Nat.beq sc.bits 0 with
        | true => .ok (.scalar ⟨1, 1⟩) locals mem
        | false =>
          match Nat.beq sc.bits 1 with
          | true => .ok (.scalar ⟨0, 1⟩) locals mem
          | false => .ub
    | .uint _ =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let modulus := scalarModulus sc.sizeBytes
        let canonical := wrapScalarBits sc.bits modulus
        let comp := Nat.sub (Nat.sub modulus 1) canonical
        .ok (.scalar ⟨comp, sc.sizeBytes⟩) locals mem
    | .int _ =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let modulus := scalarModulus sc.sizeBytes
        let canonical := wrapScalarBits sc.bits modulus
        let comp := Nat.sub (Nat.sub modulus 1) canonical
        .ok (.scalar ⟨comp, sc.sizeBytes⟩) locals mem
    | _ => .unsupported
  | .none =>
    match Nat.beq sc.sizeBytes 0 with
    | true => .unsupported
    | false =>
      match Nat.beq sc.sizeBytes 1 with
      | true =>
        match Nat.beq sc.bits 0 with
        | true => .ok (.scalar ⟨1, 1⟩) locals mem
        | false =>
          match Nat.beq sc.bits 1 with
          | true => .ok (.scalar ⟨0, 1⟩) locals mem
          | false =>
            let modulus := scalarModulus 1
            let canonical := wrapScalarBits sc.bits modulus
            let comp := Nat.sub (Nat.sub modulus 1) canonical
            .ok (.scalar ⟨comp, 1⟩) locals mem
      | false =>
        let modulus := scalarModulus sc.sizeBytes
        let canonical := wrapScalarBits sc.bits modulus
        let comp := Nat.sub (Nat.sub modulus 1) canonical
        .ok (.scalar ⟨comp, sc.sizeBytes⟩) locals mem

/--
Test whether signed two's-complement addition of `lhs` and `rhs` at byte width
`sizeBytes` overflows `[-2^(8 * sizeBytes - 1), 2^(8 * sizeBytes - 1) - 1]`.

Signed addition overflows if and only if both operands have the same sign and
the wrapped sum has the opposite sign.

Reference (The Rust Reference, "Operator expressions — Overflow"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#overflow>

> "The following things are considered to be overflow:
> - When +, * or binary - create a value greater than the maximum value, or
>   less than the minimum value that can be stored."
-/
def signedOverflowAdd (lhs rhs sizeBytes : Nat) : Bool :=
  let modulus := scalarModulus sizeBytes
  let sum := wrapScalarBits (Nat.add lhs rhs) modulus
  match
    isSignedNegative lhs sizeBytes,
    isSignedNegative rhs sizeBytes,
    isSignedNegative sum sizeBytes
  with
  | true, true, false => true
  | false, false, true => true
  | _, _, _ => false

/--
Test whether signed two's-complement subtraction `lhs - rhs` at byte width
`sizeBytes` overflows `[-2^(8 * sizeBytes - 1), 2^(8 * sizeBytes - 1) - 1]`.

Signed subtraction overflows if and only if `lhs` and `rhs` have opposite signs
and the wrapped difference has a sign different from `lhs`.

Reference (The Rust Reference, "Operator expressions — Overflow"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#overflow>

> "The following things are considered to be overflow:
> - When +, * or binary - create a value greater than the maximum value, or
>   less than the minimum value that can be stored."
-/
def signedOverflowSub (lhs rhs sizeBytes : Nat) : Bool :=
  let modulus := scalarModulus sizeBytes
  let ca := wrapScalarBits lhs modulus
  let cb := wrapScalarBits rhs modulus
  let diff :=
    match Nat.ble cb ca with
    | true => wrapScalarBits (Nat.sub ca cb) modulus
    | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
  match
    isSignedNegative ca sizeBytes,
    isSignedNegative cb sizeBytes,
    isSignedNegative diff sizeBytes
  with
  | true, false, false => true
  | false, true, true => true
  | _, _, _ => false

/--
Test whether signed two's-complement multiplication `lhs * rhs` at byte width
`sizeBytes` overflows `[-2^(8 * sizeBytes - 1), 2^(8 * sizeBytes - 1) - 1]`.

Reference (The Rust Reference, "Operator expressions — Overflow"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#overflow>

> "The following things are considered to be overflow:
> - When +, * or binary - create a value greater than the maximum value, or
>   less than the minimum value that can be stored."
-/
def signedOverflowMul (lhs rhs sizeBytes : Nat) : Bool :=
  match Nat.beq sizeBytes 0 with
  | true => false
  | false =>
    let modulus := scalarModulus sizeBytes
    let halfModulus := Nat.div modulus 2
    let ca := wrapScalarBits lhs modulus
    let cb := wrapScalarBits rhs modulus
    let negA := isSignedNegative ca sizeBytes
    let negB := isSignedNegative cb sizeBytes
    let magA := match negA with | false => ca | true => Nat.sub modulus ca
    let magB := match negB with | false => cb | true => Nat.sub modulus cb
    let magProd := Nat.mul magA magB
    match Nat.beq magProd 0 with
    | true => false
    | false =>
      match negA, negB with
      | false, false => Nat.ble halfModulus magProd
      | true, true => Nat.ble halfModulus magProd
      | _, _ => Bool.not (Nat.ble magProd halfModulus)

/--
Evaluate signed two's-complement integer division `a / b` at byte width `sz`
(where `b != 0` has already been checked).

In addition to division by zero, dividing the minimum signed value `-2^(w-1)` by
`-1` is undefined behavior in MIR `BinOp::Div`. Otherwise, the quotient
truncates toward zero.

Reference (The Rust Reference, "Arithmetic and logical binary operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators>

> "Integer division rounds towards zero."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1649-L1654>

> "/// The `/` operator (division)
> ///
> /// For integer types, division by zero is UB, as is `MIN / -1` for signed."
-/
def evalSignedDiv
    (a b sz : Nat)
    (locals : List LocalSlot)
    (mem : Memory) :
    RvalueEvalResult :=
  let modulus := scalarModulus sz
  let numBits := Nat.mul sz 8
  let minSigned := scalarPow2 (Nat.sub numBits 1)
  let minusOne := Nat.sub modulus 1
  let ca := wrapScalarBits a modulus
  let cb := wrapScalarBits b modulus
  match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with
  | true => .ub
  | false =>
    let negA := isSignedNegative ca sz
    let negB := isSignedNegative cb sz
    let magA := match negA with | false => ca | true => Nat.sub modulus ca
    let magB := match negB with | false => cb | true => Nat.sub modulus cb
    let magQ := Nat.div magA magB
    let quotBits :=
      match Nat.beq magQ 0 with
      | true => 0
      | false =>
        match negA, negB with
        | false, false => wrapScalarBits magQ modulus
        | true, true => wrapScalarBits magQ modulus
        | _, _ => wrapScalarBits (Nat.sub modulus magQ) modulus
    .ok (.scalar ⟨quotBits, sz⟩) locals mem

/--
Evaluate signed two's-complement integer remainder `a % b` at byte width `sz`
(where `b != 0` has already been checked).

In addition to remainder by zero, `MIN % -1` is undefined behavior in MIR
`BinOp::Rem`. Otherwise, the remainder has the sign of the dividend `a`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1655-L1660>

> "/// The `%` operator (remainder)
> ///
> /// For integer types, remainder by zero is UB, as is `MIN % -1` for signed."
-/
def evalSignedRem
    (a b sz : Nat)
    (locals : List LocalSlot)
    (mem : Memory) :
    RvalueEvalResult :=
  let modulus := scalarModulus sz
  let numBits := Nat.mul sz 8
  let minSigned := scalarPow2 (Nat.sub numBits 1)
  let minusOne := Nat.sub modulus 1
  let ca := wrapScalarBits a modulus
  let cb := wrapScalarBits b modulus
  match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with
  | true => .ub
  | false =>
    let negA := isSignedNegative ca sz
    let negB := isSignedNegative cb sz
    let magA := match negA with | false => ca | true => Nat.sub modulus ca
    let magB := match negB with | false => cb | true => Nat.sub modulus cb
    let magR := Nat.mod magA magB
    let remBits :=
      match Nat.beq magR 0 with
      | true => 0
      | false =>
        match negA with
        | false => wrapScalarBits magR modulus
        | true => wrapScalarBits (Nat.sub modulus magR) modulus
    .ok (.scalar ⟨remBits, sz⟩) locals mem

/--
Evaluate the `core::intrinsics::exact_div` intrinsic over two concrete
`ScalarInt` operands `lhs` and `rhs`, dispatching signed two's-complement exact
division when `isSigned == true` and unsigned exact division when
`isSigned == false`.

Division by zero (`rhs.bits == 0`), signed overflow (`MIN / -1`), or a non-zero
remainder (`lhs % rhs != 0`) is undefined behavior (`.ub`).

Reference (`core::intrinsics::exact_div`, Rust 1.98.0 standard library):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.exact_div.html>

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1932-L1939>

> "/// Performs an exact division, resulting in undefined behavior where
> /// `x % y != 0` or `y == 0` or `x == T::MIN && y == -1`
> ///
> /// This intrinsic does not have a stable counterpart.
> #[rustc_intrinsic_const_stable_indirect]
> #[rustc_nounwind]
> #[rustc_intrinsic]
> pub const unsafe fn exact_div<T: Copy>(x: T, y: T) -> T;"
-/
def evalExactDiv
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory := {})
    (isSigned : Bool := false) :
    RvalueEvalResult :=
  match Nat.beq lhs.sizeBytes 0 with
  | true => .ub
  | false =>
    match Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false => .ub
    | true =>
      let sz := lhs.sizeBytes
      let modulus := scalarModulus sz
      let a := lhs.bits
      let b := rhs.bits
      match Nat.beq b 0 with
      | true => .ub
      | false =>
        match isSigned with
        | false =>
          match Nat.beq (Nat.mod a b) 0 with
          | true => .ok (.scalar ⟨wrapScalarBits (Nat.div a b) modulus, sz⟩) locals mem
          | false => .ub
        | true =>
          match evalSignedRem a b sz locals mem with
          | .ok (.scalar remSc) _ _ =>
            match Nat.beq remSc.bits 0 with
            | true => evalSignedDiv a b sz locals mem
            | false => .ub
          | .ok _ _ _ => .ub
          | .ub => .ub
          | .unsupported => .ub

/--
Alias for `evalExactDiv` matching the `V2026_06_01` `RvalueEvalResult` helper
name (`evalScalarExactDiv`).

Reference (`core::intrinsics::exact_div`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.exact_div.html>

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1932-L1939>

> "/// Performs an exact division, resulting in undefined behavior where
> /// `x % y != 0` or `y == 0` or `x == T::MIN && y == -1`
> ///
> /// This intrinsic does not have a stable counterpart."
-/
abbrev evalScalarExactDiv := evalExactDiv

/--
Evaluate a `BinOp` over two concrete `ScalarInt` operands `lhs` and `rhs` of
non-zero byte width `sizeBytes`, dispatching signed operations when
`isSigned = true` and unsigned operations when `isSigned = false`.

Reference (The Rust Reference, "Operator expressions — Overflow"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#overflow>

> "The following things are considered to be overflow:
> - When +, * or binary - create a value greater than the maximum value, or
>   less than the minimum value that can be stored."

Reference (The Rust Reference, "Behavior not considered unsafe"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-not-considered-unsafe.html#integer-overflow>

> "In the case of implicitly-wrapped overflow, implementations must provide
> well-defined (even if still considered erroneous) results by using two’s
> complement overflow conventions."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1706>

> "pub enum BinOp {
>     /// The `+` operator (addition)
>     Add,
>     /// Like `Add`, but with UB on overflow.  (Integers only.)
>     AddUnchecked,
>     /// Like `Add`, but returns `(T, bool)` of both the wrapped result
>     /// and a bool indicating whether it overflowed.
>     AddWithOverflow,
> ...
>     /// The `<<` operator (shift left)
>     ///
>     /// The offset is given by `RHS.rem_euclid(LHS::BITS)`. ...
>     Shl,
>     /// Like `Shl`, but is UB if the RHS >= LHS::BITS or RHS < 0
>     ShlUnchecked,
>     /// The `>>` operator (shift right) ...
>     Shr,
>     /// Like `Shl`, but is UB if the RHS >= LHS::BITS or RHS < 0
>     ShrUnchecked,
> ...
>     /// [`Rvalue::BinaryOp`]`(BinOp::Cmp, A, B)` returns
>     /// - `Ordering::Less` (`-1_i8`, as a Scalar) if `A < B`
>     /// - `Ordering::Equal` (`0_i8`, as a Scalar) if `A == B`
>     /// - `Ordering::Greater` (`+1_i8`, as a Scalar) if `A > B`
>     Cmp,"
-/
def evalScalarBinOp
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory := {})
    (isSigned : Bool := false) :
    RvalueEvalResult :=
  match Nat.beq lhs.sizeBytes 0 with
  | true => .unsupported
  | false =>
    let sz := lhs.sizeBytes
    let numBits := Nat.mul sz 8
    let modulus := scalarModulus sz
    let a := lhs.bits
    let b := rhs.bits
    match op with
    | .shl =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let shift := Nat.mod b numBits
        .ok (.scalar ⟨shiftLeftBits a shift modulus, sz⟩) locals mem
    | .shlUnchecked =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .unsupported
      | false =>
        match Nat.ble numBits b with
        | true => .ub
        | false => .ok (.scalar ⟨shiftLeftBits a b modulus, sz⟩) locals mem
    | .shr =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let shift := Nat.mod b numBits
        let shifted :=
          match isSigned with
          | false => wrapScalarBits (shiftRightUnsignedBits a shift) modulus
          | true => arithmeticShrBits a sz shift
        .ok (.scalar ⟨shifted, sz⟩) locals mem
    | .shrUnchecked =>
      match Nat.beq rhs.sizeBytes 0 with
      | true => .unsupported
      | false =>
        match Nat.ble numBits b with
        | true => .ub
        | false =>
          let shifted :=
            match isSigned with
            | false => wrapScalarBits (shiftRightUnsignedBits a b) modulus
            | true => arithmeticShrBits a sz b
          .ok (.scalar ⟨shifted, sz⟩) locals mem
    | _ =>
      match Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => .unsupported
      | true =>
        match op with
        | .add =>
          let sum := Nat.add a b
          .ok (.scalar ⟨wrapScalarBits sum modulus, sz⟩) locals mem
        | .addUnchecked =>
          let sum := Nat.add a b
          match isSigned with
          | false =>
            match Nat.ble modulus sum with
            | true => .ub
            | false => .ok (.scalar ⟨sum, sz⟩) locals mem
          | true =>
            match signedOverflowAdd a b sz with
            | true => .ub
            | false => .ok (.scalar ⟨wrapScalarBits sum modulus, sz⟩) locals mem
        | .addWithOverflow =>
          let sum := Nat.add a b
          let wrapped : ScalarInt := ⟨wrapScalarBits sum modulus, sz⟩
          let overflowBit :=
            match isSigned with
            | false => match Nat.ble modulus sum with | true => 1 | false => 0
            | true =>
              match signedOverflowAdd a b sz with | true => 1 | false => 0
          .ok
            (.aggregate 0 (.scalar wrapped :: .scalar ⟨overflowBit, 1⟩ :: .nil))
            locals
            mem
        | .sub =>
          match Nat.ble b a with
          | true =>
            .ok (.scalar ⟨wrapScalarBits (Nat.sub a b) modulus, sz⟩) locals mem
          | false =>
            let wrappedDiff :=
              wrapScalarBits
                (Nat.sub (Nat.add modulus (wrapScalarBits a modulus))
                  (wrapScalarBits b modulus))
                modulus
            .ok (.scalar ⟨wrappedDiff, sz⟩) locals mem
        | .subUnchecked =>
          match isSigned with
          | false =>
            match Nat.ble b a with
            | true =>
              let diff := Nat.sub a b
              match Nat.ble modulus diff with
              | true => .ub
              | false => .ok (.scalar ⟨diff, sz⟩) locals mem
            | false => .ub
          | true =>
            match signedOverflowSub a b sz with
            | true => .ub
            | false =>
              let ca := wrapScalarBits a modulus
              let cb := wrapScalarBits b modulus
              let wrappedDiff :=
                match Nat.ble cb ca with
                | true => wrapScalarBits (Nat.sub ca cb) modulus
                | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
              .ok (.scalar ⟨wrappedDiff, sz⟩) locals mem
        | .subWithOverflow =>
          match isSigned with
          | false =>
            match Nat.ble b a with
            | true =>
              let diff := wrapScalarBits (Nat.sub a b) modulus
              .ok
                (.aggregate 0 (.scalar ⟨diff, sz⟩ :: .scalar ⟨0, 1⟩ :: .nil))
                locals
                mem
            | false =>
              let wrappedDiff :=
                wrapScalarBits
                  (Nat.sub (Nat.add modulus (wrapScalarBits a modulus))
                    (wrapScalarBits b modulus))
                  modulus
              .ok
                (.aggregate 0
                  (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨1, 1⟩ :: .nil))
                locals
                mem
          | true =>
            let ca := wrapScalarBits a modulus
            let cb := wrapScalarBits b modulus
            let wrappedDiff :=
              match Nat.ble cb ca with
              | true => wrapScalarBits (Nat.sub ca cb) modulus
              | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
            let overflowBit :=
              match signedOverflowSub a b sz with | true => 1 | false => 0
            .ok
              (.aggregate 0
                (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨overflowBit, 1⟩ :: .nil))
              locals
              mem
        | .mul =>
          let prod := Nat.mul a b
          .ok (.scalar ⟨wrapScalarBits prod modulus, sz⟩) locals mem
        | .mulUnchecked =>
          let prod := Nat.mul a b
          match isSigned with
          | false =>
            match Nat.ble modulus prod with
            | true => .ub
            | false => .ok (.scalar ⟨prod, sz⟩) locals mem
          | true =>
            match signedOverflowMul a b sz with
            | true => .ub
            | false => .ok (.scalar ⟨wrapScalarBits prod modulus, sz⟩) locals mem
        | .mulWithOverflow =>
          let prod := Nat.mul a b
          let wrapped : ScalarInt := ⟨wrapScalarBits prod modulus, sz⟩
          let overflowBit :=
            match isSigned with
            | false => match Nat.ble modulus prod with | true => 1 | false => 0
            | true =>
              match signedOverflowMul a b sz with | true => 1 | false => 0
          .ok
            (.aggregate 0 (.scalar wrapped :: .scalar ⟨overflowBit, 1⟩ :: .nil))
            locals
            mem
        | .div =>
          match Nat.beq b 0 with
          | true => .ub
          | false =>
            match isSigned with
            | false =>
              .ok (.scalar ⟨wrapScalarBits (Nat.div a b) modulus, sz⟩) locals mem
            | true => evalSignedDiv a b sz locals mem
        | .rem =>
          match Nat.beq b 0 with
          | true => .ub
          | false =>
            match isSigned with
            | false =>
              .ok (.scalar ⟨wrapScalarBits (Nat.mod a b) modulus, sz⟩) locals mem
            | true => evalSignedRem a b sz locals mem
        | .bitAnd =>
          .ok (.scalar ⟨bitwiseAndBits numBits a b, sz⟩) locals mem
        | .bitOr =>
          .ok (.scalar ⟨bitwiseOrBits numBits a b, sz⟩) locals mem
        | .bitXor =>
          .ok (.scalar ⟨bitwiseXorBits numBits a b, sz⟩) locals mem
        | .eq => .ok (.scalar (boolToScalar (Nat.beq a b))) locals mem
        | .ne =>
          .ok (.scalar (boolToScalar (Bool.not (Nat.beq a b)))) locals mem
        | .lt =>
          let cmp :=
            match isSigned with
            | false => Bool.not (Nat.ble b a)
            | true => signedLt a b sz
          .ok (.scalar (boolToScalar cmp)) locals mem
        | .le =>
          let cmp :=
            match isSigned with
            | false => Nat.ble a b
            | true => signedLe a b sz
          .ok (.scalar (boolToScalar cmp)) locals mem
        | .gt =>
          let cmp :=
            match isSigned with
            | false => Bool.not (Nat.ble a b)
            | true => signedLt b a sz
          .ok (.scalar (boolToScalar cmp)) locals mem
        | .ge =>
          let cmp :=
            match isSigned with
            | false => Nat.ble b a
            | true => signedLe b a sz
          .ok (.scalar (boolToScalar cmp)) locals mem
        | .cmp =>
          match isSigned with
          | false =>
            match Nat.beq a b with
            | true => .ok (.scalar ⟨0, 1⟩) locals mem
            | false =>
              match Nat.ble a b with
              | true => .ok (.scalar ⟨255, 1⟩) locals mem
              | false => .ok (.scalar ⟨1, 1⟩) locals mem
          | true =>
            let ca := wrapScalarBits a modulus
            let cb := wrapScalarBits b modulus
            match Nat.beq ca cb with
            | true => .ok (.scalar ⟨0, 1⟩) locals mem
            | false =>
              match signedLt ca cb sz with
              | true => .ok (.scalar ⟨255, 1⟩) locals mem
              | false => .ok (.scalar ⟨1, 1⟩) locals mem
        | _ => .unsupported

/--
Target byte width for integer cast targets (`CastKind.intToInt`), parameterized
by target pointer width `ptrBytes` (defaulting to `8` bytes for 64-bit targets,
or `4` bytes for 32-bit targets for `usize` and `isize`).

Reference (The Rust Reference, "Type cast expressions — Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting between two integers of the same size (e.g. i32 -> u32) is a no-op
> (Rust uses 2’s complement for negative values of fixed integers)"
>
> "Casting from a larger integer to a smaller integer (e.g. u32 -> u8) will
> truncate"

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The size of this primitive is how many bytes it takes to reference any
> location in memory. For example, on a 32 bit target, this is 4 bytes and on a
> 64 bit target, this is 8 bytes."
-/
def intCastTargetBytes (ty : RigidTy) (ptrBytes : Nat := 8) : Option Nat :=
  match ty with
  | .uint .u8 => .some 1
  | .uint .u16 => .some 2
  | .uint .u32 => .some 4
  | .uint .u64 => .some 8
  | .uint .u128 => .some 16
  | .uint .usize => .some ptrBytes
  | .int .i8 => .some 1
  | .int .i16 => .some 2
  | .int .i32 => .some 4
  | .int .i64 => .some 8
  | .int .i128 => .some 16
  | .int .isize => .some ptrBytes
  | _ => .none

/--
Compute the signed half-modulus `2^(8 * sizeBytes - 1)` (the unsigned bit
pattern of `T::MIN` for a signed integer of byte width `sizeBytes`).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8, i16, i32, i64,
> i128, isize"
-/
@[reducible]
def signedHalfModulus (sizeBytes : Nat) : Nat :=
  Nat.div (scalarModulus sizeBytes) 2

/--
Count the number of set (`1`) bits in the low `remBits` bits of `bits` by
structural recursion (`core::intrinsics::ctpop`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1656-L1669>

> "/// Returns the number of bits set in an integer type `T`
> ...
> #[rustc_intrinsic]
> pub const fn ctpop<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def ctpopLoop : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ remBits, bits =>
    Nat.add (Nat.mod bits 2) (ctpopLoop remBits (Nat.div bits 2))

/--
Count consecutive trailing zero (`0`) bits starting from the least significant
bit across `remBits` bits of `bits` (`core::intrinsics::cttz`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1734-L1773>

> "/// Returns the number of trailing unset bits (zeroes) in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn cttz<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def cttzLoop : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ remBits, bits =>
    match Nat.beq (Nat.mod bits 2) 0 with
    | true => Nat.add 1 (cttzLoop remBits (Nat.div bits 2))
    | false => 0

/--
Reverse the low `remBits` bits of `bits` into accumulator `acc`
(`core::intrinsics::bitreverse`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1812-L1825>

> "/// Reverses the bits in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn bitreverse<T: Copy>(x: T) -> T;"
-/
@[reducible]
def bitreverseLoop : Nat → Nat → Nat → Nat
  | .zero, _, acc => acc
  | .succ remBits, bits, acc =>
    bitreverseLoop
      remBits
      (Nat.div bits 2)
      (Nat.add (Nat.mul acc 2) (Nat.mod bits 2))

/--
Count consecutive leading zero (`0`) bits starting from the most significant bit
of a `numBits`-bit unsigned word `bits` (`core::intrinsics::ctlz`), computed as
the trailing zero count of the `numBits`-bit reversal of `bits`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1671-L1710>

> "/// Returns the number of leading unset bits (zeroes) in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn ctlz<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def ctlzBits (numBits bits : Nat) : Nat :=
  cttzLoop numBits (bitreverseLoop numBits bits 0)

/--
Reverse the low `remBytes` bytes of `bits` into accumulator `acc`
(`core::intrinsics::bswap`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1797-L1810>

> "/// Reverses the bytes in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn bswap<T: Copy>(x: T) -> T;"
-/
@[reducible]
def bswapLoop : Nat → Nat → Nat → Nat
  | .zero, _, acc => acc
  | .succ remBytes, bits, acc =>
    bswapLoop
      remBytes
      (Nat.div bits 256)
      (Nat.add (Nat.mul acc 256) (Nat.mod bits 256))

/--
Evaluate `core::intrinsics::ctlz(sc)`, returning a `retBytes`-byte `ScalarInt`
(default `4` bytes for `u32`) holding the count of leading zero bits in `sc`.
Returns `.none` if `sc.sizeBytes == 0` or `retBytes == 0`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1671-L1710>

> "/// Returns the number of leading unset bits (zeroes) in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn ctlz<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def evalCtlz (sc : ScalarInt) (retBytes : Nat := 4) : Option ScalarInt :=
  match Bool.or (Nat.beq sc.sizeBytes 0) (Nat.beq retBytes 0) with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    .some ⟨ctlzBits (Nat.mul sc.sizeBytes 8) ca, retBytes⟩

/--
Evaluate `core::intrinsics::ctlz_nonzero(sc)`, returning `.none` (undefined
behavior) when `sc` is zero (`ca == 0`) or has zero byte width.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1712-L1732>

> "/// Like `ctlz`, but extra-unsafe as it returns `undef` when
> /// given an `x` with value `0`.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn ctlz_nonzero<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def evalCtlzNonzero (sc : ScalarInt) (retBytes : Nat := 4) : Option ScalarInt :=
  match Bool.or (Nat.beq sc.sizeBytes 0) (Nat.beq retBytes 0) with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    match Nat.beq ca 0 with
    | true => .none
    | false => .some ⟨ctlzBits (Nat.mul sc.sizeBytes 8) ca, retBytes⟩

/--
Evaluate `core::intrinsics::cttz(sc)`, returning a `retBytes`-byte `ScalarInt`
(default `4` bytes for `u32`) holding the count of trailing zero bits in `sc`.
Returns `.none` if `sc.sizeBytes == 0` or `retBytes == 0`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1734-L1773>

> "/// Returns the number of trailing unset bits (zeroes) in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn cttz<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def evalCttz (sc : ScalarInt) (retBytes : Nat := 4) : Option ScalarInt :=
  match Bool.or (Nat.beq sc.sizeBytes 0) (Nat.beq retBytes 0) with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    .some ⟨cttzLoop (Nat.mul sc.sizeBytes 8) ca, retBytes⟩

/--
Evaluate `core::intrinsics::cttz_nonzero(sc)`, returning `.none` (undefined
behavior) when `sc` is zero (`ca == 0`) or has zero byte width.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1775-L1795>

> "/// Like `cttz`, but extra-unsafe as it returns `undef` when
> /// given an `x` with value `0`.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn cttz_nonzero<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def evalCttzNonzero (sc : ScalarInt) (retBytes : Nat := 4) : Option ScalarInt :=
  match Bool.or (Nat.beq sc.sizeBytes 0) (Nat.beq retBytes 0) with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    match Nat.beq ca 0 with
    | true => .none
    | false => .some ⟨cttzLoop (Nat.mul sc.sizeBytes 8) ca, retBytes⟩

/--
Evaluate `core::intrinsics::ctpop(sc)`, returning a `retBytes`-byte `ScalarInt`
(default `4` bytes for `u32`) holding the population count of `sc`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1656-L1669>

> "/// Returns the number of bits set in an integer type `T`
> ...
> #[rustc_intrinsic]
> pub const fn ctpop<T: Copy>(x: T) -> u32;"
-/
@[reducible]
def evalCtpop (sc : ScalarInt) (retBytes : Nat := 4) : Option ScalarInt :=
  match Bool.or (Nat.beq sc.sizeBytes 0) (Nat.beq retBytes 0) with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    .some ⟨ctpopLoop (Nat.mul sc.sizeBytes 8) ca, retBytes⟩

/--
Evaluate `core::intrinsics::bswap(sc)`, reversing the byte order of `sc` while
preserving `sc.sizeBytes`. Returns `.none` if `sc.sizeBytes == 0`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1797-L1810>

> "/// Reverses the bytes in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn bswap<T: Copy>(x: T) -> T;"
-/
@[reducible]
def evalBswap (sc : ScalarInt) : Option ScalarInt :=
  match Nat.beq sc.sizeBytes 0 with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    .some ⟨bswapLoop sc.sizeBytes ca 0, sc.sizeBytes⟩

/--
Evaluate `core::intrinsics::bitreverse(sc)`, reversing the bit order of `sc`
across `8 * sc.sizeBytes` bits while preserving `sc.sizeBytes`. Returns `.none`
if `sc.sizeBytes == 0`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1812-L1825>

> "/// Reverses the bits in an integer type `T`.
> ...
> #[rustc_intrinsic]
> pub const fn bitreverse<T: Copy>(x: T) -> T;"
-/
@[reducible]
def evalBitreverse (sc : ScalarInt) : Option ScalarInt :=
  match Nat.beq sc.sizeBytes 0 with
  | true => .none
  | false =>
    let ca := wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)
    .some ⟨bitreverseLoop (Nat.mul sc.sizeBytes 8) ca 0, sc.sizeBytes⟩

/--
Evaluate `core::intrinsics::wrapping_add(lhs, rhs)` modulo
`2^(8 * lhs.sizeBytes)`. Returns `.none` if `lhs.sizeBytes == 0` or
`lhs.sizeBytes != rhs.sizeBytes`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2057-L2070>

> "/// Returns (a + b) mod 2<sup>N</sup>, where N is the width of T in bits.
> ...
> #[rustc_intrinsic]
> pub const fn wrapping_add<T: Copy>(a: T, b: T) -> T;"
-/
@[reducible]
def evalWrappingAdd (lhs rhs : ScalarInt) : Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    .some ⟨wrapScalarBits (Nat.add ca cb) modulus, sz⟩

/--
Evaluate `core::intrinsics::wrapping_sub(lhs, rhs)` modulo
`2^(8 * lhs.sizeBytes)`. Returns `.none` if `lhs.sizeBytes == 0` or
`lhs.sizeBytes != rhs.sizeBytes`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2071-L2084>

> "/// Returns (a - b) mod 2<sup>N</sup>, where N is the width of T in bits.
> ...
> #[rustc_intrinsic]
> pub const fn wrapping_sub<T: Copy>(a: T, b: T) -> T;"
-/
@[reducible]
def evalWrappingSub (lhs rhs : ScalarInt) : Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    let wrappedDiff :=
      match Nat.ble cb ca with
      | true => wrapScalarBits (Nat.sub ca cb) modulus
      | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
    .some ⟨wrappedDiff, sz⟩

/--
Evaluate `core::intrinsics::wrapping_mul(lhs, rhs)` modulo
`2^(8 * lhs.sizeBytes)`. Returns `.none` if `lhs.sizeBytes == 0` or
`lhs.sizeBytes != rhs.sizeBytes`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2085-L2098>

> "/// Returns (a * b) mod 2<sup>N</sup>, where N is the width of T in bits.
> ...
> #[rustc_intrinsic]
> pub const fn wrapping_mul<T: Copy>(a: T, b: T) -> T;"
-/
@[reducible]
def evalWrappingMul (lhs rhs : ScalarInt) : Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    .some ⟨wrapScalarBits (Nat.mul ca cb) modulus, sz⟩

/--
Evaluate `core::intrinsics::saturating_add(lhs, rhs)`, clamping on unsigned
overflow to `2^w - 1` (`isSigned = false`) and on signed two's-complement
overflow to `T::MIN = -2^(w-1)` or `T::MAX = 2^(w-1) - 1` (`isSigned = true`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2100-L2113>

> "/// Computes `a + b`, saturating at numeric bounds.
> ...
> #[rustc_intrinsic]
> pub const fn saturating_add<T: Copy>(a: T, b: T) -> T;"
-/
@[reducible]
def evalSaturatingAdd
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    let sum := Nat.add ca cb
    match isSigned with
    | false =>
      match Nat.ble modulus sum with
      | true => .some ⟨Nat.sub modulus 1, sz⟩
      | false => .some ⟨sum, sz⟩
    | true =>
      match signedOverflowAdd ca cb sz with
      | false => .some ⟨wrapScalarBits sum modulus, sz⟩
      | true =>
        let half := signedHalfModulus sz
        match isSignedNegative ca sz with
        | true => .some ⟨half, sz⟩
        | false => .some ⟨Nat.sub half 1, sz⟩

/--
Evaluate `core::intrinsics::saturating_sub(lhs, rhs)`, clamping on unsigned
underflow to `0` (`isSigned = false`) and on signed two's-complement overflow to
`T::MIN = -2^(w-1)` or `T::MAX = 2^(w-1) - 1` (`isSigned = true`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2114-L2127>

> "/// Computes `a - b`, saturating at numeric bounds.
> ...
> #[rustc_intrinsic]
> pub const fn saturating_sub<T: Copy>(a: T, b: T) -> T;"
-/
@[reducible]
def evalSaturatingSub
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    match isSigned with
    | false =>
      match Nat.ble cb ca with
      | true => .some ⟨Nat.sub ca cb, sz⟩
      | false => .some ⟨0, sz⟩
    | true =>
      match signedOverflowSub ca cb sz with
      | false =>
        .some ⟨wrapScalarBits (Nat.add ca (Nat.sub modulus cb)) modulus, sz⟩
      | true =>
        let half := signedHalfModulus sz
        match isSignedNegative ca sz with
        | true => .some ⟨half, sz⟩
        | false => .some ⟨Nat.sub half 1, sz⟩

/--
Evaluate `core::intrinsics::unchecked_add(lhs, rhs)`, returning `.none`
(undefined behavior) on unsigned or signed two's-complement overflow.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1983-L1991>

> "/// Returns the result of an unchecked addition, resulting in
> /// undefined behavior when `x + y > T::MAX` or `x + y < T::MIN`.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_add<T: Copy>(x: T, y: T) -> T;"
-/
@[reducible]
def evalUncheckedAdd
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    let sum := Nat.add ca cb
    match isSigned with
    | false =>
      match Nat.ble modulus sum with
      | true => .none
      | false => .some ⟨sum, sz⟩
    | true =>
      match signedOverflowAdd ca cb sz with
      | true => .none
      | false => .some ⟨wrapScalarBits sum modulus, sz⟩

/--
Evaluate `core::intrinsics::unchecked_sub(lhs, rhs)`, returning `.none`
(undefined behavior) on unsigned underflow or signed two's-complement overflow.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1993-L2001>

> "/// Returns the result of an unchecked subtraction, resulting in
> /// undefined behavior when `x - y > T::MAX` or `x - y < T::MIN`.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_sub<T: Copy>(x: T, y: T) -> T;"
-/
@[reducible]
def evalUncheckedSub
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    match isSigned with
    | false =>
      match Nat.ble cb ca with
      | true =>
        let diff := Nat.sub ca cb
        match Nat.ble modulus diff with
        | true => .none
        | false => .some ⟨diff, sz⟩
      | false => .none
    | true =>
      match signedOverflowSub ca cb sz with
      | true => .none
      | false =>
        let wrappedDiff :=
          match Nat.ble cb ca with
          | true => wrapScalarBits (Nat.sub ca cb) modulus
          | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
        .some ⟨wrappedDiff, sz⟩

/--
Evaluate `core::intrinsics::unchecked_mul(lhs, rhs)`, returning `.none`
(undefined behavior) on unsigned or signed two's-complement multiplication
overflow.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2003-L2011>

> "/// Returns the result of an unchecked multiplication, resulting in
> /// undefined behavior when `x * y > T::MAX` or `x * y < T::MIN`.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_mul<T: Copy>(x: T, y: T) -> T;"
-/
@[reducible]
def evalUncheckedMul
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    let prod := Nat.mul ca cb
    match isSigned with
    | false =>
      match Nat.ble modulus prod with
      | true => .none
      | false => .some ⟨prod, sz⟩
    | true =>
      match signedOverflowMul ca cb sz with
      | true => .none
      | false => .some ⟨wrapScalarBits prod modulus, sz⟩

/--
Evaluate `core::intrinsics::unchecked_div(lhs, rhs)`, returning `.none`
(undefined behavior) when `rhs == 0` or signed `lhs == T::MIN && rhs == -1`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1941-L1950>

> "/// Performs an unchecked division, resulting in undefined behavior
> /// where `y == 0` or `x == T::MIN && y == -1`
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_div<T: Copy>(x: T, y: T) -> T;"
-/
@[reducible]
def evalUncheckedDiv
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    match Nat.beq cb 0 with
    | true => .none
    | false =>
      match isSigned with
      | false => .some ⟨wrapScalarBits (Nat.div ca cb) modulus, sz⟩
      | true =>
        let numBits := Nat.mul sz 8
        let minSigned := scalarPow2 (Nat.sub numBits 1)
        let minusOne := Nat.sub modulus 1
        match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with
        | true => .none
        | false =>
          let negA := isSignedNegative ca sz
          let negB := isSignedNegative cb sz
          let magA := match negA with | false => ca | true => Nat.sub modulus ca
          let magB := match negB with | false => cb | true => Nat.sub modulus cb
          let magQ := Nat.div magA magB
          let quotBits :=
            match Nat.beq magQ 0 with
            | true => 0
            | false =>
              match negA, negB with
              | false, false => wrapScalarBits magQ modulus
              | true, true => wrapScalarBits magQ modulus
              | _, _ => wrapScalarBits (Nat.sub modulus magQ) modulus
          .some ⟨quotBits, sz⟩

/--
Evaluate `core::intrinsics::unchecked_rem(lhs, rhs)`, returning `.none`
(undefined behavior) when `rhs == 0` or signed `lhs == T::MIN && rhs == -1`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1951-L1960>

> "/// Returns the remainder of an unchecked division, resulting in
> /// undefined behavior when `y == 0` or `x == T::MIN && y == -1`
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_rem<T: Copy>(x: T, y: T) -> T;"
-/
@[reducible]
def evalUncheckedRem
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    match Nat.beq cb 0 with
    | true => .none
    | false =>
      match isSigned with
      | false => .some ⟨wrapScalarBits (Nat.mod ca cb) modulus, sz⟩
      | true =>
        let numBits := Nat.mul sz 8
        let minSigned := scalarPow2 (Nat.sub numBits 1)
        let minusOne := Nat.sub modulus 1
        match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with
        | true => .none
        | false =>
          let negA := isSignedNegative ca sz
          let negB := isSignedNegative cb sz
          let magA := match negA with | false => ca | true => Nat.sub modulus ca
          let magB := match negB with | false => cb | true => Nat.sub modulus cb
          let magR := Nat.mod magA magB
          let remBits :=
            match Nat.beq magR 0 with
            | true => 0
            | false =>
              match negA with
              | false => wrapScalarBits magR modulus
              | true => wrapScalarBits (Nat.sub modulus magR) modulus
          .some ⟨remBits, sz⟩

/--
Evaluate `core::intrinsics::unchecked_shl(lhs, rhs)`, returning `.none`
(undefined behavior) if `rhs` is signed and negative or if `rhs >= 8 *
lhs.sizeBytes`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1962-L1971>

> "/// Performs an unchecked left shift, resulting in undefined behavior when
> /// `y < 0` or `y >= N`, where N is the width of T in bits.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T;"
-/
@[reducible]
def evalUncheckedShl
    (lhs rhs : ScalarInt)
    (rhsIsSigned : Bool := false) :
    Option ScalarInt :=
  match Bool.or (Nat.beq lhs.sizeBytes 0) (Nat.beq rhs.sizeBytes 0) with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let numBits := Nat.mul sz 8
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits (scalarModulus rhs.sizeBytes)
    let negShift := Bool.and rhsIsSigned (isSignedNegative cb rhs.sizeBytes)
    match Bool.or negShift (Nat.ble numBits cb) with
    | true => .none
    | false => .some ⟨shiftLeftBits ca cb modulus, sz⟩

/--
Evaluate `core::intrinsics::unchecked_shr(lhs, rhs)`, returning `.none`
(undefined behavior) if `rhs` is signed and negative or if `rhs >= 8 *
lhs.sizeBytes`. Performs logical right shift when `lhsIsSigned = false` and
arithmetic sign-extending right shift when `lhsIsSigned = true`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1972-L1981>

> "/// Performs an unchecked right shift, resulting in undefined behavior when
> /// `y < 0` or `y >= N`, where N is the width of T in bits.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn unchecked_shr<T: Copy, U: Copy>(x: T, y: U) -> T;"
-/
@[reducible]
def evalUncheckedShr
    (lhs rhs : ScalarInt)
    (lhsIsSigned : Bool := false)
    (rhsIsSigned : Bool := false) :
    Option ScalarInt :=
  match Bool.or (Nat.beq lhs.sizeBytes 0) (Nat.beq rhs.sizeBytes 0) with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let numBits := Nat.mul sz 8
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits (scalarModulus rhs.sizeBytes)
    let negShift := Bool.and rhsIsSigned (isSignedNegative cb rhs.sizeBytes)
    match Bool.or negShift (Nat.ble numBits cb) with
    | true => .none
    | false =>
      let shifted :=
        match lhsIsSigned with
        | false => wrapScalarBits (shiftRightUnsignedBits ca cb) modulus
        | true => arithmeticShrBits ca sz cb
      .some ⟨shifted, sz⟩

/--
Evaluate `core::intrinsics::three_way_compare(lhs, rhs)`, returning a 1-byte
`Ordering` scalar: `⟨255, 1⟩` (`-1i8`, `Ordering::Less`) when `lhs < rhs`,
`⟨0, 1⟩` (`0i8`, `Ordering::Equal`) when `lhs == rhs`, and `⟨1, 1⟩` (`1i8`,
`Ordering::Greater`) when `lhs > rhs`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1827-L1837>

> "/// Does a three-way comparison between the two arguments,
> /// which must be of character or integer (signed or unsigned) type.
> ...
> #[rustc_intrinsic]
> pub const fn three_way_compare<T: Copy>(lhs: T, rhss: T) ->
>     crate::cmp::Ordering;"
-/
@[reducible]
def evalThreeWayCompare
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.or
      (Nat.beq lhs.sizeBytes 0)
      (Bool.not (Nat.beq lhs.sizeBytes rhs.sizeBytes))
  with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let modulus := scalarModulus sz
    let ca := wrapScalarBits lhs.bits modulus
    let cb := wrapScalarBits rhs.bits modulus
    match Nat.beq ca cb with
    | true => .some ⟨0, 1⟩
    | false =>
      let isLt :=
        match isSigned with
        | false => Nat.ble ca cb
        | true => signedLt ca cb sz
      match isLt with
      | true => .some ⟨255, 1⟩
      | false => .some ⟨1, 1⟩

/--
Evaluate `core::intrinsics::arith_offset(dst, offset)` on a 64-bit pointer
`ptrVal` (`ptrSizeBytes == 8`) and signed 64-bit `isize` `offsetSc`
(`offsetSc.sizeBytes == 8`) with pointee byte stride `elemStride`, preserving
`ptrVal.allocId` provenance and wrapping `offsetBytes` modulo `2^64`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L899-L916>

> "/// Calculates the offset from a pointer, potentially wrapping.
> ///
> /// This is implemented as an intrinsic to avoid converting to and from an
> /// integer, since the conversion inhibits certain optimizations.
> ...
> #[rustc_intrinsic]
> pub const unsafe fn arith_offset<T>(dst: *const T, offset: isize) -> *const T;"
-/
@[reducible]
def evalArithOffset
    (ptrVal : ProvenancePtr)
    (ptrSizeBytes : Nat)
    (offsetSc : ScalarInt)
    (elemStride : Nat) :
    Option ProvenancePtr :=
  match
    Bool.and
      (Nat.beq ptrSizeBytes 8)
      (Nat.beq offsetSc.sizeBytes 8)
  with
  | false => .none
  | true =>
    let modulus := scalarModulus 8
    let offsetBits := wrapScalarBits offsetSc.bits modulus
    let newOffset :=
      match isSignedNegative offsetBits 8 with
      | false =>
        wrapScalarBits
          (Nat.add ptrVal.offsetBytes (Nat.mul offsetBits elemStride))
          modulus
      | true =>
        let mag := Nat.sub modulus offsetBits
        let byteDelta := wrapScalarBits (Nat.mul mag elemStride) modulus
        wrapScalarBits
          (Nat.add ptrVal.offsetBytes (Nat.sub modulus byteDelta))
          modulus
    .some { ptrVal with offsetBytes := newOffset }

/--
Compute the dynamic byte size `elemSizeBytes * len` of a slice `[T]` or `str`
for `core::intrinsics::size_of_val` from its 8-byte fat-pointer length metadata
`lenSc`, returning `.none` (undefined behavior) if `lenSc.sizeBytes != 8` or if
`elemSizeBytes * len` exceeds `isize::MAX` (`>= 2^63 = signedHalfModulus 8`).

`core::intrinsics::align_of_val` performs the same check before returning the
element alignment: `align_of_val_raw` has the same safety conditions as
`size_of_val_raw`, and the CTFE interpreter computes both results with one
function that rejects a slice larger than `isize::MAX` bytes.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2850-L2861>

> "/// The size of the referenced value in bytes.
> ...
> #[rustc_intrinsic]
> #[rustc_intrinsic_const_stable_indirect]
> pub const unsafe fn size_of_val<T: ?Sized>(ptr: *const T) -> usize;"

Reference (`library/core/src/mem/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/mem/mod.rs#L560-L579>

> "/// This function is only safe to call if the following conditions hold:
> ///
> /// - If `T` is `Sized`, this function is always safe to call.
> /// - If the unsized tail of `T` is:
> ///     - a [slice], then the length of the slice tail must be an initialized
> ///       integer, and the size of the *entire value*
> ///       (dynamic tail length + statically sized prefix) must fit in `isize`."
-/
@[reducible]
def evalSliceSizeOfVal
    (elemSizeBytes : Nat)
    (lenSc : ScalarInt) :
    Option ScalarInt :=
  match Nat.beq lenSc.sizeBytes 8 with
  | false => .none
  | true =>
    let modulus := scalarModulus 8
    let len := wrapScalarBits lenSc.bits modulus
    let totalBytes := Nat.mul elemSizeBytes len
    match Nat.ble (signedHalfModulus 8) totalBytes with
    | true => .none
    | false => .some ⟨totalBytes, 8⟩

/-!
## Pure IEEE-754 `binary32` / `binary64` numeric casts

`CastKind.floatToInt`, `CastKind.intToFloat`, and `CastKind.floatToFloat` on
`f32` / `f64` operate on raw bit patterns (`ScalarInt.bits`) with exact
rational decoding (`decodeBits`) and correctly rounded `roundTiesToEven`
re-encoding (`roundRatioTiesToEven`). Every definition below is a structural or
`Decidable`-instance computation over `Nat` / `Int` (no host `Float`, no
`extern`, no `Classical.choice`), so concrete casts reduce in the Lean kernel.

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from a float to an integer will round the float towards zero
> - NaN will return 0
> - Values larger than the maximum integer value, including INFINITY, will
>   saturate to the maximum value of the integer type.
> - Values smaller than the minimum integer value, including NEG_INFINITY, will
>   saturate to the minimum value of the integer type."
>
> "Casting from an integer to float will produce the closest possible float *
> - if necessary, rounding is according to roundTiesToEven mode ***
> - on overflow, infinity (of the same sign as the input) is produced"
>
> "Casting from an f32 to an f64 is perfect and lossless"
>
> "Casting from an f64 to an f32 will produce the closest possible f32 **
> - if necessary, rounding is according to roundTiesToEven mode ***
> - on overflow, infinity (of the same sign as the input) is produced"
>
> "*** as defined in IEEE 754-2008 §4.3.1: pick the nearest floating point
> number, preferring the one with an even least significant digit if exactly
> halfway between two floating point numbers."

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "The following rules apply when a NaN value is returned from an arithmetic
> operation:
> - The result has a non-deterministic sign.
> - The quiet bit and payload are non-deterministically chosen from the
>   following set of options:
>   - Preferred NaN: The quiet bit is set and the payload is all-zero.
>   - Quieting NaN propagation: The quiet bit is set and the payload is copied
>     from any input operand that is a NaN. If the inputs and outputs do not
>     have the same payload size (i.e., for as casts), then
>     - If the output is smaller than the input, low-order bits of the payload
>       get dropped.
>     - If the output is larger than the input, the payload gets filled up with
>       0s in the low-order bits."

Modeling choice: Rust leaves the sign, quiet bit, and payload of a NaN result
non-deterministic. `evalFloatToFloatRoundTiesToEven` deterministically picks
one admissible option, "Quieting NaN propagation" with the input's sign (the
`rustc_apfloat` / Miri `convert` rule), so a proof about this model covers that
choice only, not every NaN bit pattern Rust permits.
-/

/--
The IEEE-754 interchange formats of Rust's `f32` (`binary32`) and `f64`
(`binary64`).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."
-/
inductive IeeeFormat : Type where
  /-- IEEE-754 `binary32` (Rust `f32`). -/
  | binary32 : IeeeFormat
  /-- IEEE-754 `binary64` (Rust `f64`). -/
  | binary64 : IeeeFormat
deriving DecidableEq

namespace IeeeFormat

/-- Total bit width (`32` / `64`). -/
def width : IeeeFormat → Nat
  | .binary32 => 32
  | .binary64 => 64

/-- Exponent field width (`8` / `11`). -/
def exponentBits : IeeeFormat → Nat
  | .binary32 => 8
  | .binary64 => 11

/-- Trailing significand (fraction) field width (`23` / `52`). -/
def fractionBits : IeeeFormat → Nat
  | .binary32 => 23
  | .binary64 => 52

/-- Exponent bias (`127` / `1023`). -/
def bias : IeeeFormat → Nat
  | .binary32 => 127
  | .binary64 => 1023

/-- Byte width of the corresponding Rust scalar (`4` / `8`). -/
def byteWidth : IeeeFormat → Nat
  | .binary32 => 4
  | .binary64 => 8

/-- Minimum normal unbiased exponent (`1 - bias`). -/
def minExponent (f : IeeeFormat) : Int := 1 - (f.bias : Int)

/-- Maximum finite unbiased exponent (`bias`). -/
def maxExponent (f : IeeeFormat) : Int := (f.bias : Int)

end IeeeFormat

/-- IEEE-754 `binary32` bit pattern (Rust `f32::to_bits`). -/
abbrev F32Bits : Type := BitVec 32

/-- IEEE-754 `binary64` bit pattern (Rust `f64::to_bits`). -/
abbrev F64Bits : Type := BitVec 64

/-- Raw sign / biased-exponent / fraction fields of an IEEE-754 bit pattern. -/
structure FloatComponents : Type where
  /-- Sign bit. -/
  neg : Bool
  /-- Biased exponent field. -/
  exponent : Nat
  /-- Trailing significand field. -/
  fraction : Nat
deriving DecidableEq

/-- Split a bit pattern into its sign, biased exponent, and fraction fields. -/
def unpackBits (f : IeeeFormat) (bits : Nat) : FloatComponents :=
  { neg := Nat.beq ((bits / 2 ^ (f.width - 1)) % 2) 1
    exponent := (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits
    fraction := bits % 2 ^ f.fractionBits }

/-- Exact classification of an IEEE-754 bit pattern. Finite nonzero values carry
the exact rational magnitude `num / den` (`den` a power of two). -/
inductive FloatKind : Type where
  /-- Signed zero. -/
  | zero (neg : Bool) : FloatKind
  /-- Finite nonzero value `(-1)^neg * num / den`. -/
  | finite (neg : Bool) (num den : Nat) : FloatKind
  /-- Signed infinity. -/
  | inf (neg : Bool) : FloatKind
  /-- NaN with sign, quiet bit, and full fraction payload. -/
  | nan (neg : Bool) (quiet : Bool) (payload : Nat) : FloatKind
deriving DecidableEq

/-- Scale the rational `n / d` by `2 ^ e`. -/
def powScale (n d : Nat) : Int → Nat × Nat
  | .ofNat k => (n * 2 ^ k, d)
  | .negSucc k => (n, d * 2 ^ (k + 1))

/--
Exact decoding of an IEEE-754 bit pattern: all-ones exponent fields are
infinities (zero fraction) and NaNs (quiet bit = most significant fraction
bit); zero exponent fields are signed zeros and subnormals
`fraction * 2^(minExponent - fractionBits)`; every other exponent field is the
normal value `(2^fractionBits + fraction) * 2^(exponent - bias - fractionBits)`.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."
-/
def decodeBits (f : IeeeFormat) (bits : Nat) : FloatKind :=
  let c := unpackBits f bits
  if c.exponent = 2 ^ f.exponentBits - 1 then
    if c.fraction = 0 then .inf c.neg
    else .nan c.neg (Nat.beq ((c.fraction / 2 ^ (f.fractionBits - 1)) % 2) 1) c.fraction
  else if c.exponent = 0 then
    if c.fraction = 0 then .zero c.neg
    else
      let nd := powScale c.fraction 1 (f.minExponent - (f.fractionBits : Int))
      .finite c.neg nd.1 nd.2
  else
    let nd := powScale (2 ^ f.fractionBits + c.fraction) 1
      ((c.exponent : Int) - (f.bias : Int) - (f.fractionBits : Int))
    .finite c.neg nd.1 nd.2

/--
Nearest integer to `n / d`, ties to even (IEEE 754-2008 `roundTiesToEven` on
the integer quotient).

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "*** as defined in IEEE 754-2008 §4.3.1: pick the nearest floating point
> number, preferring the one with an even least significant digit if exactly
> halfway between two floating point numbers."
-/
def roundQuotientTiesToEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if r * 2 > d ∨ (r * 2 = d ∧ q % 2 = 1) then q + 1 else q

/-- `floor (log2 (n / d))` for nonzero `n`, `d`. -/
def ratioExponent (n d : Nat) : Int :=
  if d ≤ n then ((n / d).log2 : Int)
  else
    let k := (d / n).log2
    if d ≤ n * 2 ^ k then -(k : Int) else -((k : Int) + 1)

/-- Bit pattern of a signed zero. -/
def zeroBits (f : IeeeFormat) (neg : Bool) : Nat := if neg then 2 ^ (f.width - 1) else 0

/-- Bit pattern with the given sign, biased exponent, and fraction. -/
def encodeBits (f : IeeeFormat) (neg : Bool) (exponent fraction : Nat) : Nat :=
  zeroBits f neg + exponent * 2 ^ f.fractionBits + fraction

/-- Bit pattern of a signed infinity. -/
def infBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg (2 ^ f.exponentBits - 1) 0

/-- Bit pattern of the preferred (canonical positive quiet) NaN. -/
def preferredNaNBits (f : IeeeFormat) : Nat :=
  encodeBits f false (2 ^ f.exponentBits - 1) (2 ^ (f.fractionBits - 1))

/--
Correctly rounded (`roundTiesToEven`) encoding of the exact rational
`(-1)^neg * n / d` in format `f`: gradual underflow comes from clamping the
working exponent to `minExponent` (subnormals), a rounding carry-out bumps the
exponent, and overflow produces the infinity of the same sign. A zero
magnitude yields the zero of sign `neg`. The `preferredNaNBits` branches
(`d = 0`, or a significand outside the normal or subnormal range after
rounding) are unreachable from decoded finite inputs and integer inputs.

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from an integer to float will produce the closest possible float *
> - if necessary, rounding is according to roundTiesToEven mode ***
> - on overflow, infinity (of the same sign as the input) is produced"
>
> "*** as defined in IEEE 754-2008 §4.3.1: pick the nearest floating point
> number, preferring the one with an even least significant digit if exactly
> halfway between two floating point numbers."
-/
def roundRatioTiesToEven (f : IeeeFormat) (neg : Bool) (n d : Nat) : Nat :=
  if d = 0 then preferredNaNBits f
  else if n = 0 then zeroBits f neg
  else
    let exponent := max (ratioExponent n d) f.minExponent
    if exponent > f.maxExponent then infBits f neg
    else
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let significand := roundQuotientTiesToEven scaled.1 scaled.2
      let carry := decide (2 ^ (f.fractionBits + 1) ≤ significand)
      let significand' := if carry then significand / 2 else significand
      let exponent' := if carry then exponent + 1 else exponent
      if exponent' > f.maxExponent then infBits f neg
      else if significand' < 2 ^ f.fractionBits then
        if exponent' = f.minExponent then encodeBits f neg 0 significand'
        else preferredNaNBits f
      else if 2 ^ (f.fractionBits + 1) ≤ significand' then preferredNaNBits f
      else encodeBits f neg (exponent' + (f.bias : Int)).toNat (significand' - 2 ^ f.fractionBits)

/-- Target integer type of a `CastKind.floatToInt` cast. -/
inductive FloatIntTarget : Type where
  /-- Signed integer target. -/
  | signed (w : IntTy) : FloatIntTarget
  /-- Unsigned integer target. -/
  | unsigned (w : UintTy) : FloatIntTarget

/-- Target pointer width (the width of `isize` / `usize`). -/
inductive FloatPtrWidth : Type where
  /-- 32-bit targets. -/
  | bits32 : FloatPtrWidth
  /-- 64-bit targets. -/
  | bits64 : FloatPtrWidth

/-- Pointer width in bits. -/
def FloatPtrWidth.bits : FloatPtrWidth → Nat
  | .bits32 => 32
  | .bits64 => 64

/-- Bit width of an integer target. -/
def FloatIntTarget.bitWidth (pw : FloatPtrWidth) : FloatIntTarget → Nat
  | .signed w => w.bitWidth pw.bits
  | .unsigned w => w.bitWidth pw.bits

/-- Signedness of an integer target. -/
def FloatIntTarget.isSigned : FloatIntTarget → Bool
  | .signed _ => true
  | .unsigned _ => false

/--
Minimum representable value (`-(2^(w-1))` signed, `0` unsigned).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The signed two's complement integer types consist of: ... i8 -(2^7) 2^7-1"
-/
def FloatIntTarget.minValue (pw : FloatPtrWidth) (t : FloatIntTarget) : Int :=
  if t.isSigned then -((2 ^ (t.bitWidth pw - 1) : Nat) : Int) else 0

/--
Maximum representable value (`2^(w-1) - 1` signed, `2^w - 1` unsigned).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The unsigned integer types consist of: ... u8 0 2^8-1"
-/
def FloatIntTarget.maxValue (pw : FloatPtrWidth) (t : FloatIntTarget) : Int :=
  if t.isSigned then ((2 ^ (t.bitWidth pw - 1) : Nat) : Int) - 1
  else ((2 ^ t.bitWidth pw : Nat) : Int) - 1

/-- Clamp `v` into `[lo, hi]`. -/
def clampInt (lo hi v : Int) : Int := max lo (min hi v)

/-- Truncation toward zero of `(-1)^neg * n / d`. -/
def truncRatio (neg : Bool) (n d : Nat) : Int :=
  if neg then -((n / d : Nat) : Int) else ((n / d : Nat) : Int)

/--
Mathematical result of a Rust saturating float-to-int `as` cast: NaN ↦ `0`,
`±∞` ↦ the maximum / minimum, and finite values truncate toward zero and clamp
into `[lo, hi]`.

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from a float to an integer will round the float towards zero
> - NaN will return 0
> - Values larger than the maximum integer value, including INFINITY, will
>   saturate to the maximum value of the integer type.
> - Values smaller than the minimum integer value, including NEG_INFINITY, will
>   saturate to the minimum value of the integer type."
-/
def floatToIntValue (k : FloatKind) (lo hi : Int) : Int :=
  match k with
  | .nan _ _ _ => 0
  | .inf neg => if neg then lo else hi
  | .zero _ => 0
  | .finite neg n d => clampInt lo hi (truncRatio neg n d)

/-- Canonical two's-complement encoding of `v` at width `w`. -/
def encodeTwosComplement (w : Nat) (v : Int) : Nat :=
  (v % ((2 ^ w : Nat) : Int)).toNat

/--
Rust `as` float-to-int cast (`CastKind.floatToInt`) on a raw `src`-format bit
pattern, returning a canonical two's-complement `ScalarInt` of the target
width (`floatToIntValue`).

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from a float to an integer will round the float towards zero"
-/
def evalFloatToIntSaturating (src : IeeeFormat) (bits : Nat) (target : FloatIntTarget)
    (pw : FloatPtrWidth) : ScalarInt :=
  let w := target.bitWidth pw
  ⟨encodeTwosComplement w
      (floatToIntValue (decodeBits src bits) (target.minValue pw) (target.maxValue pw)),
    w / 8⟩

/-- Integer value of a `w`-bit two's-complement (signed) or unsigned bit pattern. -/
def intValueOfBits (signed : Bool) (w bits : Nat) : Int :=
  let b := bits % 2 ^ w
  if signed = true ∧ 2 ^ (w - 1) ≤ b then (b : Int) - ((2 ^ w : Nat) : Int) else (b : Int)

/--
Rust `as` int-to-float cast (`CastKind.intToFloat`): the closest `dst` float to
the source integer, rounding with `roundTiesToEven` and overflowing to the
infinity of the source's sign (`roundRatioTiesToEven`).

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from an integer to float will produce the closest possible float *
> - if necessary, rounding is according to roundTiesToEven mode ***
> - on overflow, infinity (of the same sign as the input) is produced"
-/
def evalIntToFloatRoundTiesToEven (signed : Bool) (w bits : Nat) (dst : IeeeFormat) : Nat :=
  let v := intValueOfBits signed w bits
  roundRatioTiesToEven dst (decide (v < 0)) v.natAbs 1

/--
Rust `as` float-to-float cast (`CastKind.floatToFloat`) on a raw `src`-format
bit pattern: signed zeros and infinities map to the same-signed zero and
infinity, finite values are correctly rounded with `roundTiesToEven`
(`roundRatioTiesToEven`; exact for `f32 → f64`), and a NaN keeps its sign while
its payload is quieted and shifted to the `dst` precision ("Quieting NaN
propagation": low-order payload bits are dropped when narrowing and filled with
zeros when widening) with the `dst` quiet bit set.

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting from an f32 to an f64 is perfect and lossless"
>
> "Casting from an f64 to an f32 will produce the closest possible f32 **
> - if necessary, rounding is according to roundTiesToEven mode ***
> - on overflow, infinity (of the same sign as the input) is produced"

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "Quieting NaN propagation: The quiet bit is set and the payload is copied from
> any input operand that is a NaN. If the inputs and outputs do not have the
> same payload size (i.e., for as casts), then
> - If the output is smaller than the input, low-order bits of the payload get
>   dropped.
> - If the output is larger than the input, the payload gets filled up with 0s
>   in the low-order bits."

Modeling choice: the NaN result is one deterministic admissible choice among
the non-deterministic NaN bit patterns Rust permits (see the section comment).
-/
def evalFloatToFloatRoundTiesToEven (src dst : IeeeFormat) (bits : Nat) : Nat :=
  match decodeBits src bits with
  | .zero neg => zeroBits dst neg
  | .finite neg n d => roundRatioTiesToEven dst neg n d
  | .inf neg => infBits dst neg
  | .nan neg _ payload =>
    let quiet := Nat.lor payload (2 ^ (src.fractionBits - 1))
    let payload' :=
      if src.fractionBits ≤ dst.fractionBits then
        quiet * 2 ^ (dst.fractionBits - src.fractionBits)
      else quiet / 2 ^ (src.fractionBits - dst.fractionBits)
    encodeBits dst neg (2 ^ dst.exponentBits - 1) (Nat.lor payload' (2 ^ (dst.fractionBits - 1)))

/-!
## Pure IEEE-754 `binary32` / `binary64` arithmetic, comparisons, negation, and NaN relations

Every definition below computes over exact bit patterns (`Nat`) and exact
rationals (`Int` / `Nat`) with zero host `Float`, zero `extern`, and zero
`Classical.choice`. Finite binary operations (`add`, `sub`, `mul`, `div`, `rem`)
round once with IEEE 754-2008 `roundTiesToEven` (`roundRatioTiesToEven`),
matching Rust 1.98.0 and pinned `rustc_apfloat` / Miri `FloatBits`.
-/

/--
`true` iff `bits` decodes to a NaN in IEEE-754 format `f` (all-ones biased
exponent and nonzero fraction field).

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."
-/
def isNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ _ _ => true
  | _ => false

/--
`true` iff `bits` decodes to a quiet NaN (QNaN: NaN with quiet bit `1`) in
IEEE-754 format `f`.

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "a quiet/signaling bit. Rust assumes that the quiet/signaling bit being set to
> 1 indicates a quiet NaN (QNaN), and a value of 0 indicates a signaling NaN
> (SNaN)."
-/
def isQuietNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ quiet _ => quiet
  | _ => false

/--
`true` iff `bits` decodes to a signaling NaN (SNaN: NaN with quiet bit `0` and
nonzero lower payload) in IEEE-754 format `f`.

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "a quiet/signaling bit. Rust assumes that the quiet/signaling bit being set to
> 1 indicates a quiet NaN (QNaN), and a value of 0 indicates a signaling NaN
> (SNaN)."
-/
def isSignalingNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ quiet _ => Bool.not quiet
  | _ => false

/--
Bitwise IEEE-754 unary negation (`UnOp.neg` on `f32` / `f64`): flips the sign
bit of the canonical `f.width`-bit pattern while preserving the exponent,
quiet/signaling bit, and full NaN payload verbatim.

Reference (The Rust Reference, "Negation operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#negation-operators>

> "* Negation `-`: Signed integer, Floating-point (`std::ops::Neg`)"

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "The rules for NaN values differ between arithmetic and non-arithmetic (or
> “bitwise”) operations. The non-arithmetic operations are unary -, abs,
> copysign, signum, {to,from}_bits, {to,from}_{be,le,ne}_bytes and
> is_sign_{positive,negative}. These operations are guaranteed to exactly
> preserve the bit pattern of their input except for possibly changing the sign
> bit."
-/
def evalFloatNeg (f : IeeeFormat) (bits : Nat) : Nat :=
  let b := bits % 2 ^ f.width
  let sign := 2 ^ (f.width - 1)
  if sign ≤ b then b - sign else b + sign

/--
Bitwise IEEE-754 absolute value (`f32::abs` / `f64::abs`): clears the sign bit
while preserving the exponent, quiet/signaling bit, and full NaN payload
verbatim.

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "The non-arithmetic operations are unary -, abs, copysign, signum,
> {to,from}_bits, {to,from}_{be,le,ne}_bytes and is_sign_{positive,negative}.
> These operations are guaranteed to exactly preserve the bit pattern of their
> input except for possibly changing the sign bit."
-/
def evalFloatAbs (f : IeeeFormat) (bits : Nat) : Nat :=
  bits % 2 ^ (f.width - 1)

/-- Signed integer numerator `(-1)^neg * n` for exact rational arithmetic. -/
def signedNum (neg : Bool) (n : Nat) : Int :=
  if neg then -((n : Int)) else (n : Int)

/--
IEEE-754 partial ordering of two `f`-format bit patterns: any NaN operand yields
`.none` (unordered); `-0.0` and `+0.0` compare `.some .eq`; signed infinities
compare below/above all finite values; finite rationals compare by exact cross
multiplication.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."

Reference (The Rust Reference, "Comparison operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#comparison-operators>

> "Comparison operators are defined for primitive integer, floating-point, bool,
> and char types, as well as for pointers and function pointers."
-/
def evalFloatPartialCompare (f : IeeeFormat) (lhsBits rhsBits : Nat) : Option Ordering :=
  let l := decodeBits f (lhsBits % 2 ^ f.width)
  let r := decodeBits f (rhsBits % 2 ^ f.width)
  match l, r with
  | .nan _ _ _, _ | _, .nan _ _ _ => .none
  | .inf ln, .inf rn =>
    .some
      (match ln, rn with
       | true, true => .eq
       | false, false => .eq
       | true, false => .lt
       | false, true => .gt)
  | .inf ln, _ => .some (if ln then .lt else .gt)
  | _, .inf rn => .some (if rn then .gt else .lt)
  | .zero _, .zero _ => .some .eq
  | .zero _, .finite rn rnum _ =>
    .some (if rnum = 0 then .eq else if rn then .gt else .lt)
  | .finite ln lnum _, .zero _ =>
    .some (if lnum = 0 then .eq else if ln then .lt else .gt)
  | .finite ln lnum lden, .finite rn rnum rden =>
    let lv := signedNum ln lnum * (rden : Int)
    let rv := signedNum rn rnum * (lden : Int)
    .some (if lv < rv then .lt else if lv = rv then .eq else .gt)

/--
IEEE-754 boolean comparisons (`==`, `!=`, `<`, `<=`, `>`, `>=`) on `f32` / `f64`
bit patterns derived from `evalFloatPartialCompare`. Returns `.none` for
non-comparison `BinOp`s (and for `BinOp.cmp`, which MIR does not emit for
floating-point types because `f32`/`f64` do not implement `Ord`). When either
operand is NaN, `.ne` yields `.some true` and every other comparison yields
`.some false`.

Reference (The Rust Reference, "Comparison operators"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#comparison-operators>

> "Comparison operators are defined for primitive integer, floating-point, bool,
> and char types, as well as for pointers and function pointers."
-/
def evalFloatCmp (op : BinOp) (f : IeeeFormat) (lhsBits rhsBits : Nat) : Option Bool :=
  let order := evalFloatPartialCompare f lhsBits rhsBits
  match op with
  | .eq => .some (match order with | .some .eq => true | _ => false)
  | .ne => .some (match order with | .some .eq => false | _ => true)
  | .lt => .some (match order with | .some .lt => true | _ => false)
  | .le => .some (match order with | .some .lt => true | .some .eq => true | _ => false)
  | .gt => .some (match order with | .some .gt => true | _ => false)
  | .ge => .some (match order with | .some .gt => true | .some .eq => true | _ => false)
  | _ => .none

/-- Flip the sign bit of a decoded `FloatKind` (used for `sub x y = add x (-y)`). -/
def negateFloatKind : FloatKind → FloatKind
  | .zero neg => .zero (Bool.not neg)
  | .finite neg n d => .finite (Bool.not neg) n d
  | .inf neg => .inf (Bool.not neg)
  | .nan neg q p => .nan (Bool.not neg) q p

/--
Exact IEEE-754 addition of two decoded values in format `f` under
`roundTiesToEven` (IEEE 754-2008 §6.3 signed-zero rule: `-0.0 + -0.0 = -0.0`,
and exact cancellation of opposite-sign nonzero operands yields `+0.0`).
Non-finite NaN outcomes return the deterministic `preferredNaNBits f`; full
nondeterministic NaN admissibility is modeled by `nanChoices` and
`EvalFloatBinOpRel`.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."

Reference (The Rust Reference, "Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "*** as defined in IEEE 754-2008 §4.3.1: pick the nearest floating point
> number, preferring the one with an even least significant digit if exactly
> halfway between two floating point numbers."
-/
def exactSumFloat (f : IeeeFormat) (lhs rhs : FloatKind) : Nat :=
  match lhs, rhs with
  | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
  | .inf ln, .inf rn =>
    if Bool.xor ln rn then preferredNaNBits f else infBits f ln
  | .inf ln, _ => infBits f ln
  | _, .inf rn => infBits f rn
  | .zero ln, .zero rn => zeroBits f (Bool.and ln rn)
  | .zero ln, .finite rn rnum rden =>
    let sign := if rnum = 0 then Bool.and ln rn else rn
    roundRatioTiesToEven f sign rnum rden
  | .finite ln lnum lden, .zero rn =>
    let sign := if lnum = 0 then Bool.and ln rn else ln
    roundRatioTiesToEven f sign lnum lden
  | .finite ln lnum lden, .finite rn rnum rden =>
    let n : Int := signedNum ln lnum * (rden : Int) + signedNum rn rnum * (lden : Int)
    let sign : Bool :=
      if n = 0 then Bool.and (Nat.beq lnum 0) (Bool.and (Nat.beq rnum 0) (Bool.and ln rn))
      else decide (n < 0)
    roundRatioTiesToEven f sign n.natAbs (lden * rden)

/--
Deterministic base result of IEEE-754 binary arithmetic (`add`, `sub`, `mul`,
`div`, `rem`) on `f32` / `f64` bit patterns under `roundTiesToEven`, matching
`Miri.Interpreter.FloatBits.arithmetic`. Returns `.none` for non-arithmetic
`BinOp`s.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1650>

> "pub enum BinOp {
>     /// The `+` operator (addition)
>     Add,
>     ...
>     /// The `-` operator (subtraction)
>     Sub,
>     ...
>     /// The `*` operator (multiplication)
>     Mul,
>     ...
>     /// The `/` operator (division)
>     Div,
>     /// The `%` operator (modulus)
>     Rem,"

Modeling choice: whenever an arithmetic operation produces a NaN,
`evalFloatArithBase` deterministically returns `preferredNaNBits f`. Rust leaves
the sign, quiet bit, and payload of an arithmetic NaN non-deterministic; the
relational specification `EvalFloatBinOpRel` with `.nondeterministic` captures
the admissible NaN choices (`nanChoices`).
-/
def evalFloatArithBase (op : BinOp) (f : IeeeFormat) (lhsBits rhsBits : Nat) : Option Nat :=
  let lb := lhsBits % 2 ^ f.width
  let rb := rhsBits % 2 ^ f.width
  let l := decodeBits f lb
  let r := decodeBits f rb
  match op with
  | .add => .some (exactSumFloat f l r)
  | .sub => .some (exactSumFloat f l (negateFloatKind r))
  | .mul =>
    .some
      (match l, r with
       | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
       | .inf _, .zero _ | .zero _, .inf _ => preferredNaNBits f
       | .inf ln, .finite rn rnum _ =>
         if rnum = 0 then preferredNaNBits f else infBits f (Bool.xor ln rn)
       | .finite ln lnum _, .inf rn =>
         if lnum = 0 then preferredNaNBits f else infBits f (Bool.xor ln rn)
       | .inf ln, .inf rn => infBits f (Bool.xor ln rn)
       | .zero ln, .zero rn => zeroBits f (Bool.xor ln rn)
       | .zero ln, .finite rn _ _ => zeroBits f (Bool.xor ln rn)
       | .finite ln _ _, .zero rn => zeroBits f (Bool.xor ln rn)
       | .finite ln lnum lden, .finite rn rnum rden =>
         roundRatioTiesToEven f (Bool.xor ln rn) (lnum * rnum) (lden * rden))
  | .div =>
    .some
      (match l, r with
       | .nan _ _ _, _ | _, .nan _ _ _ => preferredNaNBits f
       | .inf _, .inf _ | .zero _, .zero _ => preferredNaNBits f
       | .inf ln, .zero rn => infBits f (Bool.xor ln rn)
       | .inf ln, .finite rn _ _ => infBits f (Bool.xor ln rn)
       | .zero ln, .inf rn => zeroBits f (Bool.xor ln rn)
       | .zero ln, .finite rn rnum _ =>
         if rnum = 0 then preferredNaNBits f else zeroBits f (Bool.xor ln rn)
       | .finite ln lnum _, .zero rn =>
         if lnum = 0 then preferredNaNBits f else infBits f (Bool.xor ln rn)
       | .finite ln _ _, .inf rn => zeroBits f (Bool.xor ln rn)
       | .finite ln lnum lden, .finite rn rnum rden =>
         if rnum = 0 then
           if lnum = 0 then preferredNaNBits f else infBits f (Bool.xor ln rn)
         else
           roundRatioTiesToEven f (Bool.xor ln rn) (lnum * rden) (lden * rnum))
  | .rem =>
    .some
      (match l, r with
       | .nan _ _ _, _ | _, .nan _ _ _ | .inf _, _ | _, .zero _ => preferredNaNBits f
       | .zero _, .inf _ | .finite _ _ _, .inf _ => lb
       | .zero ln, .finite _ rnum _ =>
         if rnum = 0 then preferredNaNBits f else zeroBits f ln
       | .finite ln lnum lden, .finite _ rnum rden =>
         if rnum = 0 then preferredNaNBits f
         else
           let q := (lnum * rden) / (lden * rnum)
           let rem := lnum * rden - q * (lden * rnum)
           roundRatioTiesToEven f ln rem (lden * rden))
  | _ => .none

/--
NaN result selection mode for relational floating-point semantics
(`EvalFloatBinOpRel` and `EvalRvalueFloatRel`):
- `.deterministic`: selects only `preferredNaNBits target` (matching Miri with
  `-Zmiri-deterministic-floats` and `evalFloatArithBase`).
- `.nondeterministic`: permits any NaN bit pattern generated by `nanChoices`
  (preferred NaN, quieted input NaNs, and unchanged signaling input NaNs with
  either sign, matching Rust's portable NaN rules and Miri's `generate_nan`).

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "The following rules apply when a NaN value is returned from an arithmetic
> operation:
> - The result has a non-deterministic sign.
> - The quiet bit and payload are non-deterministically chosen from the
>   following set of options:
>   - Preferred NaN: The quiet bit is set and the payload is all-zero.
>   - Quieting NaN propagation: The quiet bit is set and the payload is copied
>     from any input operand that is a NaN.
>   - Unchanged NaN propagation: The quiet bit and payload are copied from any
>     input operand that is a NaN."

Modeling note: target-specific "extra" NaN payloads documented in `core` are not
enumerated by `nanChoices` (matching Miri's `operator.rs::generate_nan`).
-/
inductive FloatArithMode : Type where
  /-- Deterministic preferred-NaN mode. -/
  | deterministic : FloatArithMode
  /-- Nondeterministic NaN sign/payload selection mode (`nanChoices`). -/
  | nondeterministic : FloatArithMode
deriving DecidableEq

/-- Quieted NaN candidates converted to `target` from each NaN element of `inputs`. -/
def nanChoicesQuieted (target : IeeeFormat) : List (IeeeFormat × Nat) → List Nat
  | .nil => .nil
  | inp :: rest =>
    let src := inp.1
    let b := inp.2 % 2 ^ src.width
    let tail := nanChoicesQuieted target rest
    if isNaNBits src b then evalFloatToFloatRoundTiesToEven src target b :: tail
    else tail

/-- Unchanged signaling NaN candidates converted to `target` when their lower
payload remains nonzero (clearing the quiet bit never produces infinity). -/
def nanChoicesSignaling (target : IeeeFormat) : List (IeeeFormat × Nat) → List Nat
  | .nil => .nil
  | inp :: rest =>
    let src := inp.1
    let b := inp.2 % 2 ^ src.width
    let tail := nanChoicesSignaling target rest
    if isSignalingNaNBits src b then
      let conv := evalFloatToFloatRoundTiesToEven src target b
      let c := unpackBits target conv
      let lower := c.fraction % 2 ^ (target.fractionBits - 1)
      if lower = 0 then tail
      else encodeBits target c.neg (2 ^ target.exponentBits - 1) lower :: tail
    else tail

/-- Expand each candidate NaN into `[cand, -cand]` (independent sign choice). -/
def expandNanSigns (target : IeeeFormat) : List Nat → List Nat
  | .nil => .nil
  | cand :: rest => cand :: evalFloatNeg target cand :: expandNanSigns target rest

/--
Ordered list of admissible NaN bit patterns for an arithmetic operation (or
float-to-float cast) targeting format `target` with inputs `inputs`, matching
`Miri.Interpreter.FloatBits.nanChoices` element-for-element:
- `.deterministic`: `[preferredNaNBits target]`;
- `.nondeterministic`: `preferredNaNBits target` followed by quieted input NaNs
  and nonzero-lower-payload unchanged signaling input NaNs, each paired with its
  sign-flipped counterpart.

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "- Preferred NaN: The quiet bit is set and the payload is all-zero.
> - Quieting NaN propagation: The quiet bit is set and the payload is copied
>   from any input operand that is a NaN. If the inputs and outputs do not have
>   the same payload size (i.e., for as casts), then
>   - If the output is smaller than the input, low-order bits of the payload get
>     dropped.
>   - If the output is larger than the input, the payload gets filled up with 0s
>     in the low-order bits.
> - Unchanged NaN propagation: The quiet bit and payload are copied from any
>   input operand that is a NaN. If the inputs and outputs do not have the same
>   size (i.e., for as casts), the same rules as for “quieting NaN propagation”
>   apply, with one caveat: if the output is smaller than the input, dropping
>   the low-order bits may result in a payload of 0; a payload of 0 is not
>   possible with a signaling NaN (the all-0 significand encodes an infinity) so
>   unchanged NaN propagation cannot occur with some inputs."

Modeling choice: excludes target-specific "extra" NaN payloads, matching Miri's
`generate_nan`.
-/
def nanChoices (target : IeeeFormat) (inputs : List (IeeeFormat × Nat))
    (mode : FloatArithMode) : List Nat :=
  match mode with
  | .deterministic => [preferredNaNBits target]
  | .nondeterministic =>
    let candidates :=
      preferredNaNBits target ::
        (nanChoicesQuieted target inputs ++ nanChoicesSignaling target inputs)
    expandNanSigns target candidates

/-- Boolean list membership test on `Nat` using `Nat.beq`. -/
def natListMem (x : Nat) : List Nat → Bool
  | .nil => false
  | y :: ys => Bool.or (Nat.beq x y) (natListMem x ys)

/--
Decidable check that `bits % 2 ^ f.width` is an admissible quiet NaN in
`nanChoices f inputs .nondeterministic` (preferred or quieted input NaN with
either sign).

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "In particular, if all input NaNs are quiet (or if there are no input NaNs),
> then the output NaN is definitely quiet. Signaling NaN outputs can only occur
> if they are provided as an input"
-/
def isAdmissibleQuietNaN
    (f : IeeeFormat)
    (inputs : List (IeeeFormat × Nat))
    (bits : Nat) : Bool :=
  let b := bits % 2 ^ f.width
  Bool.and (isQuietNaNBits f b) (natListMem b (nanChoices f inputs .nondeterministic))

/--
Deterministic executable evaluator for `f32` / `f64` binary operations:
dispatches comparisons (`eq`, `ne`, `lt`, `le`, `gt`, `ge`) to `evalFloatCmp`
returning a `bool` scalar, and arithmetic (`add`, `sub`, `mul`, `div`, `rem`) to
`evalFloatArithBase` returning a scalar of width `f.byteWidth`. Returns `.none`
for unsupported `BinOp`s.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and
> f64, respectively."

Modeling choice: when an arithmetic operation yields NaN, `evalFloatBinOp`
returns `preferredNaNBits f` (realizing `EvalFloatBinOpRel .deterministic`).
-/
def evalFloatBinOp (op : BinOp) (f : IeeeFormat) (lhsBits rhsBits : Nat) : Option ScalarInt :=
  match evalFloatCmp op f lhsBits rhsBits with
  | .some b => .some (boolToScalar b)
  | .none =>
    match evalFloatArithBase op f lhsBits rhsBits with
    | .some bits => .some ⟨bits, f.byteWidth⟩
    | .none => .none

/--
Relational specification of IEEE-754 `f32` / `f64` binary operations parameterized
by `mode : FloatArithMode`:
- Comparisons (`eq`, `ne`, `lt`, `le`, `gt`, `ge`) are deterministic and
  mode-independent (`evalFloatCmp`).
- Finite and infinite arithmetic outcomes (`add`, `sub`, `mul`, `div`, `rem`)
  are uniquely determined by `evalFloatArithBase` (`roundTiesToEven`).
- NaN arithmetic outcomes may be any `cand ∈ nanChoices f [(f, lhsBits % 2^f.width),
  (f, rhsBits % 2^f.width)] mode`.

Reference (`core` documentation, "Primitive Type f32", "NaN bit patterns"):
<https://doc.rust-lang.org/1.98.0/core/primitive.f32.html#nan-bit-patterns>

> "The following rules apply when a NaN value is returned from an arithmetic
> operation:
> - The result has a non-deterministic sign.
> - The quiet bit and payload are non-deterministically chosen from the
>   following set of options"

Modeling note: `.deterministic` picks only `preferredNaNBits f` (matching
`evalFloatBinOp`), whereas `.nondeterministic` admits preferred, quieted, and
nonzero-payload signaling NaNs with either sign (excluding target-specific extra
NaNs).
-/
def EvalFloatBinOpRel
    (mode : FloatArithMode)
    (op : BinOp)
    (f : IeeeFormat)
    (lhsBits rhsBits : Nat)
    (out : ScalarInt) : Prop :=
  match evalFloatCmp op f lhsBits rhsBits with
  | .some b => out = boolToScalar b
  | .none =>
    match evalFloatArithBase op f lhsBits rhsBits with
    | .some baseBits =>
      if isNaNBits f baseBits = true then
        ∃ cand,
          cand ∈ nanChoices f [(f, lhsBits % 2 ^ f.width), (f, rhsBits % 2 ^ f.width)] mode ∧
          out = ⟨cand, f.byteWidth⟩
      else
        out = ⟨baseBits, f.byteWidth⟩
    | .none => False

/--
Policy parameterizing how byte-level transmutation and typed scalar decoding
handle bytes carrying pointer provenance when decoded at non-pointer scalar
types (integers, floats, `bool`, `char`, and non-pointer scalar/enum layouts):
- `.strictUcg630Ub` (default): treats decoding provenance-carrying bytes into a
  non-pointer scalar as undefined behavior (`.none` / `.ub`), matching the
  conservative UCG #630 position and Rust's `const`-context rule.
- `.stripProvenance`: discards byte provenance on non-pointer scalar decodes and
  reads only the abstract byte values, matching MiniRust and runtime-stripping
  semantics (`reference#1752`).

Reference (`core::mem::transmute` documentation, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/mem/fn.transmute.html>

> "Transmuting pointers to integers in a const context is undefined behavior,
> unless the pointer was originally created from an integer. (That includes this
> function specifically, integer-to-pointer casts, and helpers like dangling,
> but also semantically-equivalent conversions such as punning through repr(C)
> union fields.) Any attempt to use the resulting value for integer operations
> will abort const-evaluation. (And even outside const, such transmutation is
> touching on many unspecified aspects of the Rust memory model and should be
> avoided. See below for alternatives.)"

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."

Modeling choice: because Rust 1.98.0 leaves non-`const` pointer-to-integer
transmutation unspecified ("touching on many unspecified aspects of the Rust
memory model"), the TCB parameterizes this boundary explicitly rather than
hard-coding a single unguaranteed assumption. `.strictUcg630Ub` is the sound
default (refining `.stripProvenance`), and neither policy ever permits forging
reference (`.ref`) or function-pointer (`.fnPtr`) provenance.
-/
inductive Ptr2IntTransmutePolicy : Type where
  /-- Reject provenance-carrying bytes on non-pointer scalar decode (default, conservative UB). -/
  | strictUcg630Ub : Ptr2IntTransmutePolicy
  /-- Discard provenance on non-pointer scalar decode (MiniRust / stripping semantics). -/
  | stripProvenance : Ptr2IntTransmutePolicy
deriving DecidableEq

end Trusted.Rustc.V2026_08_01.MirSemantics
