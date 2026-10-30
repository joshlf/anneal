import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

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
Target byte width for integer cast targets (`CastKind.intToInt`) on a 64-bit
target (`usize` and `isize` have byte width `8`).

Reference (The Rust Reference, "Type cast expressions — Numeric cast"):
<https://doc.rust-lang.org/1.98.0/reference/expressions/operator-expr.html#numeric-cast>

> "Casting between two integers of the same size (e.g. i32 -> u32) is a no-op
> (Rust uses 2’s complement for negative values of fixed integers)"
>
> "Casting from a larger integer to a smaller integer (e.g. u32 -> u8) will
> truncate"
-/
def intCastTargetBytes : RigidTy → Option Nat
  | .uint .u8 => .some 1
  | .uint .u16 => .some 2
  | .uint .u32 => .some 4
  | .uint .u64 => .some 8
  | .uint .u128 => .some 16
  | .uint .usize => .some 8
  | .int .i8 => .some 1
  | .int .i16 => .some 2
  | .int .i32 => .some 4
  | .int .i64 => .some 8
  | .int .i128 => .some 16
  | .int .isize => .some 8
  | _ => .none

end Trusted.Rustc.V2026_06_01.MirSemantics
