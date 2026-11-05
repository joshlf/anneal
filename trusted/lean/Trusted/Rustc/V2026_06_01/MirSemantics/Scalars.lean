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
Half-modulus `256 ^ sizeBytes / 2 = 2 ^ (8 * sizeBytes - 1)` separating
non-negative (`[0, half)`) and negative (`[half, 2 * half)`) two's-complement
bit patterns of byte width `sizeBytes`.

1-to-1 with the two's-complement sign threshold `2 ^ (N - 1)` for an `N`-bit
signed integer in Rust.

Reference (The Rust Reference, "Numeric types — Integer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#integer-types>

> "Signed integer types with two's complement representation:
>
> Type   Minimum            Maximum
> i8     -(2^7)             2^7-1
> i16    -(2^15)            2^15-1
> i32    -(2^31)            2^31-1
> i64    -(2^63)            2^63-1
> i128   -(2^127)           2^127-1"
-/
@[reducible]
def signedHalfModulus (sizeBytes : Nat) : Nat :=
  Nat.div (scalarModulus sizeBytes) 2

/--
Evaluate exact integer division `core::intrinsics::exact_div(lhs, rhs)` over
two equal-width non-zero `ScalarInt` operands, returning `.none` on undefined
behavior (`rhs == 0`, signed overflow `MIN / -1`, or non-zero remainder
`lhs % rhs != 0`).

1-to-1 with `core::intrinsics::exact_div` (`IntBinOp::DivExact` in MiniRust):
when `isSigned = false`, checks `b != 0` and `a % b == 0` and returns `a / b`;
when `isSigned = true`, additionally rejects `a == INT_MIN && b == -1`, checks
that `|a| % |b| == 0`, and returns the two's-complement quotient `lhs / rhs`.

Reference (`core::intrinsics::exact_div`, Rust 1.98.0):
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
@[reducible]
def evalExactDiv
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option ScalarInt :=
  match
    Bool.and
      (Nat.beq lhs.sizeBytes rhs.sizeBytes)
      (Bool.not (Nat.beq lhs.sizeBytes 0))
  with
  | false => .none
  | true =>
    let modulus := scalarModulus lhs.sizeBytes
    let a := wrapScalarBits lhs.bits modulus
    let b := wrapScalarBits rhs.bits modulus
    match Nat.beq b 0 with
    | true => .none
    | false =>
      match isSigned with
      | false =>
        match Nat.beq (Nat.mod a b) 0 with
        | false => .none
        | true => .some ⟨Nat.div a b, lhs.sizeBytes⟩
      | true =>
        let half := signedHalfModulus lhs.sizeBytes
        match Bool.and (Nat.beq a half) (Nat.beq b (Nat.sub modulus 1)) with
        | true => .none
        | false =>
          let negA := Nat.ble half a
          let negB := Nat.ble half b
          let magA :=
            match negA with
            | false => a
            | true => wrapScalarBits (Nat.sub modulus a) modulus
          let magB :=
            match negB with
            | false => b
            | true => wrapScalarBits (Nat.sub modulus b) modulus
          match Nat.beq (Nat.mod magA magB) 0 with
          | false => .none
          | true =>
            let quotMag := Nat.div magA magB
            let resBits :=
              match negA, negB with
              | false, false => quotMag
              | true, true => quotMag
              | _, _ => wrapScalarBits (Nat.sub modulus quotMag) modulus
            .some ⟨resBits, lhs.sizeBytes⟩

/--
Lift `evalExactDiv` to an `RvalueEvalResult`, returning
`.ok (.scalar q) locals mem` when exact division succeeds and `.ub` when
`evalExactDiv` returns `.none`.

1-to-1 with the operational outcome of `core::intrinsics::exact_div` in MIR
evaluation.

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
@[reducible]
def evalScalarExactDiv
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory := {})
    (isSigned : Bool := false) :
    RvalueEvalResult :=
  match evalExactDiv lhs rhs isSigned with
  | .some q => .ok (.scalar q) locals mem
  | .none => .ub

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

end Trusted.Rustc.V2026_06_01.MirSemantics
