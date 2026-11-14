/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.MirAst
import Trusted.MirSemantics
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import MiniRustSpec.Correspondence.ProvenanceWitness
import MiniRustSpec.Correspondence.RefWitness
import MiniRustSpec.Correspondence.TbWitness

/-!
# Prototype: closing the 8 tracked TCB correspondence divergences + pure IEEE-754 float casts

**Track:** `prototype` (`no_merge_prototype`). Nothing in `trusted/**` is modified: this
file is an *operational overlay* over the unmodified `Trusted.Rustc.V2026_06_01` MIR AST
and helper functions, used to validate the candidate semantics before the Track A TCB
update `ws-tcb-correspondence-div8-and-ieee-float`.

## Part A — frame-qualified, Tree-Borrows-faithful overlay

`ProtoBorrowEntry` extends `BorrowEntry` with `targetFrameDepth` (the depth of the stack
frame owning `targetLocal`; `0` is the root frame and `currentFrameDepth s =
s.memory.callStack.length` is the active frame). Every borrow-table update and every
deref read/write is scoped to `(targetFrameDepth, targetLocal)`. The interpreter
(`evalOperandProto`, `evalRvalueProto`, `evalStmtProto`, `evalTerminatorProto`,
`stepMirFnProto`, `runMirProto`) closes the eight tracked divergences of
`scripts/run_nightly_verification_suite.py` (`TRACKED_CORRESPONDENCE_DIVERGENCES`):

| ID | Fix in this overlay |
|----|---------------------|
| `DIV-MR-CALL-TARGET-LOCAL` | frame-qualified deref reads/writes (`readFrameLocalProto`, `writeFrameLocalProto`) |
| `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` | every borrow update scoped to `(targetFrameDepth, targetLocal)` |
| `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` | direct root write is a foreign write (`.reservedFrz` → `.disabled`) |
| `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` | `Return` checks `hasFrameDeallocProtectorConflictProto` before releasing protectors |
| `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` | `preventsDeallocation .cell = false` (StorageDead / Return) |
| `DIV-LM-RAW-OVERWRITE-CHAR-COPY` | `validateLoadedValueProto` checks `char` scalar validity on typed loads |
| `DIV-LM-D6-OFFSET-DISABLED-TAG` | `BinOp.Offset` checks allocation bounds only (`evalPtrOffsetBinOpProto`) |
| `DIV-LM-ENUM-SET-DISCR-UNINIT` | `SetDiscriminant` on an `.uninit` enum local writes the tag |

## Part B — pure `BitVec 32` / `BitVec 64` IEEE-754 casts

`F32Bits := BitVec 32` and `F64Bits := BitVec 64` with exact rational decoding
(`decodeBits`, transliterating `Miri.Interpreter.FloatBits.decode`), nearest-ties-to-even
rounding (`roundQuotientTiesToEven`, `roundRatioBits`, transliterating
`Miri.Interpreter.FloatBits.roundRatio`), and the three Rust `as`-cast families
`evalFloatToIntSaturating`, `evalIntToFloatRoundTiesToEven`,
`evalFloatToFloatRoundTiesToEven`, wired into `evalRvalueProto` for
`CastKind.{floatToInt, intToFloat, floatToFloat}`. No host `Float`, no `extern`.

Every theorem below is kernel-checked and depends only on `propext` / `Quot.sound`
(see the `#guard_msgs in #print axioms` block at the end of the file).

## MiniRust ground truth without `Classical.choice`

The `Mach` / `MachTB` initial states of the two multi-function `ProvenanceWitness` programs
are built by a `String.toList`-free replica of `translateProgWithIntrinsics`
(`translateProgWithIntrinsicsSF`, §4): the upstream translator's sole classical leaf is
core `String.toList` in `translateIntrinsicOrNone`. The replica's machines are
kernel-checked equal (`rfl`) to `ProvenanceWitness.callerRefMutSilentWrongLocalMInit` /
`TBInit` and `callerBorrowAcrossScalarCallMInit` / `TBInit` in the audit harness of
`scripts/test_tcb_correspondence_div8_proto.py`.
-/

namespace Anneal.TcbCorrespondenceDiv8AndFloatPrototype

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout

/-! ## §1. Part B core: pure IEEE-754 binary32 / binary64 bit-level arithmetic -/

/-- The two IEEE-754 interchange formats modeled by the prototype. -/
inductive IeeeFormat : Type where
  /-- IEEE-754 `binary32` (Rust `f32`). -/
  | binary32 : IeeeFormat
  /-- IEEE-754 `binary64` (Rust `f64`). -/
  | binary64 : IeeeFormat
deriving DecidableEq

namespace IeeeFormat

/-- Total bit width. -/
def width : IeeeFormat → Nat
  | .binary32 => 32
  | .binary64 => 64

/-- Exponent field width. -/
def exponentBits : IeeeFormat → Nat
  | .binary32 => 8
  | .binary64 => 11

/-- Trailing significand (fraction) field width. -/
def fractionBits : IeeeFormat → Nat
  | .binary32 => 23
  | .binary64 => 52

/-- Exponent bias. -/
def bias : IeeeFormat → Nat
  | .binary32 => 127
  | .binary64 => 1023

/-- Byte width of the corresponding Rust scalar. -/
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

/-- Assemble a bit pattern from sign, biased exponent, and fraction fields. -/
def packBits (f : IeeeFormat) (c : FloatComponents) : Nat :=
  (if c.neg then 2 ^ (f.width - 1) else 0) + c.exponent * 2 ^ f.fractionBits + c.fraction

/-- Unpack an `F32Bits`. -/
def unpackF32 (x : F32Bits) : FloatComponents := unpackBits .binary32 x.toNat
/-- Pack an `F32Bits`. -/
def packF32 (c : FloatComponents) : F32Bits := BitVec.ofNat 32 (packBits .binary32 c)
/-- Unpack an `F64Bits`. -/
def unpackF64 (x : F64Bits) : FloatComponents := unpackBits .binary64 x.toNat
/-- Pack an `F64Bits`. -/
def packF64 (c : FloatComponents) : F64Bits := BitVec.ofNat 64 (packBits .binary64 c)

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

/-- `Miri.Interpreter.FloatBits.powScale`: scale `n / d` by `2 ^ e`. -/
def powScale (n d : Nat) : Int → Nat × Nat
  | .ofNat k => (n * 2 ^ k, d)
  | .negSucc k => (n, d * 2 ^ (k + 1))

/-- Exact decoding of an IEEE-754 bit pattern (transliterates
`Miri.Interpreter.FloatBits.decode`, `lean-miri/vendor/Miri/Interpreter/Float.lean:57`,
except that signed zeros are reported as `.zero` instead of `.finite 0 d`). -/
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

/-- `Miri.Interpreter.FloatClass`. -/
inductive MiriFloatClass : Type where
  | finite (numerator denominator : Nat) : MiriFloatClass
  | infinite : MiriFloatClass
  | nan (payload : Nat) : MiriFloatClass
deriving DecidableEq

/-- `Miri.Interpreter.FloatDecoded`. -/
structure MiriFloatDecoded : Type where
  negative : Bool
  value : MiriFloatClass
deriving DecidableEq

/-- Literal transliteration of `Miri.Interpreter.FloatBits.decode`
(`lean-miri/vendor/Miri/Interpreter/Float.lean:57-69`); `none` is Miri's
`.encodingExceedsWidth` error. -/
def miriDecode (f : IeeeFormat) (bits : Nat) : Option MiriFloatDecoded :=
  if bits ≥ 2 ^ f.width then none
  else
    let negative := bits / 2 ^ (f.width - 1) != 0
    let exponent := (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits
    let fraction := bits % 2 ^ f.fractionBits
    if exponent == 2 ^ f.exponentBits - 1 then
      some ⟨negative, if fraction == 0 then .infinite else .nan fraction⟩
    else
      let significand := if exponent == 0 then fraction else 2 ^ f.fractionBits + fraction
      let unbiased : Int := if exponent == 0 then f.minExponent else (exponent : Int) - (f.bias : Int)
      let nd := powScale significand 1 (unbiased - (f.fractionBits : Int))
      some ⟨negative, .finite nd.1 nd.2⟩

/-- Project a `FloatKind` to Miri's decoded representation (zeros become
`.finite 0 den` exactly as Miri decodes them). -/
def FloatKind.toMiri (f : IeeeFormat) : FloatKind → MiriFloatDecoded
  | .zero neg => ⟨neg, .finite 0 (powScale 0 1 (f.minExponent - (f.fractionBits : Int))).2⟩
  | .finite neg n d => ⟨neg, .finite n d⟩
  | .inf neg => ⟨neg, .infinite⟩
  | .nan neg _ payload => ⟨neg, .nan payload⟩

/-- Rounding direction used by the integer quotient core. -/
inductive RoundingMode : Type where
  /-- IEEE-754 `roundTiesToEven` (Rust `as`, `rustc_apfloat` default). -/
  | tiesToEven : RoundingMode
  /-- Round half away from zero (`f64::round`; the `b/585733184` bug model). -/
  | halfAwayFromZero : RoundingMode

/-- Nearest integer to `n / d`, ties to even (`roundQuotientEven`,
`lean-miri/vendor/Miri/Interpreter/Float.lean:90`). -/
def roundQuotientTiesToEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if r * 2 > d ∨ (r * 2 = d ∧ q % 2 = 1) then q + 1 else q

/-- Nearest integer to `n / d`, ties away from zero (contrast model). -/
def roundQuotientHalfAwayFromZero (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if r * 2 ≥ d then q + 1 else q

/-- Dispatch on `RoundingMode`. -/
def roundQuotient : RoundingMode → Nat → Nat → Nat
  | .tiesToEven => roundQuotientTiesToEven
  | .halfAwayFromZero => roundQuotientHalfAwayFromZero

/-- `floor (log2 (n / d))` for nonzero `n`, `d` (`ratioExponent`,
`lean-miri/vendor/Miri/Interpreter/Float.lean:85`). -/
def ratioExponent (n d : Nat) : Int :=
  if d ≤ n then ((n / d).log2 : Int)
  else
    let k := (d / n).log2
    if d ≤ n * 2 ^ k then -(k : Int) else -((k : Int) + 1)

/-- Bit pattern of a signed zero. -/
def zeroBits (f : IeeeFormat) (neg : Bool) : Nat := if neg then 2 ^ (f.width - 1) else 0

/-- Bit pattern with the given sign, biased exponent, and fraction (`encode`). -/
def encodeBits (f : IeeeFormat) (neg : Bool) (exponent fraction : Nat) : Nat :=
  zeroBits f neg + exponent * 2 ^ f.fractionBits + fraction

/-- Bit pattern of a signed infinity. -/
def infBits (f : IeeeFormat) (neg : Bool) : Nat :=
  encodeBits f neg (2 ^ f.exponentBits - 1) 0

/-- Bit pattern of the preferred (canonical positive quiet) NaN. -/
def preferredNaNBits (f : IeeeFormat) : Nat :=
  encodeBits f false (2 ^ f.exponentBits - 1) (2 ^ (f.fractionBits - 1))

/-- Correctly rounded encoding of the exact nonnegative rational `n / d` with a
separate sign (transliterates `Miri.Interpreter.FloatBits.roundRatio`,
`lean-miri/vendor/Miri/Interpreter/Float.lean:98-112`, with the rounding direction
abstracted by `mode`). Gradual underflow comes from clamping the working exponent to
`minExponent`; rounding carry-out bumps the exponent; overflow produces `±∞`. Miri's
`throw` branches (zero denominator, inconsistent rounding) are mapped to the preferred
NaN and are unreachable from decoded inputs. -/
def roundRatioBits (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d : Nat) : Nat :=
  if d = 0 then preferredNaNBits f
  else if n = 0 then zeroBits f neg
  else
    let exponent := max (ratioExponent n d) f.minExponent
    if exponent > f.maxExponent then infBits f neg
    else
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let significand := roundQuotient mode scaled.1 scaled.2
      let carry := decide (2 ^ (f.fractionBits + 1) ≤ significand)
      let significand' := if carry then significand / 2 else significand
      let exponent' := if carry then exponent + 1 else exponent
      if exponent' > f.maxExponent then infBits f neg
      else if significand' < 2 ^ f.fractionBits then
        if exponent' = f.minExponent then encodeBits f neg 0 significand'
        else preferredNaNBits f
      else if 2 ^ (f.fractionBits + 1) ≤ significand' then preferredNaNBits f
      else encodeBits f neg (exponent' + (f.bias : Int)).toNat (significand' - 2 ^ f.fractionBits)

/-- IEEE-754 `roundTiesToEven` encoding of the exact rational `(-1)^neg * n / d`
(`Miri.Interpreter.FloatBits.roundRatio`): normal, gradual-underflow subnormal, carry-out
to `exp + 1`, and overflow to `±∞`. -/
def roundRatioTiesToEven (f : IeeeFormat) (neg : Bool) (n d : Nat) : Nat :=
  roundRatioBits .tiesToEven f neg n d

/-- `true` iff `bits` decodes to a NaN. -/
def isNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ _ _ => true
  | _ => false

/-- `true` iff `bits` decodes to a quiet NaN. -/
def isQuietNaNBits (f : IeeeFormat) (bits : Nat) : Bool :=
  match decodeBits f bits with
  | .nan _ quiet _ => quiet
  | _ => false

/-! ### Float → int (saturating, truncating toward zero; NaN ↦ 0) -/

/-- Target integer type of a `FloatToInt` cast. -/
inductive IntTarget : Type where
  /-- Signed integer target. -/
  | signed (w : IntTy) : IntTarget
  /-- Unsigned integer target. -/
  | unsigned (w : UintTy) : IntTarget

/-- Target pointer width (`isize` / `usize`). -/
inductive PtrWidth : Type where
  | bits32 : PtrWidth
  | bits64 : PtrWidth

/-- Pointer width in bits. -/
def PtrWidth.bits : PtrWidth → Nat
  | .bits32 => 32
  | .bits64 => 64

/-- Bit width of an integer target. -/
def IntTarget.bitWidth (pw : PtrWidth) : IntTarget → Nat
  | .signed w => w.bitWidth pw.bits
  | .unsigned w => w.bitWidth pw.bits

/-- Signedness of an integer target. -/
def IntTarget.isSigned : IntTarget → Bool
  | .signed _ => true
  | .unsigned _ => false

/-- Minimum representable value. -/
def IntTarget.minValue (pw : PtrWidth) (t : IntTarget) : Int :=
  if t.isSigned then -((2 ^ (t.bitWidth pw - 1) : Nat) : Int) else 0

/-- Maximum representable value. -/
def IntTarget.maxValue (pw : PtrWidth) (t : IntTarget) : Int :=
  if t.isSigned then ((2 ^ (t.bitWidth pw - 1) : Nat) : Int) - 1
  else ((2 ^ t.bitWidth pw : Nat) : Int) - 1

/-- Clamp `v` into `[lo, hi]`. -/
def clampInt (lo hi v : Int) : Int := max lo (min hi v)

/-- Truncation toward zero of `(-1)^neg * n / d`. -/
def truncRatio (neg : Bool) (n d : Nat) : Int :=
  if neg then -((n / d : Nat) : Int) else ((n / d : Nat) : Int)

/-- Mathematical result of a Rust saturating `as` float-to-int cast
(`Miri.Interpreter.FloatBits.toInteger`): NaN ↦ 0, ±∞ ↦ max/min, finite values
truncate toward zero and clamp. -/
def floatToIntValue (k : FloatKind) (lo hi : Int) : Int :=
  match k with
  | .nan _ _ _ => 0
  | .inf neg => if neg then lo else hi
  | .zero _ => 0
  | .finite neg n d => clampInt lo hi (truncRatio neg n d)

/-- Canonical two's-complement encoding of `v` at width `w`. -/
def encodeTwosComplement (w : Nat) (v : Int) : Nat :=
  (v % ((2 ^ w : Nat) : Int)).toNat

/-- Rust `as` float-to-int cast on a raw `src`-format bit pattern, returning a
canonical two's-complement `ScalarInt` of the target width. -/
def evalFloatToIntSaturating (src : IeeeFormat) (bits : Nat) (target : IntTarget)
    (pw : PtrWidth) : ScalarInt :=
  let w := target.bitWidth pw
  ⟨encodeTwosComplement w
      (floatToIntValue (decodeBits src bits) (target.minValue pw) (target.maxValue pw)),
    w / 8⟩

/-! ### Int → float (round to nearest, ties to even) -/

/-- Integer value of a `w`-bit two's-complement (signed) or unsigned bit pattern. -/
def intValueOfBits (signed : Bool) (w bits : Nat) : Int :=
  let b := bits % 2 ^ w
  if signed = true ∧ 2 ^ (w - 1) ≤ b then (b : Int) - ((2 ^ w : Nat) : Int) else (b : Int)

/-- Rust `as` int-to-float cast (`Miri.Interpreter.FloatBits.fromInteger`):
correctly rounded with `roundTiesToEven`. -/
def evalIntToFloatRoundTiesToEven (signed : Bool) (w bits : Nat) (dst : IeeeFormat) : Nat :=
  let v := intValueOfBits signed w bits
  roundRatioBits .tiesToEven dst (decide (v < 0)) v.natAbs 1

/-- Half-away-from-zero contrast model of the int-to-float cast (`b/585733184`). -/
def evalIntToFloatHalfAwayFromZero (signed : Bool) (w bits : Nat) (dst : IeeeFormat) : Nat :=
  let v := intValueOfBits signed w bits
  roundRatioBits .halfAwayFromZero dst (decide (v < 0)) v.natAbs 1

/-! ### Float → float (exact widening, `roundTiesToEven` narrowing, quiet-NaN propagation) -/

/-- Float-to-float conversion (transliterates `Miri.Interpreter.FloatBits.convert`,
`lean-miri/vendor/Miri/Interpreter/Float.lean:117-128`): finite values are correctly
rounded; NaN payloads are quieted, shifted to the target precision, and get the target
quiet bit forced (pinned `rustc_apfloat` `ieee.rs::convert_r`). -/
def convertFloatBits (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat) : Nat :=
  match decodeBits src bits with
  | .zero neg => zeroBits dst neg
  | .finite neg n d => roundRatioBits mode dst neg n d
  | .inf neg => infBits dst neg
  | .nan neg _ payload =>
    let quiet := Nat.lor payload (2 ^ (src.fractionBits - 1))
    let payload' :=
      if src.fractionBits ≤ dst.fractionBits then
        quiet * 2 ^ (dst.fractionBits - src.fractionBits)
      else quiet / 2 ^ (src.fractionBits - dst.fractionBits)
    encodeBits dst neg (2 ^ dst.exponentBits - 1) (Nat.lor payload' (2 ^ (dst.fractionBits - 1)))

/-- Rust `as` float-to-float cast with `roundTiesToEven`. -/
def evalFloatToFloatRoundTiesToEven (src dst : IeeeFormat) (bits : Nat) : Nat :=
  convertFloatBits .tiesToEven src dst bits

/-- `x as f64` for `x : f32`. -/
def f32ToF64 (x : F32Bits) : F64Bits :=
  BitVec.ofNat 64 (evalFloatToFloatRoundTiesToEven .binary32 .binary64 x.toNat)

/-- `x as f32` for `x : f64`. -/
def f64ToF32 (x : F64Bits) : F32Bits :=
  BitVec.ofNat 32 (evalFloatToFloatRoundTiesToEven .binary64 .binary32 x.toNat)

/-! ## §2. Part A data structures: frame-qualified borrow table -/

/-- Frame-qualified Tree Borrows entry. Identical to `BorrowEntry` except that
`targetFrameDepth` records the depth of the stack frame owning `targetLocal`
(`0` = root frame; `currentFrameDepth s` = active frame). Byte-ranged entries
(`rangeOffset` / `rangeLen > 0`) are never created by this prototype. -/
structure ProtoBorrowEntry : Type where
  /-- Provenance tag. -/
  tag : Nat
  /-- Local of the owning frame. -/
  targetLocal : LocalIdx
  /-- Field/downcast projection of the borrowed sub-place. -/
  targetProjection : List ProjectionElem := .nil
  /-- Tree Borrows permission. -/
  perm : TreeBorrowPerm
  /-- Optional function-entry protector. -/
  protector : Option Nat := .none
  /-- Parent tag in the borrow tree. -/
  parentTag : Option Nat := .none
  /-- Depth of the stack frame owning `targetLocal` (`DIV-MR-CALL-TARGET-LOCAL`). -/
  targetFrameDepth : Nat := 0
  /-- True once the backing local allocation was deallocated (`StorageDead`/`StorageLive`/`Return`),
  distinguishing a deallocated allocation from a tag whose Tree Borrows `perm` was `.disabled`
  by a foreign write while the allocation remains live (`DIV-LM-D6-OFFSET-DISABLED-TAG` vs
  `D2` storage-revival pointer offset). -/
  allocDead : Bool := false

/-- Saved caller activation record. -/
structure ProtoSavedFrame : Type where
  /-- Body executing in the saved frame. -/
  callerBody : CapturedMir
  /-- Saved frame (locals after argument evaluation). -/
  frame : StackFrame
  /-- Caller destination receiving the callee's `_0`. -/
  destination : Place
  /-- Caller continuation block. -/
  returnTarget : BasicBlockIdx
  /-- Protectors active in the caller, restored when the callee returns. -/
  savedProtectors : List Nat

/-- Prototype memory: frame-qualified borrow table, call stack, protectors. -/
structure ProtoMemory : Type where
  borrows : List ProtoBorrowEntry := .nil
  nextTag : Nat := 1
  callees : List CapturedMir := .nil
  callStack : List ProtoSavedFrame := .nil
  activeProtectors : List Nat := .nil
  nextProtector : Nat := 1
  callerLocals : List LocalSlot := .nil

/-- Prototype machine state (the active body is carried explicitly). -/
structure ProtoMachineState : Type where
  body : CapturedMir
  frame : StackFrame
  memory : ProtoMemory

/-- Configuration knobs used only to *execute contrast models* on the real AST:
* `preserveReservedOnDirectWrite := true` is the pre-`LM-3.3` buggy direct-write
  model in which a direct root write leaves `.reservedFrz` borrows untouched;
* `legacyDeallocCheck := true` is the unpatched `Trusted.hasProtectedLocalBorrow`
  rule in which every protected tag (including `.cell`) blocks deallocation.
The prototype semantics proper is `ProtoConfig.default` (`{}`). -/
structure ProtoConfig : Type where
  preserveReservedOnDirectWrite : Bool := false
  legacyDeallocCheck : Bool := false

/-- Depth of the active frame: `0` for the root frame. -/
def currentFrameDepth (s : ProtoMachineState) : Nat := s.memory.callStack.length

/-- `callStack` index of the saved frame at depth `d < depth`
(`callStack[depth - 1 - d]`; the most recent caller is at index `0`). -/
def frameIndexOfDepth (depth d : Nat) : Nat := depth - 1 - d

/-- Read `loc` in `locals`, falling back to the root frame's caller-owned
referent slots (`callerLocals`) when `d = 0` and `loc ≥ locals.length`. -/
def readSlotWithRootFallback (callerLocals : List LocalSlot) (d loc : Nat)
    (locals : List LocalSlot) : Option LocalSlot :=
  match get? locals loc with
  | .some slot => .some slot
  | .none =>
    match d with
    | 0 => get? callerLocals loc
    | _ + 1 => .none

/-- Frame-qualified local read at `(d, loc)` (`DIV-MR-CALL-TARGET-LOCAL`). -/
def readFrameLocalProto (s : ProtoMachineState) (d loc : Nat) : Option LocalSlot :=
  let depth := currentFrameDepth s
  if d = depth then readSlotWithRootFallback s.memory.callerLocals d loc s.frame.locals
  else if d < depth then
    match get? s.memory.callStack (frameIndexOfDepth depth d) with
    | .some sf => readSlotWithRootFallback s.memory.callerLocals d loc sf.frame.locals
    | .none => .none
  else .none

/-- Update a root-frame caller-owned referent slot. -/
def writeCallerLocalProto (s : ProtoMachineState) (d loc : Nat) (slot : LocalSlot) :
    Option ProtoMachineState :=
  match d with
  | 0 =>
    match set? s.memory.callerLocals loc slot with
    | .some cl => .some { s with memory := { s.memory with callerLocals := cl } }
    | .none => .none
  | _ + 1 => .none

/-- Frame-qualified local write at `(d, loc)` (`DIV-MR-CALL-TARGET-LOCAL`). -/
def writeFrameLocalProto (s : ProtoMachineState) (d loc : Nat) (slot : LocalSlot) :
    Option ProtoMachineState :=
  let depth := currentFrameDepth s
  if d = depth then
    match set? s.frame.locals loc slot with
    | .some locals' => .some { s with frame := { s.frame with locals := locals' } }
    | .none => writeCallerLocalProto s d loc slot
  else if d < depth then
    let idx := frameIndexOfDepth depth d
    match get? s.memory.callStack idx with
    | .some sf =>
      match set? sf.frame.locals loc slot with
      | .some locals' =>
        match set? s.memory.callStack idx { sf with frame := { sf.frame with locals := locals' } } with
        | .some stack' => .some { s with memory := { s.memory with callStack := stack' } }
        | .none => .none
      | .none => writeCallerLocalProto s d loc slot
    | .none => .none
  else .none

/-- Body executing in the frame at depth `d`. -/
def frameBodyAtDepth (s : ProtoMachineState) (d : Nat) : Option CapturedMir :=
  let depth := currentFrameDepth s
  if d = depth then .some s.body
  else if d < depth then
    match get? s.memory.callStack (frameIndexOfDepth depth d) with
    | .some sf => .some sf.callerBody
    | .none => .none
  else .none

/-- Look up the entry with provenance tag `tag`. -/
def lookupProtoBorrow : List ProtoBorrowEntry → Nat → Option ProtoBorrowEntry
  | .nil, _ => .none
  | e :: rest, tag =>
    match Nat.beq e.tag tag with
    | true => .some e
    | false => lookupProtoBorrow rest tag

/-- Fuel-bounded walk up the `parentTag` chain from `t` looking for `anc`. -/
def isAncestorOrSelfAux (borrows : List ProtoBorrowEntry) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, anc, t =>
    match Nat.beq t anc with
    | true => true
    | false =>
      match lookupProtoBorrow borrows t with
      | .some e =>
        match e.parentTag with
        | .some p => isAncestorOrSelfAux borrows fuel anc p
        | .none => false
      | .none => false

/-- `anc` is `t` or an ancestor of `t` in the borrow tree. An access through `t` is a
*local* (child) access for exactly these nodes and a *foreign* access for all others. -/
def isAncestorOrSelfProto (borrows : List ProtoBorrowEntry) (anc t : Nat) : Bool :=
  isAncestorOrSelfAux borrows (borrows.length + 1) anc t

/-- The entry's protector is currently active. -/
def isProtectedProto (prots : List Nat) (e : ProtoBorrowEntry) : Bool :=
  match e.protector with
  | .some p => natListContainsBool prots p
  | .none => false

/-- Frame-qualified target test `(targetFrameDepth, targetLocal) = (d, loc)`
(`DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`). -/
def entryTargetsProto (e : ProtoBorrowEntry) (d loc : Nat) : Bool :=
  Bool.and (Nat.beq e.targetFrameDepth d) (Nat.beq e.targetLocal loc)

/-- Per-node Tree Borrows transition of `e` for an access of `kind` to
`(d, loc, proj)` through `accessTag` (`none` = direct root access). Entries of other
frames, other locals, or disjoint sub-places are untouched. -/
def entryAccessTransitionProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (kind : TreeBorrowAccessKind) (d loc : Nat)
    (proj : List ProjectionElem) (accessTag : Option Nat) (e : ProtoBorrowEntry) :
    TreeBorrowTransition :=
  match Bool.and (entryTargetsProto e d loc) (projectionsOverlap e.targetProjection proj) with
  | false => .transition e.perm
  | true =>
    let prot := isProtectedProto prots e
    let rel : TreeBorrowRelatedness :=
      match accessTag with
      | .none => .foreignAccess
      | .some t =>
        match isAncestorOrSelfProto borrows e.tag t with
        | true => .localAccess
        | false => .foreignAccess
    match cfg.preserveReservedOnDirectWrite, accessTag, kind, e.perm, prot with
    | true, .none, .write, .reservedFrz c, false => .transition (.reservedFrz c)
    | _, _, _, _, _ => treeBorrowNodeAccess kind rel e.perm prot

/-- Apply a transition outcome (UB outcomes leave the entry unchanged; callers reject
them first). -/
def applyProtoTransition (e : ProtoBorrowEntry) : TreeBorrowTransition → ProtoBorrowEntry
  | .transition p => { e with perm := p }
  | .ub => e
  | .protectedReservedIM => e

/-- Some entry reports UB for the access. -/
def accessUBProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry) (prots : List Nat)
    (kind : TreeBorrowAccessKind) (d loc : Nat) (proj : List ProjectionElem)
    (accessTag : Option Nat) : Bool :=
  borrows.any (fun e =>
    treeBorrowTransitionIsUB (entryAccessTransitionProto cfg borrows prots kind d loc proj accessTag e))

/-- Borrow table after the access. -/
def accessUpdateProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry) (prots : List Nat)
    (kind : TreeBorrowAccessKind) (d loc : Nat) (proj : List ProjectionElem)
    (accessTag : Option Nat) : List ProtoBorrowEntry :=
  borrows.map (fun e =>
    applyProtoTransition e (entryAccessTransitionProto cfg borrows prots kind d loc proj accessTag e))

/-- Frame-scoped `updateBorrowPermAtProj`: the write transition of one entry for a write
to `(d, loc, proj)` through `writerTag`. -/
def updateBorrowPermAtProjProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) (proj : List ProjectionElem) (writerTag : Option Nat)
    (e : ProtoBorrowEntry) : ProtoBorrowEntry :=
  applyProtoTransition e (entryAccessTransitionProto cfg borrows prots .write d loc proj writerTag e)

/-- Frame-scoped `updateBorrowPerm` (whole-local write). -/
def updateBorrowPermProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) (writerTag : Option Nat) (e : ProtoBorrowEntry) :
    ProtoBorrowEntry :=
  updateBorrowPermAtProjProto cfg borrows prots d loc .nil writerTag e

/-- Frame-scoped `invalidateConflictingBorrowsAtProj`. -/
def invalidateConflictingBorrowsAtProjProto (cfg : ProtoConfig)
    (borrows : List ProtoBorrowEntry) (prots : List Nat) (d loc : Nat)
    (proj : List ProjectionElem) (writerTag : Option Nat) : List ProtoBorrowEntry :=
  borrows.map (updateBorrowPermAtProjProto cfg borrows prots d loc proj writerTag)

/-- Frame-scoped `invalidateConflictingBorrows` (whole-local write). -/
def invalidateConflictingBorrowsProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) (writerTag : Option Nat) : List ProtoBorrowEntry :=
  invalidateConflictingBorrowsAtProjProto cfg borrows prots d loc .nil writerTag

/-- Frame-scoped `hasProtectedWriteConflict`: some *protected* entry of `(d, loc)` would
become UB under the write (a protected `.cell` survives every write). -/
def hasProtectedWriteConflictProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) (writerTag : Option Nat)
    (proj : List ProjectionElem := .nil) : Bool :=
  borrows.any (fun e =>
    Bool.and (isProtectedProto prots e)
      (treeBorrowTransitionIsUB
        (entryAccessTransitionProto cfg borrows prots .write d loc proj writerTag e)))

/-- `MiniRustSpec.Interp.PermissionProt.prevents_deallocation` over Anneal's six states
(every Anneal entry has performed its initial local access, so `had_local_read = true`;
`.reservedIM`, which Miri never creates under a protector, fails closed). -/
def preventsDeallocation : TreeBorrowPerm → Bool
  | .cell => false
  | .reservedFrz _ => true
  | .reservedIM => true
  | .unique => true
  | .frozen => true
  | .disabled => false

/-- Deallocation-blocking rule (legacy mode: every protected tag blocks, as in the
unpatched `Trusted.hasProtectedLocalBorrow`). -/
def deallocBlockedBy (cfg : ProtoConfig) (p : TreeBorrowPerm) : Bool :=
  match cfg.legacyDeallocCheck with
  | true => true
  | false => preventsDeallocation p

/-- Frame-scoped `hasProtectedLocalBorrow` (`StorageDead` / `StorageLive`), exempting
permissions with `preventsDeallocation = false` (`DIV-MR-TB-UNSAFECELL-PROTECTED-IM`). -/
def hasProtectedLocalBorrowProto (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) : Bool :=
  borrows.any (fun e =>
    Bool.and (entryTargetsProto e d loc)
      (Bool.and (isProtectedProto prots e) (deallocBlockedBy cfg e.perm)))

/-- Frame-scoped `disableLocalBorrows` (`StorageDead` / `StorageLive`): disables every
borrow of `(d, loc)` and marks its backing allocation deallocated (`allocDead := true`)
so a subsequent `StorageLive(loc)` revival cannot make stale pointers appear live for
non-zero `BinOp.offset`. -/
def disableLocalBorrowsProto (borrows : List ProtoBorrowEntry) (d loc : Nat) :
    List ProtoBorrowEntry :=
  borrows.map (fun e =>
    match entryTargetsProto e d loc with
    | true => { e with perm := .disabled, allocDead := true }
    | false => e)

/-- `Return` deallocation check across the returning frame's locals
`0 .. nLocals - 1` at depth `d` (`DIV-MR-TB-FNENTRY-LOCAL-DEALLOC`). -/
def hasFrameDeallocProtectorConflictProto (cfg : ProtoConfig)
    (borrows : List ProtoBorrowEntry) (prots : List Nat) (d nLocals : Nat) : Bool :=
  (List.range nLocals).any (hasProtectedLocalBorrowProto cfg borrows prots d)

/-- Disable every entry targeting a local `< nLocals` of the frame at depth `d` and mark
its backing allocation deallocated (`allocDead := true`). -/
def disableFrameBorrowsProto (borrows : List ProtoBorrowEntry) (d nLocals : Nat) :
    List ProtoBorrowEntry :=
  borrows.map (fun e =>
    match Bool.and (Nat.beq e.targetFrameDepth d) (Nat.blt e.targetLocal nLocals) with
    | true => { e with perm := .disabled, allocDead := true }
    | false => e)

/-! ## §3. The prototype interpreter -/

/-- Result of evaluating an operand / rvalue / place read. -/
inductive ProtoValResult : Type where
  | ok (v : Value) (s : ProtoMachineState) : ProtoValResult
  | ub : ProtoValResult
  | unsupported : ProtoValResult

/-- Result of evaluating a list of operands. -/
inductive ProtoValsResult : Type where
  | ok (vs : List Value) (s : ProtoMachineState) : ProtoValsResult
  | ub : ProtoValsResult
  | unsupported : ProtoValsResult

/-- Result of a place write. -/
inductive ProtoStateResult : Type where
  | ok (s : ProtoMachineState) : ProtoStateResult
  | ub : ProtoStateResult
  | unsupported : ProtoStateResult

/-- One machine step. -/
inductive ProtoStep : Type where
  | step (s : ProtoMachineState) : ProtoStep
  | ret (v : Value) (mem : ProtoMemory) : ProtoStep
  | ub : ProtoStep
  | unsupported : ProtoStep

/-- Terminal outcome of `runMirProto`. -/
inductive ProtoOutcome : Type where
  | ok (v : Value) : ProtoOutcome
  | ub : ProtoOutcome
  | unsupported : ProtoOutcome
  | outOfFuel : ProtoOutcome

/-- Scalar projection of an outcome (for kernel `decide`). -/
def ProtoOutcome.okScalar? : ProtoOutcome → Option (Nat × Nat)
  | .ok (.scalar sc) => .some (sc.bits, sc.sizeBytes)
  | _ => .none

/-- `true` iff the outcome is `.ub`. -/
def ProtoOutcome.isUB : ProtoOutcome → Bool
  | .ub => true
  | _ => false

theorem ProtoOutcome.eq_of_okScalar? {r : ProtoOutcome} {b n : Nat}
    (h : r.okScalar? = .some (b, n)) : r = .ok (.scalar ⟨b, n⟩) := by
  cases r with
  | ok v =>
    cases v with
    | scalar sc =>
      simp only [ProtoOutcome.okScalar?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      cases sc
      simp only at h1 h2
      subst h1; subst h2; rfl
    | _ => simp [ProtoOutcome.okScalar?] at h
  | _ => simp [ProtoOutcome.okScalar?] at h

theorem ProtoOutcome.eq_ub_of_isUB {r : ProtoOutcome} (h : r.isUB = true) : r = .ub := by
  cases r <;> simp_all [ProtoOutcome.isUB]

/-- `Nat.ble` as a decision procedure. -/
theorem nat_ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; exact Bool.noConfusion h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

/-- `Nat.beq` as a decision procedure. -/
theorem nat_beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · have : a ≠ b := fun he => by rw [he, Nat.beq_refl] at h; exact Bool.noConfusion h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

/-- Typed-load validity (`validateLoadedValue` extended with the `char` Unicode scalar
check, `DIV-LM-RAW-OVERWRITE-CHAR-COPY`). Applied to every `copy`/`move` operand load. -/
def validateLoadedValueProto (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Operand) (v : Value) : Bool :=
  match op with
  | .constant _ => true
  | .copy _ | .move _ =>
    match operandTy localDecls layouts op with
    | .some ty =>
      match ty.kind with
      | .bool =>
        match v with
        | .scalar sc => Bool.or (Nat.beq sc.bits 0) (Nat.beq sc.bits 1)
        | _ => false
      | .char =>
        match v with
        | .scalar sc => Bool.and (Nat.beq sc.sizeBytes 4) (isValidCharCode sc.bits)
        | _ => false
      | _ => true
    | .none => true

/-- Field/downcast-only projection (the sub-places the prototype can borrow). -/
def isFieldOnlyProj : List ProjectionElem → Bool
  | .nil => true
  | .field _ _ :: rest => isFieldOnlyProj rest
  | .downcast _ _ :: rest => isFieldOnlyProj rest
  | _ :: _ => false

/-- Commit `newRoot` into `(d, loc)` and install `borrows'`. -/
def commitFrameWriteProto (s : ProtoMachineState) (d loc : Nat) (newRoot : Value)
    (borrows' : List ProtoBorrowEntry) : ProtoStateResult :=
  match writeFrameLocalProto s d loc (.init newRoot) with
  | .some s' => .ok { s' with memory := { s'.memory with borrows := borrows' } }
  | .none => .ub

/-- Place read (copy semantics). Deref reads are frame-qualified
(`DIV-MR-CALL-TARGET-LOCAL`) and perform a Tree Borrows read access through the
pointer's tag. Direct local reads do not touch the borrow table (as in `Trusted`). -/
def readPlaceProto (cfg : ProtoConfig) (s : ProtoMachineState) (p : Place) : ProtoValResult :=
  match p.projection with
  | .deref :: rest =>
    match get? s.frame.locals p.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupProtoBorrow s.memory.borrows ptrVal.tag with
      | .none => .unsupported
      | .some entry =>
        let fullProj := appendProjections entry.targetProjection rest
        let d := entry.targetFrameDepth
        let loc := entry.targetLocal
        let prots := s.memory.activeProtectors
        match accessUBProto cfg s.memory.borrows prots .read d loc fullProj (.some ptrVal.tag) with
        | true => .ub
        | false =>
          match Nat.beq ptrVal.offsetBytes 0 with
          | false => .unsupported
          | true =>
            match readFrameLocalProto s d loc with
            | .some (.init rootVal) =>
              match readProjectedValue s.frame.locals rootVal fullProj with
              | .ok v =>
                .ok v { s with memory := { s.memory with
                  borrows := accessUpdateProto cfg s.memory.borrows prots .read d loc fullProj
                    (.some ptrVal.tag) } }
              | .ub => .ub
              | .unsupported => .unsupported
            | _ => .ub
    | .some (.init _) => .unsupported
    | _ => .ub
  | proj =>
    match projectionHasDeref proj with
    | true => .unsupported
    | false =>
      match get? s.frame.locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue s.frame.locals rootVal proj with
        | .ok v => .ok v s
        | .ub => .ub
        | .unsupported => .unsupported
      | _ => .ub

/-- Place write. Deref writes are frame-qualified and perform a Tree Borrows write
access through the pointer's tag; direct writes are foreign writes to every borrow of
`(currentFrameDepth s, loc)` (and to no other frame's borrows). -/
def writePlaceProto (cfg : ProtoConfig) (s : ProtoMachineState) (p : Place) (v : Value) :
    ProtoStateResult :=
  match p.projection with
  | .deref :: rest =>
    match get? s.frame.locals p.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupProtoBorrow s.memory.borrows ptrVal.tag with
      | .none => .unsupported
      | .some entry =>
        let fullProj := appendProjections entry.targetProjection rest
        let d := entry.targetFrameDepth
        let loc := entry.targetLocal
        let prots := s.memory.activeProtectors
        match accessUBProto cfg s.memory.borrows prots .write d loc fullProj (.some ptrVal.tag) with
        | true => .ub
        | false =>
          match Nat.beq ptrVal.offsetBytes 0 with
          | false => .unsupported
          | true =>
            let borrows' :=
              accessUpdateProto cfg s.memory.borrows prots .write d loc fullProj (.some ptrVal.tag)
            match readFrameLocalProto s d loc with
            | .some (.init rootVal) =>
              match writeProjectedValue s.frame.locals rootVal fullProj v with
              | .ok newRoot => commitFrameWriteProto s d loc newRoot borrows'
              | .ub => .ub
              | .unsupported => .unsupported
            | .some .uninit =>
              match fullProj with
              | .nil => commitFrameWriteProto s d loc v borrows'
              | _ :: _ => .ub
            | _ => .ub
    | .some (.init _) => .unsupported
    | _ => .ub
  | proj =>
    match projectionHasDeref proj with
    | true => .unsupported
    | false =>
      let d := currentFrameDepth s
      let loc := p.local_
      let prots := s.memory.activeProtectors
      match get? s.frame.locals loc with
      | .none => .ub
      | .some .dead => .ub
      | .some slot =>
        match hasProtectedWriteConflictProto cfg s.memory.borrows prots d loc .none proj with
        | true => .ub
        | false =>
          let borrows' := invalidateConflictingBorrowsAtProjProto cfg s.memory.borrows prots d loc proj .none
          match proj with
          | .nil => commitFrameWriteProto s d loc v borrows'
          | pe :: restProj =>
            match slot with
            | .init rootVal =>
              match writeProjectedValue s.frame.locals rootVal proj v with
              | .ok newRoot => commitFrameWriteProto s d loc newRoot borrows'
              | .ub => .ub
              | .unsupported => .unsupported
            | .uninit =>
              match uninitFieldWriteShell? s.body.localDecls s.body.layouts loc pe restProj with
              | .some shell =>
                match writeProjectedValue s.frame.locals shell proj v with
                | .ok newRoot => commitFrameWriteProto s d loc newRoot borrows'
                | .ub => .ub
                | .unsupported => .unsupported
              | .none => .ub
            | .dead => .ub

/-- Operand evaluation. Every `copy`/`move` load is validated by
`validateLoadedValueProto`; `move` of a whole local deinitializes it. -/
def evalOperandProto (cfg : ProtoConfig) (s : ProtoMachineState) (op : Operand) : ProtoValResult :=
  match op with
  | .constant c =>
    match evalConstValue c.val c.ty .nil s.body.layouts with
    | .some v => .ok v s
    | .none => .unsupported
  | .copy p =>
    match readPlaceProto cfg s p with
    | .ok v s' =>
      match validateLoadedValueProto s.body.localDecls s.body.layouts op v with
      | true => .ok v s'
      | false => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | .move p =>
    match p.projection with
    | .nil =>
      match get? s.frame.locals p.local_ with
      | .some (.init v) =>
        match validateLoadedValueProto s.body.localDecls s.body.layouts op v with
        | true =>
          match set? s.frame.locals p.local_ .uninit with
          | .some locals' => .ok v { s with frame := { s.frame with locals := locals' } }
          | .none => .ub
        | false => .ub
      | _ => .ub
    | _ :: _ =>
      match readPlaceProto cfg s p with
      | .ok v s' =>
        match validateLoadedValueProto s.body.localDecls s.body.layouts op v with
        | true => .ok v s'
        | false => .ub
      | .ub => .ub
      | .unsupported => .unsupported

/-- Left-to-right evaluation of call arguments / aggregate fields. -/
def evalOperandsProto (cfg : ProtoConfig) (s : ProtoMachineState) : List Operand → ProtoValsResult
  | .nil => .ok .nil s
  | op :: ops =>
    match evalOperandProto cfg s op with
    | .ok v s₁ =>
      match evalOperandsProto cfg s₁ ops with
      | .ok vs s₂ => .ok (v :: vs) s₂
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

/-- Perm-independent allocation byte bound of a whole-local borrow: the byte size of
the target local in its owning frame when the entry's allocation has not been freed
(`entry.allocDead = false`) and the slot is live (`.init _` or `.uninit`), `0` when
deallocated or dead, and `none` (unsupported) for sub-place borrows or unknown layouts. -/
def ptrAllocByteBoundProto (s : ProtoMachineState) (entry : ProtoBorrowEntry) : Option Nat :=
  match entry.targetProjection with
  | .nil =>
    match entry.allocDead, readFrameLocalProto s entry.targetFrameDepth entry.targetLocal with
    | false, .some (.init _) | false, .some .uninit =>
      match frameBodyAtDepth s entry.targetFrameDepth with
      | .some b =>
        match get? b.localDecls entry.targetLocal with
        | .some decl => rigidTyByteSize b.layouts decl.ty
        | .none => .none
      | .none => .none
    | _, _ => .some 0
  | _ :: _ => .none

/-- `BinOp.Offset` decoupled from Tree Borrows permissions
(`DIV-LM-D6-OFFSET-DISABLED-TAG`): only `evalBinOpOffset`'s live-allocation bounds
and `isize` overflow checks apply; the tag is preserved. A zero byte delta (`count == 0`
or `stride == 0`) is valid at any `offsetBytes < 2^63` even after the allocation is dead
(`WitLM3_1.lm31OffsetDisabledDeadZeroBody`); a non-zero byte delta requires a live
allocation (`entry.allocDead = false`, so `StorageDead`+`StorageLive` revival rejects
non-zero offsets on stale tags). A `.disabled` tag is rejected later, at dereference. -/
def evalPtrOffsetBinOpProto (s : ProtoMachineState) (lhsOp : Operand) (ptrVal : ProvenancePtr)
    (sz : Nat) (offsetSc : ScalarInt) : ProtoValResult :=
  match lookupProtoBorrow s.memory.borrows ptrVal.tag with
  | .none => .unsupported
  | .some entry =>
    match pointeeElemByteStride s.body.localDecls s.body.layouts lhsOp with
    | .none => .ub
    | .some stride =>
      match ptrAllocByteBoundProto s entry with
      | .none => .unsupported
      | .some bound =>
        let ptrBytes := layoutPointerBytes s.body.layouts
        let effBound : Option Nat :=
          match Bool.and (Nat.beq bound 0)
            (Bool.or (Nat.beq (wrapScalarBits offsetSc.bits (scalarModulus ptrBytes)) 0)
              (Nat.beq stride 0)) with
          | true => .none
          | false => .some bound
        match evalBinOpOffset ptrVal sz offsetSc stride effBound ptrBytes with
        | .some p' => .ok (.ptr p' sz) s
        | .none => .ub

/-- Float format of a MIR float type (`f16` / `f128` are unsupported). -/
def ieeeFormatOfTy? (ty : Ty) : Option IeeeFormat :=
  match ty.kind with
  | .float .f32 => .some .binary32
  | .float .f64 => .some .binary64
  | _ => .none

/-- Integer target of a MIR integer type. -/
def intTargetOfTy? (ty : Ty) : Option IntTarget :=
  match ty.kind with
  | .int w => .some (.signed w)
  | .uint w => .some (.unsigned w)
  | _ => .none

/-- Pointer width of a layout table. -/
def ptrWidthOfLayouts (layouts : LayoutTable) : PtrWidth :=
  match layoutPointerBytes layouts with
  | 4 => .bits32
  | _ => .bits64

/-- `CastKind.{floatToInt, intToFloat, floatToFloat}` (Part B wiring). -/
def evalFloatCastProto (kind : CastKind) (srcTy? : Option Ty) (targetTy : Ty)
    (layouts : LayoutTable) (v : Value) : Option Value :=
  match kind, srcTy?, v with
  | .floatToInt, .some srcTy, .scalar sc =>
    match ieeeFormatOfTy? srcTy, intTargetOfTy? targetTy with
    | .some fmt, .some tgt =>
      match Nat.beq sc.sizeBytes fmt.byteWidth with
      | true => .some (.scalar (evalFloatToIntSaturating fmt sc.bits tgt (ptrWidthOfLayouts layouts)))
      | false => .none
    | _, _ => .none
  | .intToFloat, .some srcTy, .scalar sc =>
    match intTargetOfTy? srcTy, ieeeFormatOfTy? targetTy with
    | .some tgt, .some fmt =>
      let w := tgt.bitWidth (ptrWidthOfLayouts layouts)
      match Nat.beq (sc.sizeBytes * 8) w with
      | true => .some (.scalar ⟨evalIntToFloatRoundTiesToEven tgt.isSigned w sc.bits fmt, fmt.byteWidth⟩)
      | false => .none
    | _, _ => .none
  | .floatToFloat, .some srcTy, .scalar sc =>
    match ieeeFormatOfTy? srcTy, ieeeFormatOfTy? targetTy with
    | .some src, .some dst =>
      match Nat.beq sc.sizeBytes src.byteWidth with
      | true => .some (.scalar ⟨evalFloatToFloatRoundTiesToEven src dst sc.bits, dst.byteWidth⟩)
      | false => .none
    | _, _ => .none
  | _, _, _ => .none

/-- Rvalue evaluation. -/
def evalRvalueProto (cfg : ProtoConfig) (s : ProtoMachineState) (rv : Rvalue) : ProtoValResult :=
  let decls := s.body.localDecls
  let layouts := s.body.layouts
  match rv with
  | .use op | .wrapUnsafeBinder op _ => evalOperandProto cfg s op
  | .copyForDeref place =>
    -- `Trusted.evalRvalue .copyForDeref`: an unvalidated copy of the (pointer) place.
    readPlaceProto cfg s place
  | .repeat op count =>
    match evalOperandProto cfg s op with
    | .ok v s₁ => .ok (.aggregate 0 (replicateValue count v)) s₁
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp .not op =>
    match evalOperandProto cfg s op with
    | .ok (.scalar sc) s₁ =>
      match evalUnaryNot sc (operandTy decls layouts op) s₁.frame.locals emptyMemory with
      | .ok v _ _ => .ok v s₁
      | .ub => .ub
      | .unsupported => .unsupported
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .unaryOp .neg op =>
    match evalOperandProto cfg s op with
    | .ok (.scalar sc) s₁ =>
      match Nat.beq sc.sizeBytes 0 with
      | true => .unsupported
      | false =>
        let modulus := scalarModulus sc.sizeBytes
        let canonical := wrapScalarBits sc.bits modulus
        .ok (.scalar ⟨wrapScalarBits (Nat.sub modulus canonical) modulus, sc.sizeBytes⟩) s₁
    | .ok _ _ => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .binaryOp op lhsOp rhsOp =>
    match evalOperandProto cfg s lhsOp with
    | .ok lhsVal s₁ =>
      match evalOperandProto cfg s₁ rhsOp with
      | .ok rhsVal s₂ =>
        match lhsVal, rhsVal with
        | .ptr ptrVal sz, .scalar offsetSc =>
          match op with
          | .offset => evalPtrOffsetBinOpProto s₂ lhsOp ptrVal sz offsetSc
          | _ => .unsupported
        | .scalar lhs, .scalar rhs =>
          match op with
          | .offset => .unsupported
          | _ =>
            match evalScalarBinOp op lhs rhs .nil {} (operandIsSigned decls lhsOp layouts) with
            | .ok v _ _ => .ok v s₂
            | .ub => .ub
            | .unsupported => .unsupported
        | _, _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .ref bk place =>
    let perm :=
      match bk with
      | .shared => sharedBorrowPerm decls layouts place
      | .mut _ => mutableBorrowPerm decls layouts place
    match place.projection with
    | .deref :: rest =>
      match get? s.frame.locals place.local_ with
      | .some (.init (.ptr ptrVal sz)) =>
        match lookupProtoBorrow s.memory.borrows ptrVal.tag with
        | .none => .unsupported
        | .some parent =>
          let eagerReject : Bool :=
            match parent.perm, bk with
            | .disabled, _ => true
            | .frozen, .mut _ => true
            | _, _ => false
          match eagerReject with
          | true => .ub
          | false =>
            -- Safe references need an aligned, dereferenceable address; the overlay models
            -- no sub-local byte offsets, so `&*p` with `offsetBytes ≠ 0` fails closed
            -- (e.g. `RefWitness.misalignedRef`, where MiniRust and `Trusted` raise UB).
            match Bool.and (isFieldOnlyProj rest) (Nat.beq ptrVal.offsetBytes 0) with
            | false => .unsupported
            | true =>
              let fullProj := appendProjections parent.targetProjection rest
              let d := parent.targetFrameDepth
              let loc := parent.targetLocal
              let prots := s.memory.activeProtectors
              let skipRead : Bool := match perm with | .cell => true | _ => false
              let readUB : Bool :=
                match skipRead with
                | true => false
                | false => accessUBProto cfg s.memory.borrows prots .read d loc fullProj (.some ptrVal.tag)
              match readUB with
              | true => .ub
              | false =>
                match readFrameLocalProto s d loc with
                | .none => .ub
                | .some .dead => .ub
                | .some _ =>
                  let borrows₁ :=
                    match skipRead with
                    | true => s.memory.borrows
                    | false => accessUpdateProto cfg s.memory.borrows prots .read d loc fullProj (.some ptrVal.tag)
                  let tag := s.memory.nextTag
                  let child : ProtoBorrowEntry :=
                    { tag := tag, targetLocal := loc, targetProjection := fullProj, perm := perm,
                      parentTag := .some ptrVal.tag, targetFrameDepth := d }
                  .ok (.ptr { allocId := tag, offsetBytes := ptrVal.offsetBytes } sz)
                    { s with memory := { s.memory with borrows := child :: borrows₁, nextTag := tag + 1 } }
      | .some (.init _) => .unsupported
      | _ => .ub
    | proj =>
      match isFieldOnlyProj proj with
      | false => .unsupported
      | true =>
        match get? s.frame.locals place.local_ with
        | .none => .ub
        | .some .dead => .ub
        | .some _ =>
          let tag := s.memory.nextTag
          let entry : ProtoBorrowEntry :=
            { tag := tag, targetLocal := place.local_, targetProjection := proj, perm := perm,
              targetFrameDepth := currentFrameDepth s }
          .ok (.ptr { allocId := tag, offsetBytes := 0 } 8)
            { s with memory := { s.memory with borrows := entry :: s.memory.borrows, nextTag := tag + 1 } }
  | .rawPtr mutability place =>
    let perm :=
      match mutability with
      | .not => sharedBorrowPerm decls layouts place
      | .mut => TreeBorrowPerm.unique
    let ptrBytes := layoutPointerBytes layouts
    match place.projection with
    | .deref :: rest =>
      match get? s.frame.locals place.local_ with
      | .some (.init (.ptr ptrVal sz)) =>
        match lookupProtoBorrow s.memory.borrows ptrVal.tag with
        | .none => .unsupported
        | .some parent =>
          match parent.perm with
          | .disabled => .ub
          | _ =>
            match isFieldOnlyProj rest with
            | false => .unsupported
            | true =>
              let tag := s.memory.nextTag
              let child : ProtoBorrowEntry :=
                { tag := tag, targetLocal := parent.targetLocal,
                  targetProjection := appendProjections parent.targetProjection rest,
                  perm := perm, parentTag := .some ptrVal.tag,
                  targetFrameDepth := parent.targetFrameDepth }
              .ok (.ptr { allocId := tag, offsetBytes := ptrVal.offsetBytes } sz)
                { s with memory := { s.memory with borrows := child :: s.memory.borrows, nextTag := tag + 1 } }
      | .some (.init _) => .unsupported
      | _ => .ub
    | proj =>
      match isFieldOnlyProj proj with
      | false => .unsupported
      | true =>
        match get? s.frame.locals place.local_ with
        | .none => .ub
        | .some .dead => .ub
        | .some _ =>
          let tag := s.memory.nextTag
          let entry : ProtoBorrowEntry :=
            { tag := tag, targetLocal := place.local_, targetProjection := proj, perm := perm,
              targetFrameDepth := currentFrameDepth s }
          .ok (.ptr { allocId := tag, offsetBytes := 0 } ptrBytes)
            { s with memory := { s.memory with borrows := entry :: s.memory.borrows, nextTag := tag + 1 } }
  | .discriminant place =>
    -- Layout-aware discriminant (`Trusted.evalPlaceDiscriminant`: single-variant layouts,
    -- variant bounds, `core::cmp::Ordering` encoding, scalar-represented enums).
    match readPlaceProto cfg s place with
    | .ok val s₁ =>
      match evalPlaceDiscriminant val s₁.frame.locals emptyMemory place decls layouts with
      | .ok v _ _ => .ok v s₁
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .cast kind op targetTy =>
    match kind with
    | .floatToInt | .intToFloat | .floatToFloat =>
      match evalOperandProto cfg s op with
      | .ok v s₁ =>
        match evalFloatCastProto kind (operandTy decls layouts op) targetTy layouts v with
        | .some v' => .ok v' s₁
        | .none => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .intToInt =>
      -- `Trusted.evalRvalue (.cast .intToInt ..)`: wrap / sign-extend to the target width.
      match evalOperandProto cfg s op with
      | .ok (.scalar sc) s₁ =>
        match Nat.beq sc.sizeBytes 0 with
        | true => .unsupported
        | false =>
          match intCastTargetBytes targetTy.kind with
          | .some targetBytes =>
            let modulus := scalarModulus targetBytes
            let castedBits :=
              match operandIsSigned decls op layouts with
              | false => wrapScalarBits sc.bits modulus
              | true =>
                match Nat.ble targetBytes sc.sizeBytes with
                | true => wrapScalarBits sc.bits modulus
                | false => signExtendBits sc.bits sc.sizeBytes targetBytes
            .ok (.scalar ⟨castedBits, targetBytes⟩) s₁
          | .none => .unsupported
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | .ptrToPtr =>
      -- Thin raw-pointer casts keep the provenance tag (`Trusted.evalCastPtrToPtr`); the
      -- array-element re-derivation and wide-pointer cases fail closed.
      match evalOperandProto cfg s op with
      | .ok (.ptr ptrVal sz) s₁ =>
        match Nat.beq sz (layoutPointerBytes layouts) with
        | false => .ub
        | true =>
          match thinRawPtrPointee? targetTy with
          | .none => .ub
          | .some dstElem =>
            match arrayPtrOrRefElemLen? (operandTy decls layouts op) dstElem with
            | .some _ => .unsupported
            | .none => .ok (.ptr ptrVal sz) s₁
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported
    | _ => .unsupported
  | .aggregate .tuple ops | .aggregate (.array _) ops | .aggregate (.closure _) ops =>
    match evalOperandsProto cfg s ops with
    | .ok vals s₁ => .ok (.aggregate 0 vals) s₁
    | .ub => .ub
    | .unsupported => .unsupported
  | .aggregate (.adt _ variantIdx .none) ops =>
    match evalOperandsProto cfg s ops with
    | .ok vals s₁ => .ok (.aggregate variantIdx vals) s₁
    | .ub => .ub
    | .unsupported => .unsupported
  | _ => .unsupported

/-- Advance to the next statement. -/
def advanceStmtProto (s : ProtoMachineState) : ProtoMachineState :=
  { s with frame := { s.frame with stmtIdx := s.frame.stmtIdx + 1 } }

/-- `StorageLive` / `StorageDead`: deallocation of `(currentFrameDepth s, loc)`. -/
def evalStorageProto (cfg : ProtoConfig) (s : ProtoMachineState) (loc : Nat)
    (newSlot : LocalSlot) : ProtoStep :=
  match get? s.frame.locals loc with
  | .none => .ub
  | .some _ =>
    let d := currentFrameDepth s
    match hasProtectedLocalBorrowProto cfg s.memory.borrows s.memory.activeProtectors d loc with
    | true => .ub
    | false =>
      match set? s.frame.locals loc newSlot with
      | .some locals' =>
        .step (advanceStmtProto
          { s with
            frame := { s.frame with locals := locals' }
            memory := { s.memory with borrows := disableLocalBorrowsProto s.memory.borrows d loc } })
      | .none => .ub

/-- `SetDiscriminant` on a declared ADT (or undeclared) local. -/
def setDiscrDeclOk (decls : List LocalDecl) (loc : Nat) : Bool :=
  match get? decls loc with
  | .some decl =>
    match decl.ty.kind with
    | .adt _ _ => true
    | _ => false
  | .none => true

/-- `SetDiscriminant(loc, variantIdx)` (`DIV-LM-ENUM-SET-DISCR-UNINIT`): an `.uninit`
enum local becomes `.init (.aggregate variantIdx [])` (the tag is written, every payload
field stays uninitialized); an initialized aggregate keeps its fields. Both paths check
protector conflicts and run the frame-scoped foreign-write invalidation. -/
def evalSetDiscriminantProto (cfg : ProtoConfig) (s : ProtoMachineState) (loc variantIdx : Nat) :
    ProtoStep :=
  let d := currentFrameDepth s
  let prots := s.memory.activeProtectors
  let commit (fields : List Value) : ProtoStep :=
    match hasProtectedWriteConflictProto cfg s.memory.borrows prots d loc .none with
    | true => .ub
    | false =>
      match set? s.frame.locals loc (.init (.aggregate variantIdx fields)) with
      | .some locals' =>
        .step (advanceStmtProto
          { s with
            frame := { s.frame with locals := locals' }
            memory := { s.memory with
              borrows := invalidateConflictingBorrowsProto cfg s.memory.borrows prots d loc .none } })
      | .none => .ub
  match get? s.frame.locals loc with
  | .some .uninit =>
    match setDiscrDeclOk s.body.localDecls loc with
    | true => commit .nil
    | false => .unsupported
  | .some (.init (.aggregate _ fields)) => commit fields
  | .some (.init _) => .ub
  | .some .dead => .ub
  | .none => .ub

/-- `Retag(kind, place)` on a whole-local reference place: creates a child of the
pointer's entry inheriting `(targetFrameDepth, targetLocal)`; `fnEntry` attaches a fresh
protector. -/
def evalRetagProto (cfg : ProtoConfig) (s : ProtoMachineState) (kind : RetagKind)
    (place : Place) : ProtoStep :=
  match place.projection with
  | _ :: _ => .unsupported
  | .nil =>
    match placeTy s.body.localDecls s.body.layouts place with
    | .some { kind := .rawPtr _ _, .. } =>
      match get? s.frame.locals place.local_, kind with
      | .some (.init _), .raw => .step (advanceStmtProto s)
      | _, _ => .ub
    | .some { kind := .ref mutability pointee, .. } =>
      match rigidTyIsUninhabited 16 pointee with
      | true => .ub
      | false =>
        match get? s.frame.locals place.local_ with
        | .some (.init (.ptr ptrVal sz)) =>
          match lookupProtoBorrow s.memory.borrows ptrVal.tag with
          | .none => .unsupported
          | .some parent =>
            match parent.perm with
            | .disabled => .ub
            | _ =>
              let childPerm := retagPerm kind mutability pointee
              let skipRead : Bool :=
                match childPerm with
                | .cell => true
                | _ => rigidTyIsZeroSized 16 pointee
              let d := parent.targetFrameDepth
              let loc := parent.targetLocal
              let prots := s.memory.activeProtectors
              let readUB : Bool :=
                match skipRead with
                | true => false
                | false =>
                  accessUBProto cfg s.memory.borrows prots .read d loc parent.targetProjection (.some ptrVal.tag)
              match readUB with
              | true => .ub
              | false =>
                let borrows₁ :=
                  match skipRead with
                  | true => s.memory.borrows
                  | false =>
                    accessUpdateProto cfg s.memory.borrows prots .read d loc parent.targetProjection
                      (.some ptrVal.tag)
                let protId := s.memory.nextProtector
                let isFnEntry : Bool := match kind with | .fnEntry => true | _ => false
                let tag := s.memory.nextTag
                let child : ProtoBorrowEntry :=
                  { tag := tag, targetLocal := loc, targetProjection := parent.targetProjection,
                    perm := childPerm,
                    protector := match isFnEntry with | true => .some protId | false => .none,
                    parentTag := .some ptrVal.tag, targetFrameDepth := d }
                match set? s.frame.locals place.local_
                    (.init (.ptr { allocId := tag, offsetBytes := ptrVal.offsetBytes } sz)) with
                | .some locals' =>
                  .step (advanceStmtProto
                    { s with
                      frame := { s.frame with locals := locals' }
                      memory := { s.memory with
                        borrows := child :: borrows₁
                        nextTag := tag + 1
                        activeProtectors :=
                          match isFnEntry with
                          | true => protId :: prots
                          | false => prots
                        nextProtector :=
                          match isFnEntry with
                          | true => protId + 1
                          | false => protId } })
                | .none => .ub
        | .some (.init _) => .unsupported
        | _ => .ub
    | .some _ =>
      match get? s.frame.locals place.local_ with
      | .some (.init (.ptr _ _)) => .unsupported
      | .some (.init v) =>
        match validateLoadedValueProto s.body.localDecls s.body.layouts (.copy place) v with
        | true => .step (advanceStmtProto s)
        | false => .ub
      | _ => .ub
    | .none => .unsupported

/-- Statement evaluation. -/
def evalStmtProto (cfg : ProtoConfig) (s : ProtoMachineState) (stmt : Statement) : ProtoStep :=
  match stmt.kind with
  | .nop => .step (advanceStmtProto s)
  | .coverage => .step (advanceStmtProto s)
  | .constEvalCounter => .step (advanceStmtProto s)
  | .storageLive loc => evalStorageProto cfg s loc .uninit
  | .storageDead loc => evalStorageProto cfg s loc .dead
  | .assign dst rv =>
    match evalRvalueProto cfg s rv with
    | .ok v s₁ =>
      match writePlaceProto cfg s₁ dst v with
      | .ok s₂ => .step (advanceStmtProto s₂)
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported
  | .setDiscriminant p variantIdx =>
    match p.projection with
    | .nil => evalSetDiscriminantProto cfg s p.local_ variantIdx
    | _ :: _ => .unsupported
  | .retag kind place => evalRetagProto cfg s kind place
  | .backwardIncompatibleDropHint _ => .step (advanceStmtProto s)
  | .deinit p =>
    -- `Trusted.evalStmt .deinit` on the active frame.
    match p.projection with
    | .nil =>
      match get? s.frame.locals p.local_ with
      | .some .dead => .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' => .step (advanceStmtProto { s with frame := { s.frame with locals := locals' } })
        | .none => .ub
      | .none => .ub
    | proj :: rest =>
      match projectionHasDeref (proj :: rest) with
      | true => .unsupported
      | false =>
        match get? s.frame.locals p.local_ with
        | .some (.init rootVal) =>
          match readProjectedValue s.frame.locals rootVal (proj :: rest) with
          | .ok _ => .step (advanceStmtProto s)
          | .ub => .ub
          | .unsupported => .unsupported
        | _ => .ub
  | .placeMention place =>
    -- `Trusted.evalStmt .placeMention`: the root local must be live and every index
    -- operand initialized; no memory access is performed.
    match get? s.frame.locals place.local_ with
    | .none => .ub
    | .some .dead => .ub
    | .some rootSlot =>
      match placeMentionOperandsInit s.frame.locals rootSlot place.projection with
      | true => .step (advanceStmtProto s)
      | false => .ub
  | .intrinsic (.assume op) =>
    -- `Trusted.evalStmt (.intrinsic (.assume op))`: `op` must evaluate to `true`.
    match evalOperandProto cfg s op with
    | .ok (.scalar sc) s₁ =>
      match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
      | true => .step (advanceStmtProto s₁)
      | false => .ub
    | .ok _ _ => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | _ => .unsupported

/-- Find an inline callee body by `defPath`. -/
def findCalleeProto : List CapturedMir → DefPath → Option CapturedMir
  | .nil, _ => .none
  | b :: rest, dp =>
    match stringEq b.defPath dp with
    | true => .some b
    | false => findCalleeProto rest dp

/-- `Return`: check the returning frame's protector-deallocation conflicts
(`DIV-MR-TB-FNENTRY-LOCAL-DEALLOC`, exempting `.cell` per
`DIV-MR-TB-UNSAFECELL-PROTECTED-IM`), disable every borrow of the returning frame,
*then* release its protectors, pop it, and assign `_0` to the caller's destination. -/
def evalReturnProto (cfg : ProtoConfig) (s : ProtoMachineState) : ProtoStep :=
  match get? s.frame.locals 0 with
  | .some (.init retVal) =>
    let d := currentFrameDepth s
    let n := s.frame.locals.length
    match hasFrameDeallocProtectorConflictProto cfg s.memory.borrows s.memory.activeProtectors d n with
    | true => .ub
    | false =>
      let borrows₁ := disableFrameBorrowsProto s.memory.borrows d n
      match s.memory.callStack with
      | .nil => .ret retVal { s.memory with borrows := borrows₁ }
      | caller :: rest =>
        let s₁ : ProtoMachineState :=
          { body := caller.callerBody
            frame := { caller.frame with blockIdx := caller.returnTarget, stmtIdx := 0 }
            memory := { s.memory with
              borrows := borrows₁
              callStack := rest
              activeProtectors := caller.savedProtectors } }
        match writePlaceProto cfg s₁ caller.destination retVal with
        | .ok s₂ => .step s₂
        | .ub => .ub
        | .unsupported => .unsupported
  | _ => .ub

/-- Terminator evaluation (inline calls, return, goto, switchInt, unreachable). -/
def evalTerminatorProto (cfg : ProtoConfig) (s : ProtoMachineState) (term : Terminator) : ProtoStep :=
  match term.kind with
  | .goto target => .step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } }
  | .switchInt discr targets =>
    match evalOperandProto cfg s discr with
    | .ok (.scalar sc) s₁ =>
      .step { s₁ with frame := { s₁.frame with
        blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise, stmtIdx := 0 } }
    | .ok _ _ => .ub
    | .ub => .ub
    | .unsupported => .unsupported
  | .return_ => evalReturnProto cfg s
  | .unreachable => .ub
  | .call func argOps destination (.some targetBb) _ =>
    match extractCalleeDefPath? func with
    | .none => .unsupported
    | .some dp =>
      match findCalleeProto s.memory.callees dp with
      | .none => .unsupported
      | .some calleeBody =>
        match evalOperandsProto cfg s argOps with
        | .ok vals s₁ =>
          match Nat.beq vals.length calleeBody.argCount with
          | false => .ub
          | true =>
            let saved : ProtoSavedFrame :=
              { callerBody := s₁.body, frame := s₁.frame, destination := destination,
                returnTarget := targetBb, savedProtectors := s₁.memory.activeProtectors }
            .step
              { body := calleeBody
                frame := { blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody vals }
                memory := { s₁.memory with callStack := saved :: s₁.memory.callStack } }
        | .ub => .ub
        | .unsupported => .unsupported
  | _ => .unsupported

/-- One prototype machine step. -/
def stepMirFnProto (cfg : ProtoConfig) (s : ProtoMachineState) : ProtoStep :=
  match s.body.phase with
  | .other _ => .unsupported
  | _ =>
    match get? s.body.basicBlocks s.frame.blockIdx with
    | .none => .ub
    | .some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | .some stmt => evalStmtProto cfg s stmt
      | .none =>
        match Nat.beq s.frame.stmtIdx bb.statements.length with
        | true => evalTerminatorProto cfg s bb.terminator
        | false => .ub

/-- Fuel-bounded execution. -/
def runProtoFuel (cfg : ProtoConfig) : Nat → ProtoMachineState → ProtoOutcome
  | 0, _ => .outOfFuel
  | fuel + 1, s =>
    match stepMirFnProto cfg s with
    | .step s' => runProtoFuel cfg fuel s'
    | .ret v _ => .ok v
    | .ub => .ub
    | .unsupported => .unsupported

/-- Fuel-bounded silent stepping, for inspecting intermediate states. -/
def stepsProto (cfg : ProtoConfig) : Nat → ProtoMachineState → Option ProtoMachineState
  | 0, s => .some s
  | fuel + 1, s =>
    match stepMirFnProto cfg s with
    | .step s' => stepsProto cfg fuel s'
    | _ => .none

/-- Initial state for `body` with inline callees `callees` and arguments `args`. -/
def initProtoState (body : CapturedMir) (callees : List CapturedMir) (args : List Value) :
    ProtoMachineState :=
  { body := body
    frame := { blockIdx := 0, stmtIdx := 0, locals := initLocals body args }
    memory := { callees := callees } }

/-- Run `body` (root frame) with inline callees and arguments. -/
def runMirProto (body : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (fuel : Nat := 256) (cfg : ProtoConfig := {}) : ProtoOutcome :=
  runProtoFuel cfg fuel (initProtoState body callees args)

/-! ## §4. Part A witnesses: the eight tracked divergences flip to agreement -/

section PartAWitnesses

open MiniRustSpec.Correspondence (runA faultsA runA_sound faultsA_sound mirCallTreeWithCallees
  scalarBytes)
open MiniRustSpec.Correspondence.Witness (u32Ty u32Decl mkStmt mkTerm local_ constU32 fnAbi
  fnDefOp placeField retAlloc u32)
open MiniRustSpec.Correspondence.PointerWitness (ptrMutU32Decl derefPlace ptrBody)
open MiniRustSpec.Correspondence.RefWitness (refSharedU32Decl refMutU32Decl tbRetU32 TBRetOutcome
  projByteTB)
open MiniRustSpec.Correspondence.TbWitness (derefFieldPlace unsafeCellU32Decl
  refSharedUnsafeCellU32Decl initUnsafeCellU32 unsafeCellU32Layouts fnAbiUnsafeCellU32Arg)

/-- Scalar result `(bits, sizeBytes)` of the *unpatched* `Trusted` stepper (`runA` over
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`), `none` on fault / fuel exhaustion. -/
def trustedRunScalar? (body : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (fuel : Nat) : Option (Nat × Nat) :=
  match runA body fuel (initMachineStateWithCallees body args callees) with
  | .some (_, .normal (.scalar sc, _)) => .some (sc.bits, sc.sizeBytes)
  | _ => .none

/-- The unpatched `Trusted` stepper reaches a fault (`faultsA`). -/
def trustedFaults (body : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (fuel : Nat) : Bool :=
  faultsA body fuel (initMachineStateWithCallees body args callees)

/-- `n` silent steps of the unpatched `Trusted` stepper. -/
def trustedSteps (body : CapturedMir) : Nat → MachineState → Option MachineState
  | 0, s => .some s
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => trustedSteps body n s'
    | _ => .none

/-- Scalar bits stored in a local slot. -/
def slotScalarBits? : Option LocalSlot → Option Nat
  | .some (.init (.scalar sc)) => .some sc.bits
  | _ => .none

/-! ### `String.toList`-free replica of the MiniRust multi-function translator

`MiniRustSpec.Correspondence.translateProgWithIntrinsics` (and hence
`ProvenanceWitness.callerRefMutSilentWrongLocalMInit` / `callerBorrowAcrossScalarCallMInit`
and their `TBInit` lifts) transitively depends on `Classical.choice` through exactly one
leaf: core `String.toList` (Lean `v4.34.1`), used by `translateIntrinsicOrNone` to match the
callee path against the six supported `core::intrinsics::*` names. The replica below is a
verbatim copy of `translateTerminatorInProg` / `translateBlocksInProgWithIntrinsics` /
`translateFnInProgWithIntrinsics` / `translateProgFnsWithIntrinsics` /
`translateProgWithIntrinsics` (`minirust/lean/MiniRustSpec/Correspondence/Translate.lean`)
whose only change is that the intrinsic-name `match defPath.toList with ...` is replaced by
the equivalent `String` equality chain `intrinsicOfDefPathSF`. Every other helper
(`translateRsIntrinsic`, `lookupFnTarget`, `translateStmtResultWithIntrinsics`,
`splitStmts`, `fnNameMap`, `mkStartFn`, `multiMachineWithCtx`, `liftMachToTB`,
`Interp.steps`, `Interp.stepsTB`) is the real, unmodified MiniRust definition.
`scripts/test_tcb_correspondence_div8_proto.py` replays, in a temporary harness, the
kernel-checked bridges `callerRefMutSilentWrongLocalMInitSF =
ProvenanceWitness.callerRefMutSilentWrongLocalMInit := rfl` (and likewise for `TBInit` and
the `callerBorrowAcrossScalarCall` machines); those bridges necessarily inherit
`Classical.choice` from the upstream `String.toList`, so they live in the harness and not in
this file. -/

section StringFreeTranslator

open MiniRustSpec MiniRustSpec.Correspondence

/-- The six `core::intrinsics::*` paths recognized by `translateIntrinsicOrNone`, matched by
`String` equality instead of `String.toList`. -/
def intrinsicOfDefPathSF (defPath : String) : Option RsIntrinsic :=
  if defPath = "core::intrinsics::raw_eq" then some .raw_eq
  else if defPath = "core::intrinsics::ctpop" then some .ctpop
  else if defPath = "core::intrinsics::exact_div" then some .exact_div
  else if defPath = "core::intrinsics::cold_path" then some .cold_path
  else if defPath = "core::intrinsics::abort" then some .abort
  else if defPath = "core::intrinsics::ub_checks" then some .ub_checks
  else none

/-- `translateIntrinsicOrNone` via `intrinsicOfDefPathSF`. -/
def translateIntrinsicOrNoneSF (decls : List MirAst.LocalDecl) (defPath : String)
    (argOps : List MirAst.Operand) (destination : MirAst.Place)
    (target : Option MirAst.BasicBlockIdx) : Option TerminatorResult :=
  match intrinsicOfDefPathSF defPath with
  | some name => translateRsIntrinsic decls name argOps destination target
  | none => none

/-- Verbatim `translateTerminatorInProg`, calling `translateIntrinsicOrNoneSF`. -/
def translateTerminatorInProgSF (fnMap : FnMap) (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) (nextCleanup : Nat) (t : MirAst.Terminator) :
    Option (Gen.Terminator × Nat × List (Gen.BbName × Gen.BasicBlock)) :=
  match t.kind with
  | .call func argOps destination target unwind => do
    let defPath ← extractFnDefPath func
    match translateIntrinsicOrNoneSF decls defPath argOps destination target with
    | some res =>
      let b := bbName nextCleanup
      pure (.Goto b, nextCleanup + 1, [(b, ⟨res.stmts, res.terminator, .Regular⟩)])
    | none =>
      let (fn, conv) ← lookupFnTarget fnMap defPath
      let args ← argOps.mapM (translateCallArg decls)
      let retPlace ← translatePlace decls destination
      let (unwindBb, nextCleanup', extra) := translateUnwindAction nextCleanup unwind
      pure (.Call (fnPtrExpr fn) conv args retPlace (target.map bbName) (some unwindBb),
        nextCleanup', extra)
  | _ => do
    let term ← translateTerminator layouts decls t
    pure (term, nextCleanup, [])

/-- Verbatim `translateBlocksInProgWithIntrinsics`, calling `translateTerminatorInProgSF`. -/
def translateBlocksInProgWithIntrinsicsSF (fnMap : FnMap) (layouts : Layout.LayoutTable)
    (decls : List MirAst.LocalDecl) :
    Nat → Nat → List MirAst.BasicBlockData →
      Option (List (Gen.BbName × Gen.BasicBlock) × List (Gen.BbName × Gen.BasicBlock))
  | _, _, [] => some ([], [])
  | i, nextCleanup, bb :: bbs => do
    let results ← bb.statements.mapM (translateStmtResultWithIntrinsics decls · layouts)
    let sp := splitStmts (bbName i) [] nextCleanup results
    let (term, nextCleanup', extra1) ←
      translateTerminatorInProgSF fnMap layouts decls sp.2.2.2 bb.terminator
    let (rest, extraRest) ←
      translateBlocksInProgWithIntrinsicsSF fnMap layouts decls (i + 1) nextCleanup' bbs
    pure (sp.2.2.1 ++ [(sp.1, ⟨sp.2.1, term, .Regular⟩)] ++ rest, extra1 ++ extraRest)

/-- Verbatim `translateFnInProgWithIntrinsics`. -/
def translateFnInProgWithIntrinsicsSF (fnMap : FnMap)
    (body : MirAst.CapturedMir) : Option Gen.Function := do
  let conv ← translateCallConv body.fnAbi.conv
  let locals ← translateLocals body.layouts 0 body.localDecls
  let n := body.basicBlocks.length
  let (blocks, extra) ←
    translateBlocksInProgWithIntrinsicsSF fnMap body.layouts body.localDecls 0 (n + 1)
      body.basicBlocks
  pure {
    locals := ⟨locals⟩
    args := (List.range body.argCount).map (fun k => localName (k + 1))
    ret := localName 0
    calling_convention := conv
    blocks := ⟨blocks ++ [(bbName n, initBlock body)] ++ extra⟩
    start := bbName n
    implicit_writes := true
  }

/-- Verbatim `translateProgFnsWithIntrinsics`. -/
def translateProgFnsWithIntrinsicsSF (fnMap : FnMap) :
    Nat → List MirAst.CapturedMir → Option (List (Gen.FnName × Gen.Function))
  | _, [] => some []
  | idx, b :: bs => do
    let f ← translateFnInProgWithIntrinsicsSF fnMap b
    let rest ← translateProgFnsWithIntrinsicsSF fnMap (idx + 1) bs
    pure ((fnName idx, f) :: rest)

/-- Verbatim `translateProgWithIntrinsics`. -/
def translateProgWithIntrinsicsSF (entry : MirAst.CapturedMir)
    (callees : List MirAst.CapturedMir) : Option Gen.Program := do
  let fnMap := fnNameMap entry callees
  let fns ← translateProgFnsWithIntrinsicsSF fnMap 0 (entry :: callees)
  let startFn := fnName (1 + callees.length)
  pure {
    functions := ⟨fns ++ [(startFn, mkStartFn 0)]⟩
    start := startFn
    globals := ⟨[]⟩
    vtables := ⟨[]⟩
    traits := ⟨[]⟩
  }

/-- The intrinsic matcher recognizes exactly the six supported paths. -/
theorem intrinsicOfDefPathSF_table :
    intrinsicOfDefPathSF "core::intrinsics::raw_eq" = some .raw_eq ∧
    intrinsicOfDefPathSF "core::intrinsics::ctpop" = some .ctpop ∧
    intrinsicOfDefPathSF "core::intrinsics::exact_div" = some .exact_div ∧
    intrinsicOfDefPathSF "core::intrinsics::cold_path" = some .cold_path ∧
    intrinsicOfDefPathSF "core::intrinsics::abort" = some .abort ∧
    intrinsicOfDefPathSF "core::intrinsics::ub_checks" = some .ub_checks ∧
    intrinsicOfDefPathSF "witness::callee_read_ref_with_local" = none := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- `ProvenanceWitness.callerRefMutSilentWrongLocalProg`, via the replica. -/
def callerRefMutSilentWrongLocalProgSF : Gen.Program :=
  (translateProgWithIntrinsicsSF ProvenanceWitness.callerRefMutSilentWrongLocalMir
      [ProvenanceWitness.calleeReadRefWithLocalMir]).getD
    ProvenanceWitness.callRefMutProtectedProg

/-- `ProvenanceWitness.callerRefMutSilentWrongLocalMInit`, via the replica. -/
def callerRefMutSilentWrongLocalMInitSF : Interp.Mach :=
  match callerRefMutSilentWrongLocalProgSF.functions.entries[0]? with
  | some (_, callerFn) =>
    Witness.multiMachineWithCtx ProvenanceWitness.ctxCallRefMut1 callerRefMutSilentWrongLocalProgSF 2
      ProvenanceWitness.callerRefMutSilentWrongLocalMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)]
      callerFn.start
  | none => ProvenanceWitness.callRefMutProtectedMInit

/-- `ProvenanceWitness.callerRefMutSilentWrongLocalTBInit`, via the replica. -/
def callerRefMutSilentWrongLocalTBInitSF : Interp.MachTB :=
  RefWitness.liftMachToTB callerRefMutSilentWrongLocalMInitSF

/-- `ProvenanceWitness.callerBorrowAcrossScalarCallProg`, via the replica. -/
def callerBorrowAcrossScalarCallProgSF : Gen.Program :=
  (translateProgWithIntrinsicsSF ProvenanceWitness.callerBorrowAcrossScalarCallMir
      [ProvenanceWitness.calleeScalarAssignLocal1Mir]).getD
    ProvenanceWitness.callRefMutProtectedProg

/-- `ProvenanceWitness.callerBorrowAcrossScalarCallMInit`, via the replica. -/
def callerBorrowAcrossScalarCallMInitSF : Interp.Mach :=
  match callerBorrowAcrossScalarCallProgSF.functions.entries[0]? with
  | some (_, callerFn) =>
    Witness.multiMachineWithCtx ProvenanceWitness.ctxCallRefMut1 callerBorrowAcrossScalarCallProgSF 2
      ProvenanceWitness.callerBorrowAcrossScalarCallMir callerFn [.uninit, .init (.scalar ⟨5, 4⟩)]
      callerFn.start
  | none => ProvenanceWitness.callRefMutProtectedMInit

/-- `ProvenanceWitness.callerBorrowAcrossScalarCallTBInit`, via the replica. -/
def callerBorrowAcrossScalarCallTBInitSF : Interp.MachTB :=
  RefWitness.liftMachToTB callerBorrowAcrossScalarCallMInitSF

/-- Both witness programs translate successfully (the `getD` fallback is never taken). -/
theorem translateProgWithIntrinsicsSF_witnesses_isSome :
    (translateProgWithIntrinsicsSF ProvenanceWitness.callerRefMutSilentWrongLocalMir
        [ProvenanceWitness.calleeReadRefWithLocalMir]).isSome = true ∧
    (translateProgWithIntrinsicsSF ProvenanceWitness.callerBorrowAcrossScalarCallMir
        [ProvenanceWitness.calleeScalarAssignLocal1Mir]).isSome = true :=
  ⟨by decide +kernel, by decide +kernel⟩

end StringFreeTranslator

/-! ### 1. `DIV-MR-CALL-TARGET-LOCAL` (`P0_soundness`) -/

/-- Unpatched `Trusted` baseline (re-exported, classical-free): `callee` reads its own
`_1 = 100` through the caller's `&mut _1` and silently returns `137`. -/
theorem div_mr_call_target_local_trusted_baseline :
    (∃ tr mem, Trusted.ITree.ReachesRet
      (mirCallTreeWithCallees MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutSilentWrongLocalMir
        [.scalar ⟨5, 4⟩] [MiniRustSpec.Correspondence.ProvenanceWitness.calleeReadRefWithLocalMir])
      tr (.normal (.scalar ⟨137, 4⟩, mem))) ∧
    MirNoUBTree
      (mirCallTreeWithCallees MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutSilentWrongLocalMir
        [.scalar ⟨5, 4⟩] [MiniRustSpec.Correspondence.ProvenanceWitness.calleeReadRefWithLocalMir]) :=
  MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutSilentWrongLocal_anneal_137

/-- The same baseline, recomputed by executing `Trusted.stepMirFn`. -/
theorem div_mr_call_target_local_trusted_137 :
    trustedRunScalar? MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutSilentWrongLocalMir
      [MiniRustSpec.Correspondence.ProvenanceWitness.calleeReadRefWithLocalMir] [.scalar ⟨5, 4⟩] 25 =
      .some (137, 4) := by
  decide +kernel

/-- Ground truth: MiniRust `Mach` (`BasicMemory`) and `MachTB` (`TreeBorrowsMemory`)
both return `42`, executed by the real `Interp.steps` / `Interp.stepsTB` on the machine
built by the `String.toList`-free translator replica (kernel-checked equal to
`ProvenanceWitness.callerRefMutSilentWrongLocalMInit` / `TBInit` by the harness bridge). -/
theorem div_mr_call_target_local_mach_tb_42 :
    (MiniRustSpec.Interp.steps 13
        callerRefMutSilentWrongLocalMInitSF).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (MiniRustSpec.Interp.stepsTB 13
        callerRefMutSilentWrongLocalTBInitSF).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Repaired**: the frame-qualified overlay returns `42`, in 3-way agreement with
`Mach` and `MachTB`. -/
theorem div_mr_call_target_local_repaired_agrees :
    runMirProto MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutSilentWrongLocalMir
        [MiniRustSpec.Correspondence.ProvenanceWitness.calleeReadRefWithLocalMir] [.scalar ⟨5, 4⟩] =
      .ok (.scalar ⟨42, 4⟩) ∧
    (MiniRustSpec.Interp.steps 13
        callerRefMutSilentWrongLocalMInitSF).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (MiniRustSpec.Interp.stepsTB 13
        callerRefMutSilentWrongLocalTBInitSF).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   div_mr_call_target_local_mach_tb_42.1, div_mr_call_target_local_mach_tb_42.2⟩

/-- Write-back canary callee `fn write_ref_with_local(dummy: u32, r: &mut u32) -> u32
{ Retag([fn entry], r); *r = *r + 37; dummy }`: its own `_1 = 100` collides with the
caller's borrowed `_1`. -/
def calleeWriteRefWithLocalMir : CapturedMir where
  defPath := "witness::write_ref_with_local"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, refMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.retag .fnEntry (local_ 2)),
        mkStmt (.assign (derefPlace 2) (.binaryOp .add (.copy (derefPlace 2)) (constU32 37))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

/-- Write-back canary caller `fn caller_write_back(mut x: u32) -> u32 { let d =
write_ref_with_local(100, &mut x); x * 1000 + d }`. -/
def callerWriteBackMir : CapturedMir where
  defPath := "witness::caller_write_back"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::write_ref_with_local")
        [constU32 100, .move (local_ 2)] (local_ 3) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.binaryOp .mul (.copy (local_ 1)) (constU32 1000))),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 4)) (.copy (local_ 3)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- **Write-back canary**: right after the callee's `*r = *r + 37` (6 steps), the caller's
`_1` (depth 0) went from `5` to `42` while the callee's own `_1 = 100` (depth 1) is
untouched; the whole program returns `42 * 1000 + 100`. -/
theorem div_mr_call_target_local_write_back_canary :
    (stepsProto {} 6 (initProtoState callerWriteBackMir [calleeWriteRefWithLocalMir]
        [.scalar ⟨5, 4⟩])).map
      (fun s => (currentFrameDepth s, slotScalarBits? (readFrameLocalProto s 0 1),
        slotScalarBits? (readFrameLocalProto s 1 1))) =
      .some (1, .some 42, .some 100) ∧
    runMirProto callerWriteBackMir [calleeWriteRefWithLocalMir] [.scalar ⟨5, 4⟩] =
      .ok (.scalar ⟨42100, 4⟩) :=
  ⟨by decide +kernel, ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-- The unpatched `Trusted` stepper writes `137` into the *callee's* `_1` instead, so the
caller's `x` stays `5` and the program returns `5 * 1000 + 137`. -/
theorem div_mr_call_target_local_write_back_trusted :
    trustedRunScalar? callerWriteBackMir [calleeWriteRefWithLocalMir] [.scalar ⟨5, 4⟩] 30 =
      .some (5137, 4) := by
  decide +kernel

/-! ### 2. `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` (`P1_false_positive_ub`) -/

/-- Unpatched `Trusted` baseline (re-exported, classical-free): faults with UB. -/
theorem div_mr_caller_borrow_across_scalar_call_trusted_ub :
    ∃ tr u, Trusted.ITree.Reaches
      (mirCallTreeWithCallees MiniRustSpec.Correspondence.ProvenanceWitness.callerBorrowAcrossScalarCallMir
        [.scalar ⟨5, 4⟩] [MiniRustSpec.Correspondence.ProvenanceWitness.calleeScalarAssignLocal1Mir])
      tr u ∧ Trusted.ITree.FaultNow u :=
  MiniRustSpec.Correspondence.ProvenanceWitness.callerBorrowAcrossScalarCall_anneal_ub

/-- Ground truth: `Mach` and `MachTB` return `42` (same replica machine construction,
bridged to `ProvenanceWitness.callerBorrowAcrossScalarCallMInit` / `TBInit`). -/
theorem div_mr_caller_borrow_across_scalar_call_mach_tb_42 :
    (MiniRustSpec.Interp.steps 14
        callerBorrowAcrossScalarCallMInitSF).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (MiniRustSpec.Interp.stepsTB 14
        callerBorrowAcrossScalarCallTBInitSF).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Repaired**: returns `42`, in 3-way agreement with `Mach` and `MachTB`. -/
theorem div_mr_caller_borrow_across_scalar_call_repaired_agrees :
    runMirProto MiniRustSpec.Correspondence.ProvenanceWitness.callerBorrowAcrossScalarCallMir
        [MiniRustSpec.Correspondence.ProvenanceWitness.calleeScalarAssignLocal1Mir] [.scalar ⟨5, 4⟩] =
      .ok (.scalar ⟨42, 4⟩) ∧
    (MiniRustSpec.Interp.steps 14
        callerBorrowAcrossScalarCallMInitSF).toOption.map
        (fun m => (m.mem.memory.allocations[0]?, m.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    (MiniRustSpec.Interp.stepsTB 14
        callerBorrowAcrossScalarCallTBInitSF).toOption.map
        (fun m =>
          ({ retAlloc := m.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
             stackDepths := m.threads.map (·.stack.length) } : TBRetOutcome)) =
      tbRetU32 42 :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   div_mr_caller_borrow_across_scalar_call_mach_tb_42.1,
   div_mr_caller_borrow_across_scalar_call_mach_tb_42.2⟩

/-! ### 3. `DIV-MR-TB-TWOPHASE-DIRECT-WRITE` (`P1_soundness`) -/

/-- **Repaired**: the direct write `_1 = 99` disables the unprotected `Freeze`
`.reservedFrz` two-phase borrow, so `copy (*_2)` faults with UB, matching `MachTB` and the
`LM-3.3` `Trusted` semantics; the pre-`LM-3.3` buggy direct-write model
(`preserveReservedOnDirectWrite`) wrongly returns `99`. -/
theorem div_mr_tb_twophase_direct_write_repaired_agrees :
    runMirProto MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap [] [.scalar ⟨5, 4⟩] =
      .ub ∧
    MiniRustSpec.Correspondence.RefWitness.ubAfterTB
        MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap [.scalar ⟨5, 4⟩] 5 =
      some "Tree Borrows: local read of Disabled reference" ∧
    (∃ tr u, Trusted.ITree.Reaches (mirTree MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap
      (initMachineState MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap [.scalar ⟨5, 4⟩]))
        tr u ∧ Trusted.ITree.FaultNow u) ∧
    runMirProto MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap [] [.scalar ⟨5, 4⟩]
        (cfg := { preserveReservedOnDirectWrite := true }) =
      .ok (.scalar ⟨99, 4⟩) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap_tb_direct,
   MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap_anneal_ub,
   ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-! ### 4. `DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` (`P1_soundness`) -/

/-- Unpatched `Trusted` baseline (re-exported): returns `5`. -/
theorem div_mr_tb_fnentry_local_dealloc_trusted_ret :
    ∃ mem, Trusted.ITree.ReachesRet (mirTree MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb
      (initMachineState MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨5, 4⟩, mem)) :=
  MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb_anneal_ret

/-- **Repaired**: the *root-frame* `Return` (`callStack = []`) detects the protected
`Frozen` tag on `_1` and faults with UB, matching `MachTB`. -/
theorem div_mr_tb_fnentry_local_dealloc_repaired_agrees :
    runMirProto MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb [] [.scalar ⟨5, 4⟩] = .ub ∧
    MiniRustSpec.Correspondence.RefWitness.ubAfterTB
        MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb [.scalar ⟨5, 4⟩] 6 =
      some "Tree Borrows: foreign write of protected Frozen reference which had a local read" :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb_tb_direct⟩

/-- The UB is raised exactly at `Terminator::Return`: the 4 statements step, the
terminator faults. -/
theorem div_mr_tb_fnentry_local_dealloc_ub_at_return :
    (match stepsProto {} 4 (initProtoState MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb
        [] [.scalar ⟨5, 4⟩]) with
      | .some s => (s.frame.stmtIdx, match stepMirFnProto {} s with | .ub => true | _ => false)
      | .none => (0, false)) = (4, true) := by
  decide +kernel

/-- Caller of `retagFnEntryLocalDeallocUb` (multi-frame canary). -/
def callerOfFnEntryLocalDeallocMir : CapturedMir where
  defPath := "witness::caller_of_fn_entry_local_dealloc"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl]
  basicBlocks := [
    { statements := [],
      terminator := mkTerm (.call (fnDefOp "witness::retag_fn_entry_local_dealloc_ub")
        [.copy (local_ 1)] (local_ 0) (some 1) .continue_),
      isCleanup := false },
    { statements := [], terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- **Multi-frame callee-return canary**: the callee's `Retag([fn entry])` on a
reference to its *own* `_1` faults at the callee's `Return` (depth 1) instead of leaking
a dangling protected reference to the caller; unpatched `Trusted` silently returns `5`. -/
theorem div_mr_tb_fnentry_local_dealloc_callee_return_canary :
    runMirProto callerOfFnEntryLocalDeallocMir
        [MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb] [.scalar ⟨5, 4⟩] = .ub ∧
    trustedRunScalar? callerOfFnEntryLocalDeallocMir
        [MiniRustSpec.Correspondence.RefWitness.retagFnEntryLocalDeallocUb] [.scalar ⟨5, 4⟩] 20 =
      .some (5, 4) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), by decide +kernel⟩

/-! ### 5. `DIV-MR-TB-UNSAFECELL-PROTECTED-IM` (`P2_false_positive_ub`) -/

/-- **Repaired**: succeeds through `Return` with `77`, matching `MachTB`, `Mach`, and
`Trusted` (whose protected-write rule already exempts `.cell`). -/
theorem div_mr_tb_unsafecell_protected_im_repaired_agrees :
    runMirProto MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut [] [initUnsafeCellU32] =
      .ok (.scalar ⟨77, 4⟩) ∧
    MiniRustSpec.Correspondence.RefWitness.retAfterTB
        MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut [initUnsafeCellU32] 9 =
      tbRetU32 77 ∧
    MiniRustSpec.Correspondence.PointerWitness.retAfter
        MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut [initUnsafeCellU32] 9 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut_tb_direct,
   MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut_minirust_direct⟩

/-- **#4/#5 coupling**: with the legacy deallocation rule (every protected tag blocks,
as unpatched `Trusted.hasProtectedLocalBorrow`), adding #4's `Return` check breaks
`unsafeCellProtectedInteriorMut` (UB at `Return`). -/
theorem div_mr_tb_unsafecell_coupling_legacy_breaks :
    runMirProto MiniRustSpec.Correspondence.TbWitness.unsafeCellProtectedInteriorMut [] [initUnsafeCellU32]
      (cfg := { legacyDeallocCheck := true }) = .ub :=
  ProtoOutcome.eq_ub_of_isUB (by decide +kernel)

/-- `StorageDead` canary body: `_3 = copy _1` (`UnsafeCell<u32>`), `_2 = &_3`,
`Retag([fn entry], _2)`, `_0 = copy ((*_2).0)`, `StorageDead(_3)`. -/
def unsafeCellProtectedStorageDeadMir : CapturedMir :=
  { ptrBody "witness::unsafe_cell_protected_storage_dead"
      [u32Decl, unsafeCellU32Decl, refSharedUnsafeCellU32Decl, unsafeCellU32Decl]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 3) (.use (.copy (local_ 1))),
       .assign (local_ 2) (.ref .shared (local_ 3)),
       .retag .fnEntry (local_ 2),
       .assign (local_ 0) (.use (.copy (derefFieldPlace 2 0 u32Ty))),
       .storageDead 3] with
    fnAbi := fnAbiUnsafeCellU32Arg, layouts := unsafeCellU32Layouts }

/-- **`StorageDead` protected-`.cell` canary**: right before `StorageDead(_3)`, the
unpatched `Trusted.hasProtectedLocalBorrow` (`Statements.lean:1842`) reports `true` for
the protected `.cell` borrow of `_3`, so `Trusted` faults; `hasProtectedLocalBorrowProto`
reports `false` and the overlay runs through `StorageDead` and `Return`. -/
theorem div_mr_tb_unsafecell_storage_dead_canary :
    (trustedSteps unsafeCellProtectedStorageDeadMir 6
        (initMachineState unsafeCellProtectedStorageDeadMir [initUnsafeCellU32])).map
      (fun s => hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors 3) = .some true ∧
    trustedFaults unsafeCellProtectedStorageDeadMir [] [initUnsafeCellU32] 20 = true ∧
    (stepsProto {} 6 (initProtoState unsafeCellProtectedStorageDeadMir [] [initUnsafeCellU32])).map
      (fun s => hasProtectedLocalBorrowProto {} s.memory.borrows s.memory.activeProtectors 0 3) =
      .some false ∧
    runMirProto unsafeCellProtectedStorageDeadMir [] [initUnsafeCellU32] = .ok (.scalar ⟨5, 4⟩) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-! ### 6. `DIV-LM-RAW-OVERWRITE-CHAR-COPY` (`P1_soundness`) -/

/-- `char` type. -/
def charTyP : Ty := { kind := .char, layoutIdx := 0 }
/-- `char` local. -/
def charDeclP : LocalDecl := { mutability := .mut, ty := charTyP, debugName := none }

/-- Raw-overwritten `char` program (the concrete instance of
`SimLM3_1.step_raw_overwritten_direct_copy_invalid_char_divergence`):
```rust
fn raw_overwrite_char_load(mut c: char) -> char {
    let p = &raw mut c as *mut u32;   // _2 = &raw mut _1
    unsafe { *p = CODE; }             // (*_2) = const CODE_u32
    let d = c;                        // _3 = copy _1   (or move _1)
    d                                 // _0 = copy _3
}
```
-/
def rawOverwriteCharLoadMir (code : Nat) (useMove : Bool) : CapturedMir :=
  ptrBody "witness::raw_overwrite_char_load"
    [charDeclP, charDeclP, ptrMutU32Decl, charDeclP]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (derefPlace 2) (.use (constU32 code)),
     .assign (local_ 3) (.use (match useMove with | true => .move (local_ 1) | false => .copy (local_ 1))),
     .assign (local_ 0) (.use (.copy (local_ 3))),
     .storageDead 3, .storageDead 2]

/-- Unpatched `Trusted`: the direct `copy`/`move` of the raw-overwritten surrogate
`0xD800` steps without UB (the 5th statement is a silent `.tau` step) and the program
returns the invalid `char`. -/
theorem div_lm_raw_overwrite_char_copy_trusted_steps :
    (trustedSteps (rawOverwriteCharLoadMir 0xD800 false) 4
        (initMachineState (rawOverwriteCharLoadMir 0xD800 false) [.scalar ⟨0x41, 4⟩])).map
      (fun s => match stepMirFn (rawOverwriteCharLoadMir 0xD800 false) s with
        | .tau (.running _) => true
        | _ => false) = .some true ∧
    trustedRunScalar? (rawOverwriteCharLoadMir 0xD800 false) [] [.scalar ⟨0x41, 4⟩] 30 = .some (0xD800, 4) ∧
    trustedRunScalar? (rawOverwriteCharLoadMir 0xD800 true) [] [.scalar ⟨0x41, 4⟩] 30 = .some (0xD800, 4) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Repaired**: the direct typed load faults with UB on `0xD800`, `0xDFFF`, and
`0x110000`, for both `copy` and `move`. -/
theorem div_lm_raw_overwrite_char_copy_repaired_ub :
    runMirProto (rawOverwriteCharLoadMir 0xD800 false) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharLoadMir 0xDFFF false) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharLoadMir 0x110000 false) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharLoadMir 0xD800 true) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharLoadMir 0xDFFF true) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharLoadMir 0x110000 true) [] [.scalar ⟨0x41, 4⟩] = .ub :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel)⟩

/-- The UB is raised exactly at the direct load `_3 = copy _1` (5th statement). -/
theorem div_lm_raw_overwrite_char_copy_ub_at_load :
    (stepsProto {} 4 (initProtoState (rawOverwriteCharLoadMir 0xD800 false) [] [.scalar ⟨0x41, 4⟩])).map
      (fun s => (s.frame.stmtIdx, match stepMirFnProto {} s with | .ub => true | _ => false)) =
      .some (4, true) := by
  decide +kernel

/-- Positive canary: valid scalars (`0x41`, `0xD7FF`, `0xE000`, `0x10FFFF`) are accepted
and returned unchanged under both `copy` and `move`. -/
theorem div_lm_raw_overwrite_char_copy_valid_accepted :
    runMirProto (rawOverwriteCharLoadMir 0x41 false) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0x41, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0xD7FF false) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0xD7FF, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0xE000 false) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0xE000, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0x10FFFF false) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0x10FFFF, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0x41 true) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0x41, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0xD7FF true) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0xD7FF, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0xE000 true) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0xE000, 4⟩) ∧
    runMirProto (rawOverwriteCharLoadMir 0x10FFFF true) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0x10FFFF, 4⟩) :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-- lean-miri's `char` validity check `annealValidateScalarForTyId 2`
(`lean-miri/lean/LeanMiriSpec/Correspondence/Translate.lean:1855-1859`) on an Anneal
`ScalarInt`: size `4` bytes and a Unicode scalar value. -/
def miriValidateCharScalar (sc : ScalarInt) : Bool :=
  Bool.and (Nat.beq sc.sizeBytes 4) (isValidCharCode sc.bits)

/-- `isValidCharCode` is exactly Lean core's `Nat.isValidChar` (Unicode scalar values:
`< 0xD800` or `0xE000 ≤ c ≤ 0x10FFFF`). -/
theorem isValidCharCode_iff_isValidChar (n : Nat) : isValidCharCode n = true ↔ Nat.isValidChar n := by
  simp only [isValidCharCode, Nat.isValidChar, nat_ble_eq_decide, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · intro h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩

/-- **Universal equivalence** (`DIV-LM-RAW-OVERWRITE-CHAR-COPY`): for every `char`-typed
place and every scalar, `validateLoadedValueProto` on `copy`/`move` coincides with
lean-miri's `miriValidateCharScalar`, i.e. with `sizeBytes = 4 ∧ Nat.isValidChar bits`. -/
theorem validateLoadedValueProto_char_eq_miri (decls : List LocalDecl) (layouts : LayoutTable)
    (p : Place) (ty : Ty) (hty : placeTy decls layouts p = .some ty) (hchar : ty.kind = .char)
    (sc : ScalarInt) :
    validateLoadedValueProto decls layouts (.copy p) (.scalar sc) = miriValidateCharScalar sc ∧
    validateLoadedValueProto decls layouts (.move p) (.scalar sc) = miriValidateCharScalar sc ∧
    (miriValidateCharScalar sc = true ↔ sc.sizeBytes = 4 ∧ Nat.isValidChar sc.bits) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [validateLoadedValueProto, operandTy, hty, hchar, miriValidateCharScalar]
  · simp only [validateLoadedValueProto, operandTy, hty, hchar, miriValidateCharScalar]
  · simp only [miriValidateCharScalar, Bool.and_eq_true, Nat.beq_eq, isValidCharCode_iff_isValidChar]

/-- Spot checks of the equivalence on the brief's boundary scalars. -/
theorem miriValidateCharScalar_boundaries :
    miriValidateCharScalar ⟨0x41, 4⟩ = true ∧ miriValidateCharScalar ⟨0xD7FF, 4⟩ = true ∧
    miriValidateCharScalar ⟨0xE000, 4⟩ = true ∧ miriValidateCharScalar ⟨0x10FFFF, 4⟩ = true ∧
    miriValidateCharScalar ⟨0xD800, 4⟩ = false ∧ miriValidateCharScalar ⟨0xDFFF, 4⟩ = false ∧
    miriValidateCharScalar ⟨0x110000, 4⟩ = false ∧ miriValidateCharScalar ⟨0x41, 1⟩ = false := by
  decide +kernel

/-! ### 7. `DIV-LM-D6-OFFSET-DISABLED-TAG` (`P2_false_positive_ub`) -/

/-- `u8`. -/
def u8TyP : Ty := { kind := .uint .u8, layoutIdx := 0 }
/-- `u8` local. -/
def u8DeclP : LocalDecl := { mutability := .mut, ty := u8TyP, debugName := none }
/-- `*mut u8`. -/
def ptrMutU8TyP : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
/-- `*mut u8` local. -/
def ptrMutU8DeclP : LocalDecl := { mutability := .mut, ty := ptrMutU8TyP, debugName := none }
/-- `isize`. -/
def isizeTyP : Ty := { kind := .int .isize, layoutIdx := 0 }
/-- `isize` local. -/
def isizeDeclP : LocalDecl := { mutability := .mut, ty := isizeTyP, debugName := none }
/-- `isize` constant with raw two's-complement bits. -/
def constIsizeBits (bits : Nat) : Operand :=
  .constant { ty := isizeTyP, val := .scalar (.int ⟨bits, 8⟩) }
/-- `u8` constant. -/
def constU8P (n : Nat) : Operand := .constant { ty := u8TyP, val := .scalar (.int ⟨n, 1⟩) }

/-- Offset-of-a-disabled-tag program (the concrete instance of
`SimLM3_1.step_binOp_offset_disabled_divergence`):
```rust
fn offset_disabled_tag(mut x: u32) -> u32 {
    let p = &raw mut x as *mut u8;   // _2 = &raw mut _1         (tag .unique)
    x = 7;                           // _1 = const 7_u32          (foreign write: tag .disabled)
    let q = p.offset(COUNT);         // _3 = Offset(copy _2, const COUNT_isize)
    TAIL
}
```
-/
def offsetDisabledTagMir (disable : Bool) (countBits : Nat) (tail : List StatementKind) :
    CapturedMir :=
  ptrBody "witness::offset_disabled_tag"
    [u32Decl, u32Decl, ptrMutU8DeclP, ptrMutU8DeclP, u8DeclP, ptrMutU8DeclP]
    ([.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
      .assign (local_ 2) (.rawPtr .mut (local_ 1))] ++
     (match disable with | true => [.assign (local_ 1) (.use (constU32 7))] | false => []) ++
     [.assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (constIsizeBits countBits))] ++ tail)

/-- Tail returning `1` without touching the offset pointer. -/
def offsetTailRet : List StatementKind := [.assign (local_ 0) (.use (constU32 1))]
/-- Tail reading through the offset pointer. -/
def offsetTailRead : List StatementKind :=
  [.assign (local_ 4) (.use (.copy (derefPlace 3))), .assign (local_ 0) (.use (constU32 1))]
/-- Tail writing through the offset pointer. -/
def offsetTailWrite : List StatementKind :=
  [.assign (derefPlace 3) (.use (constU8P 9)), .assign (local_ 0) (.use (constU32 1))]

/-- Unpatched `Trusted` rejects the in-bounds offset of the `.disabled` tag
(`evalPtrOffsetBinOp`'s `borrowDisabled` check). -/
theorem div_lm_d6_offset_disabled_trusted_ub :
    trustedFaults (offsetDisabledTagMir true 1 offsetTailRet) [] [.scalar ⟨5, 4⟩] 20 = true ∧
    trustedFaults (offsetDisabledTagMir true 0 offsetTailRet) [] [.scalar ⟨5, 4⟩] 20 = true ∧
    trustedRunScalar? (offsetDisabledTagMir false 1 offsetTailRet) [] [.scalar ⟨5, 4⟩] 20 = .some (1, 4) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `RvalueEvalResult` UB projection. -/
def rvalueIsUB : RvalueEvalResult → Bool
  | .ub => true
  | _ => false

/-- Direct evaluation of the unpatched `Trusted.evalPtrOffsetBinOp` on an in-bounds
offset (`+1` byte into a live 4-byte `u32` local): `.ub` for a `.disabled` tag, success
for the same tag in state `.unique`. -/
theorem div_lm_d6_offset_trusted_evalPtrOffsetBinOp :
    rvalueIsUB (evalPtrOffsetBinOp [.uninit, .init (.scalar ⟨7, 4⟩), .init (.ptr ⟨1, 0⟩ 8)]
      { borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .disabled }],
        nextTag := 2 }
      [u32Decl, u32Decl, ptrMutU8DeclP] emptyLayoutTable (.copy (local_ 2)) ⟨1, 0⟩ 8 ⟨1, 8⟩) = true ∧
    rvalueIsUB (evalPtrOffsetBinOp [.uninit, .init (.scalar ⟨7, 4⟩), .init (.ptr ⟨1, 0⟩ 8)]
      { borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .unique }],
        nextTag := 2 }
      [u32Decl, u32Decl, ptrMutU8DeclP] emptyLayoutTable (.copy (local_ 2)) ⟨1, 0⟩ 8 ⟨1, 8⟩) = false := by
  decide +kernel

/-- **Repaired** (concrete): the offset of the `.disabled` tag steps (zero, interior, and
one-past-the-end offsets of the 4-byte allocation) and the program returns `1`. -/
theorem div_lm_d6_offset_disabled_repaired_steps :
    runMirProto (offsetDisabledTagMir true 0 offsetTailRet) [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨1, 4⟩) ∧
    runMirProto (offsetDisabledTagMir true 1 offsetTailRet) [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨1, 4⟩) ∧
    runMirProto (offsetDisabledTagMir true 4 offsetTailRet) [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨1, 4⟩) ∧
    runMirProto (offsetDisabledTagMir true 5 offsetTailRet) [] [.scalar ⟨5, 4⟩] = .ub :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel)⟩

/-- **Dereference safety canary**: reading or writing through the offset pointer of the
`.disabled` tag still faults with UB, while the same read through a live tag succeeds. -/
theorem div_lm_d6_offset_disabled_deref_canary :
    runMirProto (offsetDisabledTagMir true 0 offsetTailRead) [] [.scalar ⟨5, 4⟩] = .ub ∧
    runMirProto (offsetDisabledTagMir true 1 offsetTailRead) [] [.scalar ⟨5, 4⟩] = .ub ∧
    runMirProto (offsetDisabledTagMir true 0 offsetTailWrite) [] [.scalar ⟨5, 4⟩] = .ub ∧
    runMirProto (offsetDisabledTagMir true 1 offsetTailWrite) [] [.scalar ⟨5, 4⟩] = .ub ∧
    runMirProto (offsetDisabledTagMir false 0 offsetTailRead) [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨1, 4⟩) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-- Signed `isize` value of an 8-byte `ScalarInt`. -/
def isizeValue (sc : ScalarInt) : Int := intValueOfBits true 64 sc.bits

/-- Miri's `ptr_offset_inbounds` (`lean-miri/vendor/Miri/Interpreter/PointerOffset.lean:14-20`
via `checkPtrAccessSigned` / `checkedBounds`, `lean-miri/vendor/Miri/Memory/Access.lean:115-150`):
the signed byte offset must fit `i64`; a zero offset is always fine; otherwise the
allocation must be live and the whole range between the pointer and the result must be
in bounds. Tree Borrows permissions are not consulted. -/
def miriPtrOffsetInbounds (allocLive : Bool) (allocSize ptrOffset : Nat) (offsetBytes : Int) :
    Option Nat :=
  if offsetBytes < -(2 ^ 63 : Int) ∨ (2 ^ 63 : Int) ≤ offsetBytes then .none
  else if offsetBytes = 0 then .some ptrOffset
  else if allocLive = false then .none
  else if 0 < offsetBytes then
    if ptrOffset + offsetBytes.toNat ≤ allocSize then .some (ptrOffset + offsetBytes.toNat) else .none
  else
    if (-offsetBytes).toNat ≤ ptrOffset ∧ ptrOffset ≤ allocSize then
      .some (ptrOffset - (-offsetBytes).toNat)
    else .none

theorem scalarModulus_eight : scalarModulus 8 = 18446744073709551616 := by decide +kernel
theorem signedHalfModulus_eight : signedHalfModulus 8 = 9223372036854775808 := by decide +kernel

theorem wrap64 (bits : Nat) : wrapScalarBits bits 18446744073709551616 = bits % 18446744073709551616 := by
  unfold wrapScalarBits
  rw [nat_ble_eq_decide]
  by_cases h : 18446744073709551616 ≤ bits
  · simp only [h, decide_true]; rfl
  · simp only [h, decide_false]
    rw [Nat.mod_eq_of_lt (by omega)]

theorem miriPtrOffsetInbounds_neg (bound o P : Nat) :
    miriPtrOffsetInbounds true bound o (-(P : Int)) =
      if P ≤ 9223372036854775808 then
        (if P = 0 then some o else if P ≤ o ∧ o ≤ bound then some (o - P) else none)
      else none := by
  unfold miriPtrOffsetInbounds
  simp only [Int.reducePow, Int.reduceNeg]
  by_cases h1 : P ≤ 9223372036854775808
  · by_cases h0 : P = 0
    · subst h0; simp
    · have hA : ¬ (-(P:Int) < -9223372036854775808 ∨ (9223372036854775808 : Int) ≤ -(P:Int)) := by omega
      have hB : ¬ (-(P:Int) = 0) := by omega
      have hC : ¬ (0 < -(P:Int)) := by omega
      have hD : (-(-(P:Int))).toNat = P := by simp
      simp only [hA, hB, hC, hD, ite_false, h1, h0, ite_true, Bool.true_eq_false]
  · have hA : (-(P:Int) < -9223372036854775808 ∨ (9223372036854775808 : Int) ≤ -(P:Int)) := by omega
    simp only [hA, ite_true, h1, ite_false]

theorem miriPtrOffsetInbounds_nonneg (bound o Q : Nat) :
    miriPtrOffsetInbounds true bound o (Q : Int) =
      if Q < 9223372036854775808 then
        (if Q = 0 then some o else if o + Q ≤ bound then some (o + Q) else none)
      else none := by
  unfold miriPtrOffsetInbounds
  simp only [Int.reducePow, Int.reduceNeg]
  by_cases h1 : Q < 9223372036854775808
  · by_cases h0 : Q = 0
    · subst h0; simp
    · have hA : ¬ ((Q:Int) < -9223372036854775808 ∨ (9223372036854775808 : Int) ≤ (Q:Int)) := by omega
      have hB : ¬ ((Q:Int) = 0) := by omega
      have hC : (0 < (Q:Int)) := by omega
      have hD : ((Q:Int)).toNat = Q := by simp
      simp only [hA, hB, hC, hD, ite_false, h1, h0, ite_true, Bool.true_eq_false]
  · have hA : ((Q:Int) < -9223372036854775808 ∨ (9223372036854775808 : Int) ≤ (Q:Int)) := by omega
    simp only [hA, ite_true, h1, ite_false]

theorem evalBinOpOffset_lockstep_miri (ptrVal : ProvenancePtr) (offsetSc : ScalarInt)
    (stride bound : Nat) (hsz : offsetSc.sizeBytes = 8) (hin : ptrVal.offsetBytes ≤ bound)
    (hbound : bound < 2 ^ 63) :
    evalBinOpOffset ptrVal 8 offsetSc stride (.some bound) 8 =
      (miriPtrOffsetInbounds true bound ptrVal.offsetBytes (isizeValue offsetSc * (stride : Int))).map
        (fun n => { ptrVal with offsetBytes := n }) := by
  obtain ⟨a, o⟩ := ptrVal
  obtain ⟨bits, sz⟩ := offsetSc
  simp only at hsz hin ⊢
  subst hsz
  simp only [Nat.reducePow] at hbound
  have hB : bits % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have hw2 : wrapScalarBits (bits % 18446744073709551616) 18446744073709551616 =
      bits % 18446744073709551616 := by rw [wrap64, Nat.mod_mod]
  simp only [evalBinOpOffset, isSignedNegative, scalarModulus_eight, signedHalfModulus_eight,
    Nat.beq_refl, Bool.and_self, wrap64, hw2, nat_ble_eq_decide, nat_beq_eq_decide,
    isizeValue, intValueOfBits, Nat.reducePow, Nat.reduceSub,
    true_and, Nat.sub_eq, Nat.mul_eq, Nat.add_eq]
  generalize hBv : bits % 18446744073709551616 = B at hB ⊢
  by_cases hneg : 9223372036854775808 ≤ B
  · simp only [hneg, decide_true, ite_true]
    have hInt : ((B : Int) - ((18446744073709551616 : Nat) : Int)) * (stride : Int) =
        -((((18446744073709551616 - B) * stride : Nat)) : Int) := by
      rw [Int.natCast_mul, Int.ofNat_sub (Nat.le_of_lt hB), ← Int.neg_mul, Int.neg_sub]
    rw [hInt, miriPtrOffsetInbounds_neg]
    generalize (18446744073709551616 - B) * stride = P
    by_cases h1 : 9223372036854775808 ≤ P
    · have h1' : ¬ (P ≤ 9223372036854775808 ∧ P ≤ o ∧ o ≤ bound) := by omega
      by_cases hP : P ≤ 9223372036854775808
      · have hP0 : ¬ P = 0 := by omega
        have hPo : ¬ (P ≤ o ∧ o ≤ bound) := by omega
        simp only [h1, decide_true, Bool.not_true, Bool.false_and, hP, ↓reduceIte, hP0, hPo,
          Option.map_none]
      · simp only [h1, decide_true, Bool.not_true, Bool.false_and, hP, ↓reduceIte, Option.map_none]
    · have hP : P ≤ 9223372036854775808 := by omega
      by_cases h2 : P ≤ o
      · have hn : o - P ≤ bound := by omega
        have hb : ¬ 9223372036854775808 ≤ bound := by omega
        by_cases hP0 : P = 0
        · subst hP0
          simp only [Nat.le_zero_eq, reduceCtorEq, decide_false, Bool.not_false, h2, decide_true,
            Bool.and_self, Nat.sub_zero, Bool.true_and, hb, hin, Bool.or_true, Nat.zero_le, ↓reduceIte,
            Option.map_some]
        · simp only [h1, decide_false, Bool.not_false, h2, decide_true, Bool.and_self, hb, hin, hn,
            Bool.or_true, hP, ↓reduceIte, hP0, and_self, Option.map_some]
      · have hP0 : ¬ P = 0 := by omega
        simp only [h1, decide_false, Bool.not_false, h2, Bool.and_false, hP, ↓reduceIte, hP0, false_and,
          Option.map_none]
  · simp only [hneg, decide_false, ite_false]
    rw [← Int.natCast_mul, miriPtrOffsetInbounds_nonneg]
    generalize B * stride = Q
    by_cases h1 : 9223372036854775808 ≤ Q
    · have h1' : ¬ Q < 9223372036854775808 := by omega
      simp only [h1, decide_true, h1', ↓reduceIte, Option.map_none]
    · have h1' : Q < 9223372036854775808 := by omega
      have hb : ¬ 9223372036854775808 ≤ bound := by omega
      by_cases h2 : 9223372036854775808 ≤ o + Q
      · have hQ0 : ¬ Q = 0 := by omega
        have hoQ : ¬ o + Q ≤ bound := by omega
        simp only [h1, decide_false, h2, decide_true, h1', ↓reduceIte, hQ0, hoQ, Option.map_none]
      · by_cases hQ0 : Q = 0
        · subst hQ0
          have ho : ¬ 9223372036854775808 ≤ o := by omega
          simp only [Nat.le_zero_eq, reduceCtorEq, decide_false, Nat.add_zero, ho, decide_true,
            Bool.not_false, Bool.and_self, Bool.and_true, hb, hin, Bool.or_true, Nat.zero_lt_succ,
            ↓reduceIte, Option.map_some]
        · have hoQne : ¬ (o + Q = o) := by omega
          by_cases h3 : o + Q ≤ bound
          · simp only [h1, decide_false, h2, hoQne, hQ0, Bool.false_and, Bool.and_false, hb,
              Bool.not_false, hin, decide_true, h3, Bool.and_self, Bool.or_true, h1', ↓reduceIte,
              Option.map_some]
          · simp only [h1, decide_false, h2, hoQne, hQ0, Bool.false_and, Bool.and_false, h3,
              Bool.or_self, h1', ↓reduceIte, Option.map_none]


/-- The allocation bound used by `BinOp.Offset` ignores the entry's permission. -/
theorem ptrAllocByteBoundProto_perm_irrel (s : ProtoMachineState) (entry : ProtoBorrowEntry)
    (p : TreeBorrowPerm) :
    ptrAllocByteBoundProto s { entry with perm := p } = ptrAllocByteBoundProto s entry := rfl

theorem miriPtrOffsetInbounds_false_neg (bound o P : Nat) :
    miriPtrOffsetInbounds false bound o (-(P : Int)) =
      if P = 0 then some o else none := by
  cases P with
  | zero => simp [miriPtrOffsetInbounds]
  | succ k =>
    unfold miriPtrOffsetInbounds
    have h0 : ¬ (-(Nat.succ k : Int) = 0) := by rintro ⟨⟩
    simp only [Nat.succ_ne_zero, h0, ↓reduceIte, ite_self]

theorem miriPtrOffsetInbounds_false_nonneg (bound o Q : Nat) :
    miriPtrOffsetInbounds false bound o (Q : Int) =
      if Q = 0 then some o else none := by
  cases Q with
  | zero => simp [miriPtrOffsetInbounds]
  | succ k =>
    unfold miriPtrOffsetInbounds
    have h0 : ¬ ((Nat.succ k : Int) = 0) := by rintro ⟨⟩
    simp only [Nat.succ_ne_zero, h0, ↓reduceIte, ite_self]

/-- When `ptrVal.offsetBytes ≤ bound`, replacing `.some 0` with `.none` on a zero-delta
offset leaves `evalBinOpOffset` unchanged. -/
theorem evalBinOpOffset_effBound_eq_of_le (ptrVal : ProvenancePtr) (offsetSc : ScalarInt)
    (stride bound : Nat) (hsz : offsetSc.sizeBytes = 8) (hin : ptrVal.offsetBytes ≤ bound) :
    let effBound : Option Nat :=
      match Bool.and (Nat.beq bound 0)
        (Bool.or (Nat.beq (wrapScalarBits offsetSc.bits (scalarModulus 8)) 0)
          (Nat.beq stride 0)) with
      | true => .none
      | false => .some bound
    evalBinOpOffset ptrVal 8 offsetSc stride effBound 8 =
      evalBinOpOffset ptrVal 8 offsetSc stride (.some bound) 8 := by
  dsimp only
  by_cases hb0 : bound = 0
  · subst hb0
    have ho0 : ptrVal.offsetBytes = 0 := Nat.eq_zero_of_le_zero hin
    obtain ⟨a, o⟩ := ptrVal
    obtain ⟨bits, sz⟩ := offsetSc
    simp only at ho0 hsz
    subst ho0 hsz
    have hw2 : wrapScalarBits (bits % 18446744073709551616) 18446744073709551616 =
        bits % 18446744073709551616 := by rw [wrap64, Nat.mod_mod]
    simp only [evalBinOpOffset, isSignedNegative, scalarModulus_eight, signedHalfModulus_eight,
      Nat.beq_refl, Bool.and_self, wrap64, hw2, nat_ble_eq_decide, nat_beq_eq_decide,
      Nat.sub_eq, Nat.mul_eq, Nat.add_eq]
    generalize bits % 18446744073709551616 = B
    by_cases hB0 : B = 0
    · subst hB0; simp
    · by_cases hs0 : stride = 0
      · subst hs0
        simp only [hB0, decide_true, Bool.or_true, Nat.mul_zero]
        cases decide (9223372036854775808 ≤ B) <;> simp
      · simp [hB0, hs0]
  · have hb : Nat.beq bound 0 = false := by
      rw [nat_beq_eq_decide]; simp [hb0]
    simp [hb]

/-- **Repaired, universal lockstep** (`DIV-LM-D6-OFFSET-DISABLED-TAG`): for *every* borrow
entry (in particular a `.disabled` one — no hypothesis constrains `entry.perm`), every
in-bounds pointer, every 8-byte `isize` count (zero, positive, and negative), and every
pointee stride, `evalPtrOffsetBinOpProto` steps exactly when Miri's `ptr_offset_inbounds`
succeeds, to the same offset, preserving the provenance tag. -/
theorem div_lm_d6_offset_disabled_tag_repaired_agrees (s : ProtoMachineState) (lhsOp : Operand)
    (ptrVal : ProvenancePtr) (offsetSc : ScalarInt) (entry : ProtoBorrowEntry) (stride bound : Nat)
    (hlook : lookupProtoBorrow s.memory.borrows ptrVal.tag = .some entry)
    (hstride : pointeeElemByteStride s.body.localDecls s.body.layouts lhsOp = .some stride)
    (hbnd : ptrAllocByteBoundProto s entry = .some bound)
    (hptr : layoutPointerBytes s.body.layouts = 8) (hsz : offsetSc.sizeBytes = 8)
    (hin : ptrVal.offsetBytes ≤ bound) (hlt : bound < 2 ^ 63) :
    evalPtrOffsetBinOpProto s lhsOp ptrVal 8 offsetSc =
      match miriPtrOffsetInbounds true bound ptrVal.offsetBytes (isizeValue offsetSc * (stride : Int)) with
      | .some n => .ok (.ptr { ptrVal with offsetBytes := n } 8) s
      | .none => .ub := by
  unfold evalPtrOffsetBinOpProto
  rw [hlook]
  simp only
  rw [hstride]
  simp only
  rw [hbnd]
  simp only [hptr]
  rw [evalBinOpOffset_effBound_eq_of_le ptrVal offsetSc stride bound hsz hin,
    evalBinOpOffset_lockstep_miri ptrVal offsetSc stride bound hsz hin hlt]
  cases miriPtrOffsetInbounds true bound ptrVal.offsetBytes (isizeValue offsetSc * (stride : Int)) <;> rfl

/-- **Dead-allocation universal lockstep** (`DIV-LM-D6-OFFSET-DISABLED-TAG` +
`WitLM3_1.lm31OffsetDisabledDeadZeroBody` + `D2` storage revival): when the target
allocation is dead (`ptrAllocByteBoundProto s entry = .some 0`), at *any* in-range pointer
offset `ptrVal.offsetBytes < 2^63` (including `offsetBytes > 0`, e.g. `offsetBytes = 8`
after an earlier offset before `StorageDead`), `evalPtrOffsetBinOpProto` agrees with
`miriPtrOffsetInbounds false allocSize ptrVal.offsetBytes (isizeValue offsetSc * stride)`:
zero-delta offsets succeed and preserve `ptrVal`, while all non-zero-delta offsets fault
with `.ub`. -/
theorem div_lm_d6_offset_dead_alloc_lockstep_miri (s : ProtoMachineState) (lhsOp : Operand)
    (ptrVal : ProvenancePtr) (offsetSc : ScalarInt) (entry : ProtoBorrowEntry)
    (stride allocSize : Nat)
    (hlook : lookupProtoBorrow s.memory.borrows ptrVal.tag = .some entry)
    (hstride : pointeeElemByteStride s.body.localDecls s.body.layouts lhsOp = .some stride)
    (hbnd : ptrAllocByteBoundProto s entry = .some 0)
    (hptr : layoutPointerBytes s.body.layouts = 8) (hsz : offsetSc.sizeBytes = 8)
    (hoff : ptrVal.offsetBytes < 2 ^ 63) :
    evalPtrOffsetBinOpProto s lhsOp ptrVal 8 offsetSc =
      match miriPtrOffsetInbounds false allocSize ptrVal.offsetBytes
          (isizeValue offsetSc * (stride : Int)) with
      | .some n => .ok (.ptr { ptrVal with offsetBytes := n } 8) s
      | .none => .ub := by
  unfold evalPtrOffsetBinOpProto
  rw [hlook]; simp only; rw [hstride]; simp only; rw [hbnd]; simp only [hptr, Nat.beq_refl, Bool.true_and]
  obtain ⟨a, o⟩ := ptrVal
  obtain ⟨bits, sz⟩ := offsetSc
  simp only at hsz hoff ⊢
  subst hsz
  simp only [Nat.reducePow] at hoff
  have hB : bits % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have hw2 : wrapScalarBits (bits % 18446744073709551616) 18446744073709551616 =
      bits % 18446744073709551616 := by rw [wrap64, Nat.mod_mod]
  simp only [evalBinOpOffset, isSignedNegative, scalarModulus_eight, signedHalfModulus_eight,
    Nat.beq_refl, Bool.and_self, wrap64, hw2, nat_ble_eq_decide, nat_beq_eq_decide,
    isizeValue, intValueOfBits, Nat.reducePow, Nat.reduceSub,
    true_and, Nat.sub_eq, Nat.mul_eq, Nat.add_eq]
  generalize bits % 18446744073709551616 = B at hB ⊢
  have ho_not : ¬ (9223372036854775808 ≤ o) := by omega
  by_cases hneg : 9223372036854775808 ≤ B
  · have hB0 : ¬ (B = 0) := by omega
    simp only [hneg, hB0, decide_true, decide_false, Bool.false_or, ite_true]
    have hInt : ((B : Int) - ((18446744073709551616 : Nat) : Int)) * (stride : Int) =
        -((((18446744073709551616 - B) * stride : Nat)) : Int) := by
      rw [Int.natCast_mul, Int.ofNat_sub (Nat.le_of_lt hB), ← Int.neg_mul, Int.neg_sub]
    rw [hInt, miriPtrOffsetInbounds_false_neg]
    by_cases hs0 : stride = 0
    · subst hs0
      simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_le, decide_true, ↓reduceIte, ho_not,
        decide_false, Bool.not_false]
      rfl
    · simp only [hs0, decide_false]
      generalize hP : (18446744073709551616 - B) * stride = P
      have hPpos : 0 < P := by
        rw [← hP]
        exact Nat.mul_pos (Nat.sub_pos_of_lt hB) (Nat.pos_of_ne_zero hs0)
      clear hP hs0 hB0
      have hPne0 : ¬ (P = 0) := Nat.ne_of_gt hPpos
      simp only [hPne0, ↓reduceIte]
      by_cases h1 : 9223372036854775808 ≤ P
      · simp only [h1, decide_true, Bool.not_true, Bool.false_and]
      · simp only [h1, decide_false, Bool.not_false, Bool.true_and]
        by_cases h2 : P ≤ o
        · have ho_ne : ¬ (o - P = o) := by omega
          have ho_le0 : ¬ (o ≤ 0) := by omega
          simp only [h2, ho_ne, ho_le0, decide_true, decide_false, Bool.and_false, Bool.false_and,
            Bool.or_false]
        · simp only [h2, decide_false]
  · simp only [hneg, decide_false, ite_false]
    rw [← Int.natCast_mul, miriPtrOffsetInbounds_false_nonneg]
    by_cases hB0 : B = 0
    · subst hB0
      simp only [Nat.zero_mul, Nat.add_zero, decide_true, Bool.true_or, ho_not,
        decide_false, Bool.not_false, ↓reduceIte]
      rfl
    · by_cases hs0 : stride = 0
      · subst hs0
        simp only [Nat.mul_zero, Nat.add_zero, decide_true, Bool.or_true, ho_not,
          decide_false, Bool.not_false, ↓reduceIte]
        rfl
      · simp only [hB0, hs0, decide_false, Bool.or_self]
        generalize hQ : B * stride = Q
        have hQpos : 0 < Q := by
          rw [← hQ]
          exact Nat.mul_pos (Nat.pos_of_ne_zero hB0) (Nat.pos_of_ne_zero hs0)
        clear hQ hs0 hB0
        have hQne0 : ¬ (Q = 0) := Nat.ne_of_gt hQpos
        simp only [hQne0, ↓reduceIte]
        by_cases h1 : 9223372036854775808 ≤ Q
        · simp only [h1, decide_true]
        · simp only [h1, decide_false]
          by_cases h2 : 9223372036854775808 ≤ o + Q
          · simp only [h2, decide_true]
          · have hoQ_ne : ¬ (o + Q = o) := by omega
            have hoQ_le0 : ¬ (o + Q ≤ 0) := by omega
            simp only [h2, hoQ_ne, hoQ_le0, decide_false, Bool.and_false, Bool.false_and,
              Bool.or_false]

/-- Concrete lockstep instances: zero offset, positive stride, and a negative `isize`
count, each agreeing with `miriPtrOffsetInbounds` on a 4-byte allocation. -/
theorem div_lm_d6_offset_lockstep_examples :
    miriPtrOffsetInbounds true 4 0 (isizeValue ⟨0, 8⟩ * 1) = .some 0 ∧
    miriPtrOffsetInbounds true 4 0 (isizeValue ⟨3, 8⟩ * 1) = .some 3 ∧
    miriPtrOffsetInbounds true 4 3 (isizeValue ⟨18446744073709551615, 8⟩ * 1) = .some 2 ∧
    miriPtrOffsetInbounds true 4 0 (isizeValue ⟨5, 8⟩ * 1) = .none ∧
    evalBinOpOffset ⟨1, 0⟩ 8 ⟨0, 8⟩ 1 (.some 4) 8 = .some ⟨1, 0⟩ ∧
    evalBinOpOffset ⟨1, 0⟩ 8 ⟨3, 8⟩ 1 (.some 4) 8 = .some ⟨1, 3⟩ ∧
    evalBinOpOffset ⟨1, 3⟩ 8 ⟨18446744073709551615, 8⟩ 1 (.some 4) 8 = .some ⟨1, 2⟩ ∧
    evalBinOpOffset ⟨1, 0⟩ 8 ⟨5, 8⟩ 1 (.some 4) 8 = .none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ### 8. `DIV-LM-ENUM-SET-DISCR-UNINIT` (`P2_precision`) -/

/-- `Option<u32>`. -/
def optionU32TyP : Ty := { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 0 }
/-- `Option<u32>` local. -/
def optionU32DeclP : LocalDecl := { mutability := .mut, ty := optionU32TyP, debugName := none }
/-- `(_loc as Some).0`. -/
def somePayloadPlace (loc : Nat) : Place :=
  { local_ := loc, projection := [.downcast (some "Some") 1, .field 0 u32Ty] }

/-- `SetDiscriminant` on a fresh (`.uninit`) enum local:
```rust
// StorageLive(_2); discriminant(_2) = VARIANT; TAIL
```
-/
def setDiscrUninitMir (variantIdx : Nat) (tail : List StatementKind) : CapturedMir :=
  ptrBody "witness::set_discriminant_uninit" [isizeDeclP, u32Decl, optionU32DeclP]
    ([.storageLive 2, .setDiscriminant (local_ 2) variantIdx] ++ tail)

/-- Observe the discriminant. -/
def setDiscrObsTail : List StatementKind :=
  [.assign (local_ 0) (.discriminant (local_ 2)), .storageDead 2]

/-- Read the (never written) `Some` payload. -/
def setDiscrPayloadTail : List StatementKind :=
  [.assign (local_ 0) (.use (.copy (somePayloadPlace 2))), .storageDead 2]

/-- Unpatched `Trusted` faults on `SetDiscriminant` of an `.uninit` local, universally. -/
theorem div_lm_enum_set_discr_trusted_uninit_ub (s : MachineState) (loc variantIdx : Nat)
    (span : String) (decls : List LocalDecl) (layouts : LayoutTable)
    (h : get? s.frame.locals loc = .some .uninit) :
    evalStmt s ⟨.setDiscriminant ⟨loc, .nil⟩ variantIdx, span⟩ decls layouts = MirStepNode.fail .ub := by
  simp [evalStmt, h]

/-- ... and concretely on the witness programs. -/
theorem div_lm_enum_set_discr_trusted_faults :
    trustedFaults (setDiscrUninitMir 1 setDiscrObsTail) [] [.scalar ⟨5, 4⟩] 10 = true ∧
    trustedFaults (setDiscrUninitMir 0 setDiscrObsTail) [] [.scalar ⟨5, 4⟩] 10 = true := by
  decide +kernel

/-- lean-miri `Discriminant.writeDiscriminant` (`lean-miri/vendor/Miri/Interpreter/Discriminant.lean:158`)
on Anneal's local-slot abstraction: the destination is never read; an `.uninit` slot
gets its tag written with every payload byte still uninitialized; an initialized enum
value keeps its payload; a dead (or missing) local is UB (`none`). -/
def miriWriteDiscriminant (slot : Option LocalSlot) (variantIdx : Nat) : Option LocalSlot :=
  match slot with
  | .some .uninit => .some (.init (.aggregate variantIdx .nil))
  | .some (.init (.aggregate _ fields)) => .some (.init (.aggregate variantIdx fields))
  | _ => .none

/-- **Repaired, universal lockstep** (`DIV-LM-ENUM-SET-DISCR-UNINIT`): for every state,
local, and variant (with an ADT-typed or undeclared destination and no protector
conflict), `SetDiscriminant` steps exactly as `miriWriteDiscriminant` across `.uninit`,
`.init (.aggregate v fields)`, and `.dead`, followed by the frame-scoped foreign-write
invalidation of the destination's borrows. -/
theorem div_lm_enum_set_discr_uninit_repaired_agrees (cfg : ProtoConfig) (s : ProtoMachineState)
    (loc variantIdx : Nat) (span : String)
    (hdecl : setDiscrDeclOk s.body.localDecls loc = true)
    (hconf : hasProtectedWriteConflictProto cfg s.memory.borrows s.memory.activeProtectors
      (currentFrameDepth s) loc .none = false) :
    evalStmtProto cfg s ⟨.setDiscriminant ⟨loc, .nil⟩ variantIdx, span⟩ =
      match miriWriteDiscriminant (get? s.frame.locals loc) variantIdx with
      | .some slot' =>
        .step (advanceStmtProto
          { s with
            frame := { s.frame with locals := s.frame.locals.set loc slot' }
            memory := { s.memory with
              borrows := invalidateConflictingBorrowsProto cfg s.memory.borrows
                s.memory.activeProtectors (currentFrameDepth s) loc .none } })
      | .none => .ub := by
  simp only [evalStmtProto, evalSetDiscriminantProto]
  cases hslot : get? s.frame.locals loc with
  | none => simp [miriWriteDiscriminant]
  | some slot =>
    have hlt : loc < s.frame.locals.length := by
      simp only [get?] at hslot
      exact (List.getElem?_eq_some_iff.mp hslot).1
    cases slot with
    | dead => simp [miriWriteDiscriminant]
    | uninit => simp [miriWriteDiscriminant, hdecl, hconf, set?, hlt]
    | init v => cases v <;> simp [miriWriteDiscriminant, hconf, set?, hlt]

/-- Subsequent `Rvalue.discriminant` observes the written variant. -/
theorem div_lm_enum_set_discr_observed :
    runMirProto (setDiscrUninitMir 1 setDiscrObsTail) [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨1, 8⟩) ∧
    runMirProto (setDiscrUninitMir 0 setDiscrObsTail) [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨0, 8⟩) :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-- **Payload safety canary**: reading `(_2 as Some).0` after writing only the tag of an
`.uninit` enum faults with UB (the payload is still uninitialized). -/
theorem div_lm_enum_set_discr_payload_canary :
    runMirProto (setDiscrUninitMir 1 setDiscrPayloadTail) [] [.scalar ⟨5, 4⟩] = .ub :=
  ProtoOutcome.eq_ub_of_isUB (by decide +kernel)

/-- `SetDiscriminant` on a dead local (no `StorageLive`) is UB. -/
def setDiscrDeadMir : CapturedMir :=
  ptrBody "witness::set_discriminant_dead" [isizeDeclP, u32Decl, optionU32DeclP]
    [.setDiscriminant (local_ 2) 1, .assign (local_ 0) (.discriminant (local_ 2))]

/-- Initialized enum: `SetDiscriminant(_1, 1)` on `Some(5)` keeps the payload. -/
def setDiscrInitMir : CapturedMir :=
  { ptrBody "witness::set_discriminant_init" [u32Decl, optionU32DeclP]
      [.setDiscriminant (local_ 1) 1, .assign (local_ 0) (.use (.copy (somePayloadPlace 1)))] with
    fnAbi := fnAbi 1 }

theorem div_lm_enum_set_discr_dead_and_init :
    runMirProto setDiscrDeadMir [] [.scalar ⟨5, 4⟩] = .ub ∧
    runMirProto setDiscrInitMir [] [.aggregate 1 [.scalar ⟨5, 4⟩]] = .ok (.scalar ⟨5, 4⟩) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-! ### Universal frame isolation, protector exemption, and correspondence lemmas -/

/-- A write to `(d, loc)` leaves every entry of another frame unchanged. -/
theorem updateBorrowPermAtProjProto_other_frame (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) (proj : List ProjectionElem) (w : Option Nat)
    (e : ProtoBorrowEntry) (h : e.targetFrameDepth ≠ d) :
    updateBorrowPermAtProjProto cfg borrows prots d loc proj w e = e := by
  have hb : Nat.beq e.targetFrameDepth d = false := by
    rw [nat_beq_eq_decide]; simp [h]
  simp [updateBorrowPermAtProjProto, entryAccessTransitionProto, entryTargetsProto, hb,
    applyProtoTransition]

/-- **Universal frame-isolation theorem** (`DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`):
writing to `(d_active, loc)` (at any sub-place, through any tag or directly) leaves every
`ProtoBorrowEntry` with `targetFrameDepth ≠ d_active` completely unchanged, position by
position. -/
theorem div_mr_caller_borrow_frame_isolation (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (d loc : Nat) (proj : List ProjectionElem) (w : Option Nat) (i : Nat)
    (hi : i < borrows.length) (hd : borrows[i].targetFrameDepth ≠ d) :
    (invalidateConflictingBorrowsAtProjProto cfg borrows prots d loc proj w)[i]? = .some borrows[i] := by
  rw [invalidateConflictingBorrowsAtProjProto, List.getElem?_map, List.getElem?_eq_getElem hi]
  exact congrArg some (updateBorrowPermAtProjProto_other_frame cfg borrows prots d loc proj w _ hd)

/-- Writes never report a protector conflict on another frame's entry. -/
theorem entryAccessTransitionProto_other_frame (cfg : ProtoConfig) (borrows : List ProtoBorrowEntry)
    (prots : List Nat) (kind : TreeBorrowAccessKind) (d loc : Nat) (proj : List ProjectionElem)
    (w : Option Nat) (e : ProtoBorrowEntry) (h : e.targetFrameDepth ≠ d) :
    entryAccessTransitionProto cfg borrows prots kind d loc proj w e = .transition e.perm := by
  have hb : Nat.beq e.targetFrameDepth d = false := by
    rw [nat_beq_eq_decide]; simp [h]
  simp [entryAccessTransitionProto, entryTargetsProto, hb]

/-- `commitFrameWriteProto` installs exactly the given borrow table. -/
theorem commitFrameWriteProto_borrows {s s' : ProtoMachineState} {d loc : Nat} {r : Value}
    {b : List ProtoBorrowEntry} (h : commitFrameWriteProto s d loc r b = .ok s') :
    s'.memory.borrows = b := by
  unfold commitFrameWriteProto at h
  split at h
  · cases h; rfl
  · cases h

/-- **End-to-end frame isolation of direct writes** (`DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`):
every *successful* `writePlaceProto` to a deref-free place `_loc.proj` of the active frame
(depth `currentFrameDepth s`) leaves every borrow entry of every other frame unchanged,
position by position. -/
theorem writePlaceProto_direct_frame_isolation (cfg : ProtoConfig) (s s' : ProtoMachineState)
    (loc : Nat) (proj : List ProjectionElem) (v : Value)
    (hnd : projectionHasDeref proj = false)
    (h : writePlaceProto cfg s ⟨loc, proj⟩ v = .ok s')
    (i : Nat) (hi : i < s.memory.borrows.length)
    (hd : s.memory.borrows[i].targetFrameDepth ≠ currentFrameDepth s) :
    s'.memory.borrows[i]? = .some s.memory.borrows[i] := by
  have hb : s'.memory.borrows = invalidateConflictingBorrowsAtProjProto cfg s.memory.borrows
      s.memory.activeProtectors (currentFrameDepth s) loc proj .none := by
    unfold writePlaceProto at h
    split at h
    · rename_i rest heq
      simp only at heq
      subst heq
      simp [projectionHasDeref] at hnd
    · simp only [hnd] at h
      repeat' split at h
      all_goals first | exact commitFrameWriteProto_borrows h | cases h
  rw [hb]
  exact div_mr_caller_borrow_frame_isolation cfg _ _ _ _ _ _ i hi hd

/-- **End-to-end frame isolation of deref writes** (`DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`
+ `DIV-MR-CALL-TARGET-LOCAL`): every *successful* write through `*_loc` whose tag resolves
to `entry` leaves every borrow entry of every frame other than the pointee's frame
`entry.targetFrameDepth` unchanged, position by position. -/
theorem writePlaceProto_deref_frame_isolation (cfg : ProtoConfig) (s s' : ProtoMachineState)
    (loc : Nat) (rest : List ProjectionElem) (v : Value) (ptrVal : ProvenancePtr) (sz : Nat)
    (entry : ProtoBorrowEntry)
    (hloc : get? s.frame.locals loc = .some (.init (.ptr ptrVal sz)))
    (hlook : lookupProtoBorrow s.memory.borrows ptrVal.tag = .some entry)
    (h : writePlaceProto cfg s ⟨loc, .deref :: rest⟩ v = .ok s')
    (i : Nat) (hi : i < s.memory.borrows.length)
    (hd : s.memory.borrows[i].targetFrameDepth ≠ entry.targetFrameDepth) :
    s'.memory.borrows[i]? = .some s.memory.borrows[i] := by
  have hb : s'.memory.borrows = invalidateConflictingBorrowsAtProjProto cfg s.memory.borrows
      s.memory.activeProtectors entry.targetFrameDepth entry.targetLocal
      (appendProjections entry.targetProjection rest) (.some ptrVal.tag) := by
    unfold writePlaceProto at h
    simp only [hloc, hlook] at h
    repeat' split at h
    all_goals first | exact commitFrameWriteProto_borrows h | cases h
  rw [hb]
  exact div_mr_caller_borrow_frame_isolation cfg _ _ _ _ _ _ i hi hd

/-- The deallocation rule agrees with MiniRust's `PermissionProt::prevents_deallocation`
under the embedding of Anneal's six states (every entry has had its initial local read;
`.reservedIM` fails closed). -/
def toMiniRustProtPerm : TreeBorrowPerm → MiniRustSpec.Gen.PermissionProt
  | .cell => .Cell
  | .reservedFrz c => .Reserved true c
  | .reservedIM => .Reserved true false
  | .unique => .Unique
  | .frozen => .Frozen true
  | .disabled => .Disabled

theorem preventsDeallocation_eq_miniRust (p : TreeBorrowPerm) :
    preventsDeallocation p =
      MiniRustSpec.Interp.PermissionProt.prevents_deallocation (toMiniRustProtPerm p) := by
  cases p <;> rfl

/-- `preventsDeallocation` truth table (`.cell`/`.disabled` exempt). -/
theorem preventsDeallocation_table :
    preventsDeallocation .cell = false ∧ preventsDeallocation .disabled = false ∧
    preventsDeallocation .unique = true ∧ preventsDeallocation (.reservedFrz false) = true ∧
    preventsDeallocation (.reservedFrz true) = true ∧ preventsDeallocation .frozen = true ∧
    preventsDeallocation .reservedIM = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Additional B1 adversarial hardening: reborrow/retag propagation, `.cell` vs `.reservedIM`,
disabled-tag deref UB, and `SetDiscriminant` borrow invalidation / protector conflict -/

/-- Callee that reborrows `_3 = &mut *_2`, retags `_3` (`RetagKind.default`), and writes
`*_3 = *_3 + 37` while its own `_1 = 100`. -/
def calleeReborrowWriteMir : CapturedMir where
  defPath := "witness::callee_reborrow_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 3),
        mkStmt (.retag .fnEntry (local_ 2)),
        mkStmt (.assign (local_ 3) (.ref (.mut false) (derefPlace 2))),
        mkStmt (.retag .default (local_ 3)),
        mkStmt (.assign (derefPlace 3) (.binaryOp .add (.copy (derefPlace 3)) (constU32 37))),
        mkStmt (.assign (local_ 0) (.use (.copy (local_ 1)))),
        mkStmt (.storageDead 3)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

/-- Caller of `calleeReborrowWriteMir`. -/
def callerReborrowWriteMir : CapturedMir where
  defPath := "witness::caller_reborrow_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refMutU32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 2) (.ref (.mut false) (local_ 1)))],
      terminator := mkTerm (.call (fnDefOp "witness::callee_reborrow_write")
        [constU32 100, .move (local_ 2)] (local_ 3) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.binaryOp .mul (.copy (local_ 1)) (constU32 1000))),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 4)) (.copy (local_ 3)))),
        mkStmt (.storageDead 4),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- **Multi-hop reborrow & `Retag` frame-depth propagation canary**
(`DIV-MR-CALL-TARGET-LOCAL`): inside `calleeReborrowWriteMir` (depth `1`), both the
`FnEntry` retag of `_2`, the sub-reborrow `_3 = &mut *_2`, and the `Default` retag of
`_3` inherit `targetFrameDepth = 0` and `targetLocal = 1`; writing through `*_3` mutates
caller `_1` from `5` to `42` while keeping callee `_1 = 100` untouched (`42100`), whereas
unpatched `Trusted` mutates callee `_1` and returns `5137`. -/
theorem div_mr_call_target_local_reborrow_in_callee_canary :
    (stepsProto {} 9 (initProtoState callerReborrowWriteMir [calleeReborrowWriteMir]
        [.scalar ⟨5, 4⟩])).map
      (fun s => (s.memory.borrows.map (fun e => (e.tag, e.targetFrameDepth, e.targetLocal)),
        slotScalarBits? (readFrameLocalProto s 0 1),
        slotScalarBits? (readFrameLocalProto s 1 1))) =
      .some ([(4, 0, 1), (3, 0, 1), (2, 0, 1), (1, 0, 1)], .some 42, .some 100) ∧
    runMirProto callerReborrowWriteMir [calleeReborrowWriteMir] [.scalar ⟨5, 4⟩] =
      .ok (.scalar ⟨42100, 4⟩) ∧
    trustedRunScalar? callerReborrowWriteMir [calleeReborrowWriteMir] [.scalar ⟨5, 4⟩] 35 =
      .some (5137, 4) :=
  ⟨by decide +kernel, ProtoOutcome.eq_of_okScalar? (by decide +kernel), by decide +kernel⟩

/-- **Universal reborrow frame-depth inheritance** (`DIV-MR-CALL-TARGET-LOCAL`): whenever
`&*ptr`, `&mut *ptr`, `&raw const *ptr`, or `&raw mut *ptr` succeeds on a pointer stored in
`loc` whose tag resolves to `parent`, the newly minted head entry in `s'.memory.borrows`
inherits `(parent.targetFrameDepth, parent.targetLocal)`. -/
theorem reborrow_inherits_targetFrameDepth (cfg : ProtoConfig) (s : ProtoMachineState)
    (loc : Nat) (rest : List ProjectionElem) (ptrVal : ProvenancePtr) (sz : Nat)
    (parent : ProtoBorrowEntry)
    (hloc : get? s.frame.locals loc = .some (.init (.ptr ptrVal sz)))
    (hlook : lookupProtoBorrow s.memory.borrows ptrVal.tag = .some parent) :
    (∀ bk v s',
      evalRvalueProto cfg s (.ref bk ⟨loc, .deref :: rest⟩) = .ok v s' →
      ∃ child tail, s'.memory.borrows = child :: tail ∧
        child.targetFrameDepth = parent.targetFrameDepth ∧
        child.targetLocal = parent.targetLocal ∧
        child.parentTag = .some ptrVal.tag) ∧
    (∀ mutability v s',
      evalRvalueProto cfg s (.rawPtr mutability ⟨loc, .deref :: rest⟩) = .ok v s' →
      ∃ child, s'.memory.borrows = child :: s.memory.borrows ∧
        child.targetFrameDepth = parent.targetFrameDepth ∧
        child.targetLocal = parent.targetLocal ∧
        child.parentTag = .some ptrVal.tag) := by
  constructor
  · intro bk v s' h
    simp only [evalRvalueProto, hloc, hlook] at h
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> try cases h
    exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  · intro mutability v s' h
    simp only [evalRvalueProto, hloc, hlook] at h
    split at h <;> try cases h
    split at h <;> try cases h
    exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- **Universal direct-write transition separation** (`DIV-MR-TB-TWOPHASE-DIRECT-WRITE`):
an unprotected direct write (`writerTag = .none`) overlapping `e` at `(d, loc, proj)`
disables `.reservedFrz c` while preserving `.cell` and unprotected `.reservedIM`. -/
theorem direct_write_disables_reservedFrz_preserves_cell_and_reservedIM
    (borrows : List ProtoBorrowEntry) (prots : List Nat) (d loc : Nat)
    (proj : List ProjectionElem) (e : ProtoBorrowEntry)
    (htgt : entryTargetsProto e d loc = true)
    (hov : projectionsOverlap e.targetProjection proj = true)
    (hprot : isProtectedProto prots e = false) :
    (∀ c, updateBorrowPermAtProjProto {} borrows prots d loc proj .none
        { e with perm := .reservedFrz c } = { e with perm := .disabled }) ∧
    updateBorrowPermAtProjProto {} borrows prots d loc proj .none
        { e with perm := .reservedIM } = { e with perm := .reservedIM } ∧
    updateBorrowPermAtProjProto {} borrows prots d loc proj .none
        { e with perm := .cell } = { e with perm := .cell } := by
  have htgt' : ∀ p, entryTargetsProto { e with perm := p } d loc = true := fun _ => htgt
  have hprot' : ∀ p, isProtectedProto prots { e with perm := p } = false := fun _ => hprot
  refine ⟨fun c => ?_, ?_, ?_⟩ <;>
    simp [updateBorrowPermAtProjProto, entryAccessTransitionProto, htgt', hov, hprot',
      treeBorrowNodeAccess, applyProtoTransition]

/-- `&mut UnsafeCell<u32>` local declaration. -/
def refMutUnsafeCellU32Decl : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .ref .mut (.adt "core::cell::UnsafeCell" [.uint .u32]), layoutIdx := 0 },
    debugName := none }

/-- Canary body: take `_2 = &mut _1` (`.reservedIM`) and `_3 = &_1` (`.cell`) on
`_1 : UnsafeCell<u32>`, perform a direct root write `_1 = UnsafeCell(44)`, and then read
through both `(*_2).0` and `(*_3).0`. -/
def unsafeCellDirectWriteSurvivesMir : CapturedMir :=
  { ptrBody "witness::unsafe_cell_direct_write_survives"
      [u32Decl, unsafeCellU32Decl, refMutUnsafeCellU32Decl, refSharedUnsafeCellU32Decl,
       u32Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .assign (local_ 2) (.ref (.mut false) (local_ 1)),
       .assign (local_ 3) (.ref .shared (local_ 1)),
       .assign (local_ 1) (.aggregate (.adt "core::cell::UnsafeCell" 0 none) [constU32 44]),
       .assign (local_ 4) (.use (.copy (derefFieldPlace 2 0 u32Ty))),
       .assign (local_ 5) (.use (.copy (derefFieldPlace 3 0 u32Ty))),
       .assign (local_ 0) (.binaryOp .add (.copy (local_ 4)) (.copy (local_ 5))),
       .storageDead 5, .storageDead 4, .storageDead 3, .storageDead 2] with
    fnAbi := fnAbiUnsafeCellU32Arg, layouts := unsafeCellU32Layouts }

/-- **Concrete `.reservedIM` & `.cell` survival canary** (`DIV-MR-TB-TWOPHASE-DIRECT-WRITE`):
unlike `Freeze` `.reservedFrz` (which `twoPhaseDirectWriteTreeBorrowsGap` disables on a
direct root write), unprotected `.reservedIM` (`&mut UnsafeCell<u32>`) and `.cell`
(`&UnsafeCell<u32>`) both survive the direct write `_1 = UnsafeCell(44)` and observe
`44 + 44 = 88`. -/
theorem div_mr_tb_twophase_direct_write_reservedIM_and_cell_survive_canary :
    runMirProto unsafeCellDirectWriteSurvivesMir [] [initUnsafeCellU32] =
      .ok (.scalar ⟨88, 4⟩) :=
  ProtoOutcome.eq_of_okScalar? (by decide +kernel)

/-- **Protected deallocation separation between `.cell` and `.reservedIM`**
(`DIV-MR-TB-FNENTRY-LOCAL-DEALLOC` + `DIV-MR-TB-UNSAFECELL-PROTECTED-IM`): for a protected
entry targeting `(d, loc)`, `.cell` and `.disabled` do not block `StorageDead`/`Return`
(`hasProtectedLocalBorrowProto = false`), whereas `.reservedIM`, `.reservedFrz c`,
`.unique`, and `.frozen` block deallocation (`hasProtectedLocalBorrowProto = true`). -/
theorem hasProtectedLocalBorrowProto_cell_exempt_reservedIM_blocks
    (prots : List Nat) (d loc : Nat) (e : ProtoBorrowEntry)
    (htgt : entryTargetsProto e d loc = true)
    (hprot : isProtectedProto prots e = true) :
    hasProtectedLocalBorrowProto {} [{ e with perm := .cell }] prots d loc = false ∧
    hasProtectedLocalBorrowProto {} [{ e with perm := .disabled }] prots d loc = false ∧
    hasProtectedLocalBorrowProto {} [{ e with perm := .reservedIM }] prots d loc = true ∧
    (∀ c, hasProtectedLocalBorrowProto {} [{ e with perm := .reservedFrz c }] prots d loc = true) ∧
    hasProtectedLocalBorrowProto {} [{ e with perm := .unique }] prots d loc = true ∧
    hasProtectedLocalBorrowProto {} [{ e with perm := .frozen }] prots d loc = true := by
  have htgt' : ∀ p, entryTargetsProto { e with perm := p } d loc = true := fun _ => htgt
  have hprot' : ∀ p, isProtectedProto prots { e with perm := p } = true := fun _ => hprot
  refine ⟨?_, ?_, ?_, fun c => ?_, ?_, ?_⟩ <;>
    simp [hasProtectedLocalBorrowProto, htgt', hprot', deallocBlockedBy, preventsDeallocation]

/-- **Frame isolation of `disableFrameBorrowsProto` on `Return`**: entries belonging to
other frames (`targetFrameDepth ≠ d`) are untouched, while entries of the returning frame
(`targetFrameDepth = d ∧ targetLocal < nLocals`) are disabled and marked `allocDead = true`. -/
theorem disableFrameBorrowsProto_frame_isolation (borrows : List ProtoBorrowEntry)
    (d nLocals i : Nat) (hi : i < borrows.length) :
    (borrows[i].targetFrameDepth ≠ d →
      (disableFrameBorrowsProto borrows d nLocals)[i]? = .some borrows[i]) ∧
    (borrows[i].targetFrameDepth = d ∧ borrows[i].targetLocal < nLocals →
      (disableFrameBorrowsProto borrows d nLocals)[i]? =
        .some { borrows[i] with perm := .disabled, allocDead := true }) := by
  rw [disableFrameBorrowsProto, List.getElem?_map, List.getElem?_eq_getElem hi]
  constructor
  · intro hne
    have hb : Nat.beq borrows[i].targetFrameDepth d = false := by
      rw [nat_beq_eq_decide]; simp [hne]
    simp [hb]
  · rintro ⟨heq, hlt⟩
    have hb : Nat.beq borrows[i].targetFrameDepth d = true := by
      rw [nat_beq_eq_decide]; simp [heq]
    have hl : Nat.blt borrows[i].targetLocal nLocals = true :=
      Nat.blt_eq.mpr hlt
    simp [hb, hl]

/-- Callee returning a raw pointer `&raw mut _1` to its own local `_1` (no `FnEntry`
protector, so `Return` itself succeeds, but disables the callee frame's borrows). -/
def calleeReturnRawPtrToLocalMir : CapturedMir where
  defPath := "witness::callee_return_raw_ptr_to_local"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [ptrMutU32Decl, u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.rawPtr .mut (local_ 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- Caller that calls `calleeReturnRawPtrToLocalMir` and dereferences the returned dangling
pointer `*_2`. -/
def callerDerefReturnedCalleeRawPtrMir : CapturedMir where
  defPath := "witness::caller_deref_returned_callee_raw_ptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, ptrMutU32Decl]
  basicBlocks := [
    { statements := [mkStmt (.storageLive 2)],
      terminator := mkTerm (.call (fnDefOp "witness::callee_return_raw_ptr_to_local")
        [.copy (local_ 1)] (local_ 2) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy (derefPlace 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- **Dangling callee raw-pointer return canary**: returning `&raw mut _1` from a callee
disables its borrow at `Return` (`disableFrameBorrowsProto`), so dereferencing it in the
caller faults with `.ub` (whereas unpatched `Trusted` fails to disable callee borrows on
`Return` and silently reads the caller's `_1 = 5`!). -/
theorem div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub :
    runMirProto callerDerefReturnedCalleeRawPtrMir [calleeReturnRawPtrToLocalMir]
      [.scalar ⟨5, 4⟩] = .ub ∧
    trustedRunScalar? callerDerefReturnedCalleeRawPtrMir [calleeReturnRawPtrToLocalMir]
      [.scalar ⟨5, 4⟩] 20 = .some (5, 4) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), by decide +kernel⟩

/-- `*mut char` local declaration. -/
def ptrMutCharDeclP : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut .char, layoutIdx := 0 }, debugName := none }

/-- Projected `move (*_3)` of a raw-overwritten `char` through `_3 : *mut char`. -/
def rawOverwriteCharDerefMoveMir (code : Nat) : CapturedMir :=
  ptrBody "witness::raw_overwrite_char_deref_move"
    [charDeclP, charDeclP, ptrMutU32Decl, ptrMutCharDeclP]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (derefPlace 2) (.use (constU32 code)),
     .assign (local_ 3) (.rawPtr .mut (local_ 1)),
     .assign (local_ 0) (.use (.move (derefPlace 3))),
     .storageDead 3, .storageDead 2]

/-- **Projected `move (*_3)` `char` validation canary** (`DIV-LM-RAW-OVERWRITE-CHAR-COPY`):
moving out of a dereferenced `*mut char` place validates the loaded `char` scalar, faulting
with `.ub` on `0xD800`, `0xDFFF`, and `0x110000` while accepting `0x41`, `0xD7FF`, `0xE000`,
and `0x10FFFF`. -/
theorem div_lm_raw_overwrite_char_projected_move_canary :
    runMirProto (rawOverwriteCharDerefMoveMir 0xD800) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharDerefMoveMir 0xDFFF) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharDerefMoveMir 0x110000) [] [.scalar ⟨0x41, 4⟩] = .ub ∧
    runMirProto (rawOverwriteCharDerefMoveMir 0x41) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0x41, 4⟩) ∧
    runMirProto (rawOverwriteCharDerefMoveMir 0xD7FF) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0xD7FF, 4⟩) ∧
    runMirProto (rawOverwriteCharDerefMoveMir 0xE000) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0xE000, 4⟩) ∧
    runMirProto (rawOverwriteCharDerefMoveMir 0x10FFFF) [] [.scalar ⟨0x41, 4⟩] = .ok (.scalar ⟨0x10FFFF, 4⟩) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel), ProtoOutcome.eq_of_okScalar? (by decide +kernel),
   ProtoOutcome.eq_of_okScalar? (by decide +kernel)⟩

/-- `evalRetagProto` on an `.uninit` or `.dead` `.rawPtr` local faults with `.ub` even for
`RetagKind.raw` (matching `Trusted.evalStmt`, which evaluates `evalOperand (.copy place)`
first). -/
theorem evalRetagProto_raw_uninit_or_dead_ub (cfg : ProtoConfig) (s : ProtoMachineState)
    (loc : Nat) (m : Mutability) (pt : RigidTy) (lidx : Nat)
    (hty : placeTy s.body.localDecls s.body.layouts ⟨loc, .nil⟩ =
      .some { kind := .rawPtr m pt, layoutIdx := lidx }) :
    (get? s.frame.locals loc = .some .uninit →
      evalRetagProto cfg s .raw ⟨loc, .nil⟩ = .ub) ∧
    (get? s.frame.locals loc = .some .dead →
      evalRetagProto cfg s .raw ⟨loc, .nil⟩ = .ub) := by
  constructor <;> intro hslot <;> simp [evalRetagProto, hty, hslot]

/-- `lookupProtoBorrow borrows tag = .some entry` implies `entry ∈ borrows` and
`entry.tag = tag`. -/
theorem lookupProtoBorrow_mem_and_tag {borrows : List ProtoBorrowEntry} {tag : Nat}
    {entry : ProtoBorrowEntry} (h : lookupProtoBorrow borrows tag = .some entry) :
    entry ∈ borrows ∧ entry.tag = tag := by
  induction borrows with
  | nil => cases h
  | cons hd tl ih =>
    unfold lookupProtoBorrow at h
    cases hb : Nat.beq hd.tag tag
    · rw [hb] at h
      obtain ⟨hm, ht⟩ := ih h
      exact ⟨List.mem_cons_of_mem hd hm, ht⟩
    · rw [hb] at h
      injection h with heq
      subst heq
      exact ⟨List.Mem.head tl, Nat.eq_of_beq_eq_true hb⟩

theorem isAncestorOrSelfProto_refl (borrows : List ProtoBorrowEntry) (tag : Nat) :
    isAncestorOrSelfProto borrows tag tag = true := by
  unfold isAncestorOrSelfProto
  cases borrows.length <;> simp [isAncestorOrSelfAux, Nat.beq_refl]

theorem projectionsOverlap_append_self_fieldOnly (p rest : List ProjectionElem)
    (hp : isFieldOnlyProj p = true) :
    projectionsOverlap p (appendProjections p rest) = true := by
  have haux : ∀ (q : List ProjectionElem), isFieldOnlyProj q = true →
      stripTransparentProjections q = q ∧
      normalizeSubsliceProjections q = q ∧
      stripTransparentProjections (appendProjections q rest) =
        appendProjections q (stripTransparentProjections rest) ∧
      normalizeSubsliceProjections (appendProjections q (stripTransparentProjections rest)) =
        appendProjections q (normalizeSubsliceProjections (stripTransparentProjections rest)) ∧
      projectionsOverlapAux q
        (appendProjections q (normalizeSubsliceProjections (stripTransparentProjections rest))) = true := by
    intro q hq
    induction q with
    | nil => simp [appendProjections, stripTransparentProjections, normalizeSubsliceProjections,
        normalizeSubsliceProjectionsAux, projectionsOverlapAux]
    | cons pe tl ih =>
      cases pe <;> simp only [isFieldOnlyProj] at hq <;> try contradiction
      case field idx ty =>
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih hq
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [stripTransparentProjections, h1]
        · simp [normalizeSubsliceProjections, normalizeSubsliceProjectionsAux]
          exact h2
        · simp [appendProjections, stripTransparentProjections, h3]
        · simp [appendProjections, normalizeSubsliceProjections, normalizeSubsliceProjectionsAux]
          exact h4
        · simp [appendProjections, projectionsOverlapAux, Nat.beq_refl, h5]
      case downcast nm idx =>
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih hq
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [stripTransparentProjections, h1]
        · simp [normalizeSubsliceProjections, normalizeSubsliceProjectionsAux]
          exact h2
        · simp [appendProjections, stripTransparentProjections, h3]
        · simp [appendProjections, normalizeSubsliceProjections, normalizeSubsliceProjectionsAux]
          exact h4
        · simp [appendProjections, projectionsOverlapAux, Nat.beq_refl, h5]
  obtain ⟨h1, h2, h3, h4, h5⟩ := haux p hp
  unfold projectionsOverlap
  rw [h1, h2, h3, h4, h5]

/-- **Universal disabled-tag deref/reborrow/retag UB** (`DIV-LM-D6-OFFSET-DISABLED-TAG`):
while `evalPtrOffsetBinOpProto` allows in-bounds arithmetic on a `.disabled` tag, any
subsequent deref read, deref write, safe reborrow (`&*p`, `&mut *p`), or raw reborrow
(`&raw const *p`, `&raw mut *p`) at *any* byte offset and projection suffix universally
faults with `.ub`. -/
theorem disabled_tag_deref_and_reborrow_ub (s : ProtoMachineState) (loc : Nat)
    (rest : List ProjectionElem) (ptrVal : ProvenancePtr) (sz : Nat)
    (entry : ProtoBorrowEntry) (v : Value) (bk : BorrowKind) (mutability : Mutability)
    (hloc : get? s.frame.locals loc = .some (.init (.ptr ptrVal sz)))
    (hlook : lookupProtoBorrow s.memory.borrows ptrVal.tag = .some entry)
    (hproj : isFieldOnlyProj entry.targetProjection = true)
    (hdis : entry.perm = .disabled) :
    readPlaceProto {} s ⟨loc, .deref :: rest⟩ = .ub ∧
    writePlaceProto {} s ⟨loc, .deref :: rest⟩ v = .ub ∧
    evalRvalueProto {} s (.ref bk ⟨loc, .deref :: rest⟩) = .ub ∧
    evalRvalueProto {} s (.rawPtr mutability ⟨loc, .deref :: rest⟩) = .ub := by
  obtain ⟨hmem, htag⟩ := lookupProtoBorrow_mem_and_tag hlook
  have htgt : entryTargetsProto entry entry.targetFrameDepth entry.targetLocal = true := by
    simp [entryTargetsProto, Nat.beq_refl]
  have hov : projectionsOverlap entry.targetProjection
      (appendProjections entry.targetProjection rest) = true :=
    projectionsOverlap_append_self_fieldOnly entry.targetProjection rest hproj
  have hanc : isAncestorOrSelfProto s.memory.borrows entry.tag ptrVal.tag = true := by
    rw [htag]; exact isAncestorOrSelfProto_refl s.memory.borrows ptrVal.tag
  have hub_kind : ∀ kind,
      accessUBProto {} s.memory.borrows s.memory.activeProtectors kind
        entry.targetFrameDepth entry.targetLocal
        (appendProjections entry.targetProjection rest) (.some ptrVal.tag) = true := by
    intro kind
    unfold accessUBProto
    apply List.any_eq_true.mpr
    refine ⟨entry, hmem, ?_⟩
    simp only [entryAccessTransitionProto, htgt, hov, Bool.and_self, hanc, hdis]
    cases kind <;> cases isProtectedProto s.memory.activeProtectors entry <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [readPlaceProto, hloc, hlook, hub_kind .read]
  · simp [writePlaceProto, hloc, hlook, hub_kind .write]
  · simp [evalRvalueProto, hloc, hlook, hdis]
  · simp [evalRvalueProto, hloc, hlook, hdis]

/-- **Universal `SetDiscriminant` protector-conflict UB** (`DIV-LM-ENUM-SET-DISCR-UNINIT`):
whenever `hasProtectedWriteConflictProto` is `true` on `(currentFrameDepth s, loc)`,
`SetDiscriminant` on `loc` faults with `.ub` across every slot state (`.uninit`,
`.init (.aggregate v fields)`, `.init _`, `.dead`, or `.none`). -/
theorem div_lm_enum_set_discr_protected_conflict_ub (cfg : ProtoConfig) (s : ProtoMachineState)
    (loc variantIdx : Nat) (span : String)
    (hdecl : setDiscrDeclOk s.body.localDecls loc = true)
    (hconf : hasProtectedWriteConflictProto cfg s.memory.borrows s.memory.activeProtectors
      (currentFrameDepth s) loc .none = true) :
    evalStmtProto cfg s ⟨.setDiscriminant ⟨loc, .nil⟩ variantIdx, span⟩ = .ub := by
  simp only [evalStmtProto, evalSetDiscriminantProto]
  cases hslot : get? s.frame.locals loc with
  | none => rfl
  | some slot =>
    cases slot with
    | dead => rfl
    | uninit => simp [hdecl, hconf]
    | init v => cases v <;> simp [hconf]

/-- `&Option<u32>` local declaration. -/
def refSharedOptionU32DeclP : LocalDecl :=
  { mutability := .mut,
    ty := { kind := .ref .not (.adt "core::option::Option" [.uint .u32]), layoutIdx := 0 },
    debugName := none }

/-- Canary 1: unprotected shared borrow `_2 = &_1` on `Option<u32>` (either `.uninit` or
`.init`), followed by `SetDiscriminant(_1, 1)`, followed by a deref discriminant read
`_0 = discriminant(*_2)` (which reads `*_2` through `readPlaceProto`). -/
def setDiscrInvalidatesBorrowMir (initFirst : Bool) : CapturedMir :=
  { ptrBody "witness::set_discr_invalidates_borrow"
      [isizeDeclP, optionU32DeclP, refSharedOptionU32DeclP]
      ((match initFirst with
        | true => []
        | false => [.deinit (local_ 1)]) ++
       [.storageLive 2,
        .assign (local_ 2) (.ref .shared (local_ 1)),
        .setDiscriminant (local_ 1) 1,
        .assign (local_ 0) (.discriminant (derefPlace 2)),
        .storageDead 2]) with
    fnAbi := fnAbi 1 }

/-- Canary 2: protected shared borrow `_2 = &_1`, `Retag([fn entry], _2)`, followed by
`SetDiscriminant(_1, 1)` on either `.init` or `.uninit` `Option<u32>`. -/
def setDiscrProtectedConflictMir (uninitSlot : Bool) : CapturedMir :=
  { ptrBody "witness::set_discr_protected_conflict"
      [isizeDeclP, optionU32DeclP, refSharedOptionU32DeclP, optionU32DeclP]
      ([.storageLive 2, .storageLive 3] ++
       (match uninitSlot with
        | true =>
          [.assign (local_ 2) (.ref .shared (local_ 3)),
           .retag .fnEntry (local_ 2),
           .setDiscriminant (local_ 3) 1,
           .assign (local_ 0) (.discriminant (local_ 3))]
        | false =>
          [.assign (local_ 2) (.ref .shared (local_ 1)),
           .retag .fnEntry (local_ 2),
           .setDiscriminant (local_ 1) 1,
           .assign (local_ 0) (.discriminant (local_ 1))]) ++
       [.storageDead 3, .storageDead 2]) with
    fnAbi := fnAbi 1 }

/-- **`SetDiscriminant` borrow-invalidation & protector-conflict canary**
(`DIV-LM-ENUM-SET-DISCR-UNINIT`):
1. `SetDiscriminant` invalidates an unprotected `.frozen` borrow `&Option<u32>`, so a
   subsequent deref read `discriminant(*_2)` faults with `.ub` (whereas unpatched `Trusted`
   in `Statements.lean:3359-3364` omits `invalidateConflictingBorrows` on `.setDiscriminant`
   and wrongly returns `1`);
2. `SetDiscriminant` on a local with an active `FnEntry`-protected `.frozen` borrow faults
   immediately with `.ub` on both `.uninit` and `.init (.aggregate ...)` (whereas unpatched
   `Trusted` omits `hasProtectedWriteConflict` on `.setDiscriminant` and wrongly returns
   `1` on `.init`). -/
theorem div_lm_enum_set_discr_borrow_invalidation_and_protector_canary :
    runMirProto (setDiscrInvalidatesBorrowMir true) [] [.aggregate 0 []] = .ub ∧
    trustedRunScalar? (setDiscrInvalidatesBorrowMir true) [] [.aggregate 0 []] 20 = .some (1, 8) ∧
    runMirProto (setDiscrProtectedConflictMir true) [] [.aggregate 0 []] = .ub ∧
    runMirProto (setDiscrProtectedConflictMir false) [] [.aggregate 0 []] = .ub ∧
    trustedRunScalar? (setDiscrProtectedConflictMir false) [] [.aggregate 0 []] 20 = .some (1, 8) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), by decide +kernel,
   ProtoOutcome.eq_ub_of_isUB (by decide +kernel), ProtoOutcome.eq_ub_of_isUB (by decide +kernel),
   by decide +kernel⟩

/-- **Overlay coverage canaries** (A1 corpus differential): the MIR constructs added so that
the overlay executes the MiniRust witness corpus like `Trusted` — `UnOp.{Not, Neg}`,
`CopyForDeref`, `Deinit`, `PlaceMention`, `Assume`, `IntToInt` casts, and the layout-aware
`Discriminant` — agree with the unpatched `Trusted` stepper on real corpus bodies, both on
values and on UB. (`scripts/test_tcb_correspondence_div8_proto.py` replays the full
235-body corpus differential.) -/
theorem overlay_coverage_canaries :
    runMirProto MiniRustSpec.Correspondence.Witness.negMention [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨4294967291, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.negMention [] [.scalar ⟨5, 4⟩] 256 = .some (4294967291, 4) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.signedEdge [] [.scalar ⟨5, 1⟩] = .ok (.scalar ⟨251, 1⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.signedEdge [] [.scalar ⟨5, 1⟩] 256 = .some (251, 1) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.tempMove [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨12, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.tempMove [] [.scalar ⟨5, 4⟩] 256 = .some (12, 4) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.assumeSub [] [.scalar ⟨5, 4⟩, .scalar ⟨1, 1⟩] = .ok (.scalar ⟨4, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.assumeSub [] [.scalar ⟨5, 4⟩, .scalar ⟨1, 1⟩] 256 = .some (4, 4) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.ordBoolCastTempMove [] [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨1, 1⟩] = .ok (.scalar ⟨0, 1⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.ordBoolCastTempMove [] [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨1, 1⟩] 256 = .some (0, 1) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.cmpDiscrSwitch [] [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨1, 1⟩] = .ok (.scalar ⟨0, 1⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.cmpDiscrSwitch [] [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨1, 1⟩] 256 = .some (0, 1) ∧
    runMirProto MiniRustSpec.Correspondence.RefWitness.refMutReborrowWrite [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨15, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.RefWitness.refMutReborrowWrite [] [.scalar ⟨5, 4⟩] 256 = .some (15, 4) ∧
    runMirProto MiniRustSpec.Correspondence.RefWitness.refLoopCountdown [] [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨15, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.RefWitness.refLoopCountdown [] [.scalar ⟨5, 4⟩] 256 = .some (15, 4) ∧
    runMirProto MiniRustSpec.Correspondence.TbWitness.swapRefs [] [.scalar ⟨5, 4⟩, .scalar ⟨5, 4⟩] = .ok (.scalar ⟨505, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.TbWitness.swapRefs [] [.scalar ⟨5, 4⟩, .scalar ⟨5, 4⟩] 256 = .some (505, 4) ∧
    runMirProto MiniRustSpec.Correspondence.TbWitness.loopDerefCopyCountdown [] [.scalar ⟨5, 4⟩, .scalar ⟨5, 4⟩] = .ok (.scalar ⟨20, 4⟩) ∧
    trustedRunScalar? MiniRustSpec.Correspondence.TbWitness.loopDerefCopyCountdown [] [.scalar ⟨5, 4⟩, .scalar ⟨5, 4⟩] 256 = .some (20, 4) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.castBitNot [] [.scalar ⟨5, 1⟩] = .ub ∧
    trustedFaults MiniRustSpec.Correspondence.Witness.castBitNot [] [.scalar ⟨5, 1⟩] 256 = true ∧
    runMirProto MiniRustSpec.Correspondence.Witness.deadDeinit [] [] = .ub ∧
    trustedFaults MiniRustSpec.Correspondence.Witness.deadDeinit [] [] 256 = true ∧
    runMirProto MiniRustSpec.Correspondence.Witness.deadPlaceMention [] [] = .ub ∧
    trustedFaults MiniRustSpec.Correspondence.Witness.deadPlaceMention [] [] 256 = true ∧
    runMirProto MiniRustSpec.Correspondence.Witness.uninitBoolNot [] [] = .ub ∧
    trustedFaults MiniRustSpec.Correspondence.Witness.uninitBoolNot [] [] 256 = true ∧
    runMirProto MiniRustSpec.Correspondence.Witness.assumeDeadLocal [] [.scalar ⟨5, 4⟩] = .ub ∧
    trustedFaults MiniRustSpec.Correspondence.Witness.assumeDeadLocal [] [.scalar ⟨5, 4⟩] 256 = true := by
  repeat' apply And.intro
  all_goals first
    | exact ProtoOutcome.eq_of_okScalar? (by decide +kernel)
    | exact ProtoOutcome.eq_ub_of_isUB (by decide +kernel)
    | decide +kernel

/-! ### Additional B2 adversarial hardening: `WitLM3_1` D6 4-body suite + storage-revival offset,
cross-frame local-slot isolation, read/stmt borrow isolation, `Return` destination write
invalidation & protector check, and downstream TCB compatibility lemmas -/

/-- `u64` local declaration. -/
def u64DeclP : LocalDecl :=
  { mutability := .mut, ty := { kind := .uint .u64, layoutIdx := 0 }, debugName := none }

/-- `*mut u64` local declaration. -/
def rawPtrMutU64DeclP : LocalDecl :=
  { mutability := .mut, ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }, debugName := none }

/-- `u64` constant operand. -/
def constU64P (n : Nat) : Operand :=
  .constant { ty := { kind := .uint .u64, layoutIdx := 0 }, val := .scalar (.int ⟨n, 8⟩) }

/-- `usize` constant operand. -/
def constUsizeP (n : Nat) : Operand :=
  .constant { ty := { kind := .uint .usize, layoutIdx := 0 }, val := .scalar (.int ⟨n, 8⟩) }

/-- `isize` constant operand. -/
def constIsizeP (n : Nat) : Operand :=
  .constant { ty := { kind := .int .isize, layoutIdx := 0 }, val := .scalar (.int ⟨n, 8⟩) }

/-- `WitLM3_1.lm31OffsetDisabledLiveBody`: disable a live raw-pointer tag with a direct
write `_1 = 7_u64` and offset it by `+1_usize` (stride `8`, reaching `offsetBytes = 8`). -/
def lm31OffsetDisabledLiveMir : CapturedMir :=
  { ptrBody "witness::lm31_offset_disabled_live_stride"
      [u64DeclP, u64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.rawPtr .mut (local_ 1)),
       .assign (local_ 1) (.use (constU64P 7)),
       .assign (local_ 3) (.binaryOp .offset (.move (local_ 2)) (constUsizeP 1)),
       .assign (local_ 0) (.use (constU64P 1)),
       .storageDead 3, .storageDead 2] with
    fnAbi := fnAbi 1 }

/-- `WitLM3_1.lm31OffsetDisabledNegBody`: offset `_2` to `offsetBytes = 8`, disable its
tag via `_1 = 7_u64` while `_1` stays live, and step backward by `-1_isize` to
`offsetBytes = 0`. -/
def lm31OffsetDisabledNegMir : CapturedMir :=
  { ptrBody "witness::lm31_offset_disabled_live_neg_isize"
      [u64DeclP, u64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP]
      [.storageLive 2, .storageLive 3, .storageLive 4,
       .assign (local_ 2) (.rawPtr .mut (local_ 1)),
       .assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (constUsizeP 1)),
       .assign (local_ 1) (.use (constU64P 7)),
       .assign (local_ 4) (.binaryOp .offset (.move (local_ 3)) (constIsizeP 18446744073709551615)),
       .assign (local_ 0) (.use (constU64P 1)),
       .storageDead 4, .storageDead 3, .storageDead 2] with
    fnAbi := fnAbi 1 }

/-- `WitLM3_1.lm31OffsetDisabledUsizeMaxBody`: disable `_2`'s tag via `_1 = 7_u64` and
offset by `usize::MAX` from `offsetBytes = 0` (UB in both Miri and Anneal). -/
def lm31OffsetDisabledUsizeMaxMir : CapturedMir :=
  { ptrBody "witness::lm31_offset_disabled_usize_max"
      [u64DeclP, u64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.rawPtr .mut (local_ 1)),
       .assign (local_ 1) (.use (constU64P 7)),
       .assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (constUsizeP 18446744073709551615)),
       .assign (local_ 0) (.use (constU64P 1)),
       .storageDead 3, .storageDead 2] with
    fnAbi := fnAbi 1 }

/-- `WitLM3_1.lm31OffsetDisabledDeadZeroBody`: advance `_3` to `offsetBytes = 8`, deallocate
`_1` via `StorageDead(_1)`, and perform a zero-count `Offset(copy _3, 0_usize)` at
`offsetBytes = 8` on the dead local. -/
def lm31OffsetDisabledDeadZeroMir : CapturedMir :=
  { ptrBody "witness::lm31_offset_disabled_dead_zero_at_8"
      [u64DeclP, u64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP]
      [.storageLive 2, .storageLive 3, .storageLive 4,
       .assign (local_ 2) (.rawPtr .mut (local_ 1)),
       .assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (constUsizeP 1)),
       .storageDead 1,
       .assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (constUsizeP 0)),
       .assign (local_ 0) (.use (constU64P 1)),
       .storageDead 4, .storageDead 3, .storageDead 2] with
    fnAbi := fnAbi 1 }

/-- `L5_ControlAndCalls.stmtDivRevivePtrOffsetBody`: mint `_2 = &raw mut _1`, deallocate
`_1` (`StorageDead(_1)`), revive `_1` (`StorageLive(_1)`), and offset `_2` by `offCount`. -/
def stmtDivRevivePtrOffsetMir (offCount : Nat) : CapturedMir :=
  { ptrBody "witness::stmt_div_revive_ptr_offset"
      [u64DeclP, u64DeclP, rawPtrMutU64DeclP, rawPtrMutU64DeclP]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 1) (.use (constU64P 10)),
       .assign (local_ 2) (.rawPtr .mut (local_ 1)),
       .storageDead 1,
       .storageLive 1,
       .assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (constIsizeP offCount)),
       .assign (local_ 0) (.use (constU64P 0)),
       .storageDead 3, .storageDead 2, .storageDead 1] with
    fnAbi := fnAbi 1 }

/-- **`WitLM3_1` D6 4-witness suite & `StorageDead`+`StorageLive` revival offset canary**
(`DIV-LM-D6-OFFSET-DISABLED-TAG` + `D2` storage revival):
1. `lm31OffsetDisabledLiveMir` (`+1_usize` stride `8` on live `_1` after `_1 = 7` disabled
   tag) succeeds in `runMirProto` (`.ok 1`) while unpatched `Trusted` faults with `.ub`;
2. `lm31OffsetDisabledNegMir` (`-1_isize` stride `8` from `offsetBytes = 8` on live `_1`
   after `_1 = 7` disabled tag) succeeds in `runMirProto` (`.ok 1`) while `Trusted` faults;
3. `lm31OffsetDisabledUsizeMaxMir` (`usize::MAX` from `offsetBytes = 0`) faults with `.ub`
   in both `runMirProto` and `Trusted` (matching Miri `"PointerArithOverflow"`);
4. `lm31OffsetDisabledDeadZeroMir` (`0_usize` count at `offsetBytes = 8` after
   `StorageDead(_1)`) succeeds in `runMirProto` (`.ok 1`, matching Miri) while `Trusted`
   faults with `.ub`;
5. `stmtDivRevivePtrOffsetMir 1` (non-zero `+1_isize` offset on stale tag `_2` after
   `StorageDead(_1); StorageLive(_1)` revival) faults with `.ub` in both `runMirProto` and
   `Trusted` (`L5_ControlAndCalls.stmt_div_storage_revive_ptr_offset_is_ub`), whereas a
   zero offset `stmtDivRevivePtrOffsetMir 0` succeeds in `runMirProto` (`.ok 0`). -/
theorem div_lm_d6_wit_lm3_1_four_witnesses_and_revive_canary :
    runMirProto lm31OffsetDisabledLiveMir [] [.scalar ⟨42, 8⟩] = .ok (.scalar ⟨1, 8⟩) ∧
    trustedFaults lm31OffsetDisabledLiveMir [] [.scalar ⟨42, 8⟩] 20 = true ∧
    runMirProto lm31OffsetDisabledNegMir [] [.scalar ⟨42, 8⟩] = .ok (.scalar ⟨1, 8⟩) ∧
    trustedFaults lm31OffsetDisabledNegMir [] [.scalar ⟨42, 8⟩] 20 = true ∧
    runMirProto lm31OffsetDisabledUsizeMaxMir [] [.scalar ⟨42, 8⟩] = .ub ∧
    trustedFaults lm31OffsetDisabledUsizeMaxMir [] [.scalar ⟨42, 8⟩] 20 = true ∧
    runMirProto lm31OffsetDisabledDeadZeroMir [] [.scalar ⟨42, 8⟩] = .ok (.scalar ⟨1, 8⟩) ∧
    trustedFaults lm31OffsetDisabledDeadZeroMir [] [.scalar ⟨42, 8⟩] 20 = true ∧
    runMirProto (stmtDivRevivePtrOffsetMir 1) [] [.scalar ⟨10, 8⟩] = .ub ∧
    trustedFaults (stmtDivRevivePtrOffsetMir 1) [] [.scalar ⟨10, 8⟩] 20 = true ∧
    runMirProto (stmtDivRevivePtrOffsetMir 0) [] [.scalar ⟨10, 8⟩] = .ok (.scalar ⟨0, 8⟩) ∧
    trustedFaults (stmtDivRevivePtrOffsetMir 0) [] [.scalar ⟨10, 8⟩] 20 = true := by
  repeat' apply And.intro
  all_goals first
    | exact ProtoOutcome.eq_of_okScalar? (by decide +kernel)
    | exact ProtoOutcome.eq_ub_of_isUB (by decide +kernel)
    | decide +kernel

/-- `writeFrameLocalProto` at `(d, loc)` preserves `currentFrameDepth`, preserves
`callStack` when writing to the active frame (`d = currentFrameDepth s`), and preserves
the active frame's `s.frame.locals` when writing to a caller frame (`d < currentFrameDepth s`). -/
theorem writeFrameLocalProto_local_isolation {s s₁ : ProtoMachineState} {d loc : Nat}
    {slot : LocalSlot} (h : writeFrameLocalProto s d loc slot = .some s₁) :
    currentFrameDepth s₁ = currentFrameDepth s ∧
    (d = currentFrameDepth s → s₁.memory.callStack = s.memory.callStack) ∧
    (d < currentFrameDepth s → s₁.frame.locals = s.frame.locals) := by
  unfold writeFrameLocalProto writeCallerLocalProto at h
  dsimp only at h
  split at h
  · rename_i hd
    split at h
    · cases h; exact ⟨rfl, fun _ => rfl, fun hlt => absurd hd (Nat.ne_of_lt hlt)⟩
    · split at h
      · split at h <;> cases h
        exact ⟨rfl, fun _ => rfl, fun hlt => absurd hd (Nat.ne_of_lt hlt)⟩
      · cases h
  · rename_i hnd
    split at h
    · rename_i hlt
      split at h
      · split at h
        · split at h
          · rename_i stack' hset2
            cases h
            have hlen : stack'.length = s.memory.callStack.length := by
              unfold set? at hset2
              split at hset2
              · cases hset2; exact List.length_set
              · cases hset2
            exact ⟨hlen, fun heq => absurd heq hnd, fun _ => rfl⟩
          · cases h
        · split at h
          · split at h <;> cases h
            exact ⟨rfl, fun heq => absurd heq hnd, fun _ => rfl⟩
          · cases h
      · cases h
    · cases h

theorem commitFrameWriteProto_local_isolation {s s' : ProtoMachineState} {d loc : Nat}
    {r : Value} {b : List ProtoBorrowEntry}
    (h : commitFrameWriteProto s d loc r b = .ok s') :
    currentFrameDepth s' = currentFrameDepth s ∧
    (d = currentFrameDepth s → s'.memory.callStack = s.memory.callStack) ∧
    (d < currentFrameDepth s → s'.frame.locals = s.frame.locals) := by
  unfold commitFrameWriteProto at h
  cases hw : writeFrameLocalProto s d loc (.init r) with
  | none => rw [hw] at h; cases h
  | some s₁ =>
    rw [hw] at h; cases h
    have hi := writeFrameLocalProto_local_isolation hw
    exact ⟨hi.1, hi.2.1, hi.2.2⟩

/-- **End-to-end local-slot frame isolation of `writePlaceProto`**
(`DIV-MR-CALL-TARGET-LOCAL` + `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`):
1. Every successful direct write (`projectionHasDeref proj = false`) leaves the entire
   `callStack` untouched (`s'.memory.callStack = s.memory.callStack`);
2. Every successful deref write (`⟨loc, .deref :: rest⟩`) whose pointer resolves to `entry`
   preserves `currentFrameDepth`, leaves `s'.memory.callStack = s.memory.callStack` when
   `entry.targetFrameDepth = currentFrameDepth s`, and leaves the active callee frame's
   locals completely untouched (`s'.frame.locals = s.frame.locals`) when mutating a caller
   frame (`entry.targetFrameDepth < currentFrameDepth s`). -/
theorem writePlaceProto_frame_local_isolation (cfg : ProtoConfig) (s s' : ProtoMachineState)
    (loc : Nat) (v : Value) :
    (∀ proj, projectionHasDeref proj = false →
      writePlaceProto cfg s ⟨loc, proj⟩ v = .ok s' →
      currentFrameDepth s' = currentFrameDepth s ∧
      s'.memory.callStack = s.memory.callStack) ∧
    (∀ rest ptrVal sz entry,
      get? s.frame.locals loc = .some (.init (.ptr ptrVal sz)) →
      lookupProtoBorrow s.memory.borrows ptrVal.tag = .some entry →
      writePlaceProto cfg s ⟨loc, .deref :: rest⟩ v = .ok s' →
      currentFrameDepth s' = currentFrameDepth s ∧
      (entry.targetFrameDepth = currentFrameDepth s →
        s'.memory.callStack = s.memory.callStack) ∧
      (entry.targetFrameDepth < currentFrameDepth s →
        s'.frame.locals = s.frame.locals)) := by
  constructor
  · intro proj hnd h
    have hc : ∃ r b, commitFrameWriteProto s (currentFrameDepth s) loc r b = .ok s' := by
      unfold writePlaceProto at h
      split at h
      · rename_i rest heq; simp only at heq; subst heq; simp [projectionHasDeref] at hnd
      · simp only [hnd] at h
        repeat' split at h
        all_goals first | exact ⟨_, _, h⟩ | cases h
    obtain ⟨r, b, hc⟩ := hc
    have hi := commitFrameWriteProto_local_isolation hc
    exact ⟨hi.1, hi.2.1 rfl⟩
  · intro rest ptrVal sz entry hloc hlook h
    have hc : ∃ r b, commitFrameWriteProto s entry.targetFrameDepth entry.targetLocal r b = .ok s' := by
      unfold writePlaceProto at h
      simp only [hloc, hlook] at h
      repeat' split at h
      all_goals first | exact ⟨_, _, h⟩ | cases h
    obtain ⟨r, b, hc⟩ := hc
    exact commitFrameWriteProto_local_isolation hc

/-- **Borrow-table frame isolation of `readPlaceProto`, `StorageLive`/`StorageDead`, and
`SetDiscriminant`** (`DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`):
1. Every successful deref read `readPlaceProto cfg s ⟨loc, .deref :: rest⟩ = .ok v s'`
   through `entry` leaves every borrow entry of every frame `≠ entry.targetFrameDepth`
   unchanged;
2. Every successful `evalStorageProto` (`StorageLive` / `StorageDead`) and
   `evalSetDiscriminantProto` in the active frame leaves every borrow entry of every caller
   frame (`targetFrameDepth ≠ currentFrameDepth s`) unchanged. -/
theorem readPlaceProto_and_stmt_borrow_frame_isolation (cfg : ProtoConfig)
    (s s' : ProtoMachineState) (i : Nat) (hi : i < s.memory.borrows.length) :
    (∀ loc rest v ptrVal sz entry,
      get? s.frame.locals loc = .some (.init (.ptr ptrVal sz)) →
      lookupProtoBorrow s.memory.borrows ptrVal.tag = .some entry →
      readPlaceProto cfg s ⟨loc, .deref :: rest⟩ = .ok v s' →
      s.memory.borrows[i].targetFrameDepth ≠ entry.targetFrameDepth →
      s'.memory.borrows[i]? = .some s.memory.borrows[i]) ∧
    (∀ loc newSlot,
      evalStorageProto cfg s loc newSlot = .step s' →
      s.memory.borrows[i].targetFrameDepth ≠ currentFrameDepth s →
      s'.memory.borrows[i]? = .some s.memory.borrows[i]) ∧
    (∀ loc variantIdx,
      evalSetDiscriminantProto cfg s loc variantIdx = .step s' →
      s.memory.borrows[i].targetFrameDepth ≠ currentFrameDepth s →
      s'.memory.borrows[i]? = .some s.memory.borrows[i]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro loc rest v ptrVal sz entry hloc hlook h hd
    have hb : s'.memory.borrows = accessUpdateProto cfg s.memory.borrows s.memory.activeProtectors
        .read entry.targetFrameDepth entry.targetLocal
        (appendProjections entry.targetProjection rest) (.some ptrVal.tag) := by
      unfold readPlaceProto at h
      simp only [hloc, hlook] at h
      repeat' split at h
      all_goals first | (cases h; rfl) | cases h
    rw [hb, accessUpdateProto, List.getElem?_map, List.getElem?_eq_getElem hi]
    dsimp only [Option.map]
    rw [entryAccessTransitionProto_other_frame _ _ _ _ _ _ _ _ _ hd]
    rfl
  · intro loc newSlot h hd
    have hb : s'.memory.borrows = disableLocalBorrowsProto s.memory.borrows (currentFrameDepth s) loc := by
      unfold evalStorageProto at h
      dsimp only at h
      repeat' split at h
      all_goals first | (cases h; rfl) | cases h
    rw [hb, disableLocalBorrowsProto, List.getElem?_map, List.getElem?_eq_getElem hi]
    dsimp only [Option.map]
    have hne : Nat.beq s.memory.borrows[i].targetFrameDepth (currentFrameDepth s) = false := by
      rw [nat_beq_eq_decide]; simp only [hd, decide_eq_false_iff_not, not_false_eq_true]
    simp only [entryTargetsProto, hne, Bool.false_and]
  · intro loc variantIdx h hd
    have hb : s'.memory.borrows = invalidateConflictingBorrowsProto cfg s.memory.borrows
        s.memory.activeProtectors (currentFrameDepth s) loc .none := by
      unfold evalSetDiscriminantProto at h
      dsimp only at h
      repeat' split at h
      all_goals first | (cases h; rfl) | cases h
    rw [hb]
    exact div_mr_caller_borrow_frame_isolation cfg _ _ _ _ _ _ i hi hd

/-- **Kernel-checked 3-way agreement on `ProvenanceWitness.callerRefMutProtectedMir`**
(`DIV-MR-CALL-TARGET-LOCAL` companion in `ProvenanceWitness.lean:1528`): passing
`_2 = &mut _1` to `calleeAdd37RefMutMir` (which performs `Retag([fn entry], _1)` and
`*_1 = *_1 + 37`) and returning `_3 + _1` yields `.ok (.scalar ⟨84, 4⟩)` in `runMirProto`,
matching `Mach` and `MachTB` (`callRefMutProtectedRoundTrip_mach_and_tb`), whereas
unpatched `Trusted` faults with `.ub` (`callRefMutProtected_anneal_ret`). -/
theorem div_mr_call_ref_mut_protected_roundtrip_agrees :
    runMirProto MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutProtectedMir
      [MiniRustSpec.Correspondence.ProvenanceWitness.calleeAdd37RefMutMir]
      [.scalar ⟨5, 4⟩] = .ok (.scalar ⟨84, 4⟩) ∧
    trustedFaults MiniRustSpec.Correspondence.ProvenanceWitness.callerRefMutProtectedMir
      [MiniRustSpec.Correspondence.ProvenanceWitness.calleeAdd37RefMutMir]
      [.scalar ⟨5, 4⟩] 25 = true :=
  ⟨ProtoOutcome.eq_of_okScalar? (by decide +kernel), by decide +kernel⟩

/-- Simple callee `fn ret_const42() -> u32 { 42 }` used to test `Return` destination
write borrow invalidation and caller protector enforcement. -/
def calleeRetConst42Mir : CapturedMir where
  defPath := "witness::callee_ret_const42"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 0) (.use (constU32 42)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 0
  layouts := emptyLayoutTable
  allocations := []

/-- Caller taking `_2 = &_1` (optionally `FnEntry`-protected), calling
`callee_ret_const42() -> _1` (`caller.destination = _1`), and then reading `*_2` (or `_1`). -/
def callerRetDestConflictMir (protectBorrow : Bool) : CapturedMir where
  defPath := "witness::caller_ret_dest_conflict"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [u32Decl, u32Decl, refSharedU32Decl]
  basicBlocks := [
    { statements :=
        [mkStmt (.storageLive 2),
         mkStmt (.assign (local_ 2) (.ref .shared (local_ 1)))] ++
        (match protectBorrow with
         | true => [mkStmt (.retag .fnEntry (local_ 2))]
         | false => []),
      terminator := mkTerm (.call (fnDefOp "witness::callee_ret_const42")
        [] (local_ 1) (some 1) .continue_),
      isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0)
          (.use (.copy (match protectBorrow with | true => local_ 1 | false => derefPlace 2)))),
        mkStmt (.storageDead 2)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbi 1
  layouts := emptyLayoutTable
  allocations := []

/-- **`Return` destination write borrow-invalidation & caller-protector canary**:
when a callee returns and writes `_0` into `caller.destination = _1` (`evalReturnProto` vs
unpatched `Terminators.lean:3015` `writePlaceValue`):
1. An unprotected `.frozen` borrow `_2 = &_1` in the caller is disabled by the return
   write into `_1`, so a subsequent read `*_2` faults with `.ub` in `runMirProto` (whereas
   unpatched `Trusted.evalTerminator` calls `writePlaceValue` without
   `invalidateConflictingBorrows` and wrongly returns `42`);
2. A caller `FnEntry`-protected `.frozen` borrow `_2 = &_1` makes writing the return value
   into `_1` fault immediately with `.ub` at `Return` in `runMirProto` (whereas unpatched
   `Trusted.evalTerminator` omits `hasProtectedWriteConflict` on `caller.destination` and
   wrongly returns `42`). -/
theorem div_mr_return_destination_invalidation_and_protector_canary :
    runMirProto (callerRetDestConflictMir false) [calleeRetConst42Mir] [.scalar ⟨5, 4⟩] = .ub ∧
    trustedRunScalar? (callerRetDestConflictMir false) [calleeRetConst42Mir] [.scalar ⟨5, 4⟩] 20 =
      .some (42, 4) ∧
    runMirProto (callerRetDestConflictMir true) [calleeRetConst42Mir] [.scalar ⟨5, 4⟩] = .ub ∧
    trustedRunScalar? (callerRetDestConflictMir true) [calleeRetConst42Mir] [.scalar ⟨5, 4⟩] 20 =
      .some (42, 4) :=
  ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), by decide +kernel,
   ProtoOutcome.eq_ub_of_isUB (by decide +kernel), by decide +kernel⟩

/-- Protected foreign-write UB coincides with `preventsDeallocation` across all 6
`TreeBorrowPerm` states (`Places.lean:963` `borrowEntryWriteConflicts entry .none`). -/
theorem treeBorrowProtectedForeignWriteUB_eq_preventsDeallocation (p : TreeBorrowPerm) :
    treeBorrowTransitionIsUB (treeBorrowNodeAccess .write .foreignAccess p true) =
      preventsDeallocation p := by
  cases p <;> rfl

/-- **Downstream TCB compatibility (`Statements.lean:1945`
`hasProtectedLocalBorrow_of_hasProtectedWriteConflict`)**: even after exempting `.cell` and
`.disabled` via `preventsDeallocation`, any direct write protector conflict on `(d, loc)`
(`hasProtectedWriteConflictProto {} borrows prots d loc .none proj = true`) implies
`hasProtectedLocalBorrowProto {} borrows prots d loc = true`. -/
theorem hasProtectedLocalBorrowProto_of_hasProtectedWriteConflictProto
    (borrows : List ProtoBorrowEntry) (prots : List Nat) (d loc : Nat)
    (proj : List ProjectionElem)
    (h : hasProtectedWriteConflictProto {} borrows prots d loc .none proj = true) :
    hasProtectedLocalBorrowProto {} borrows prots d loc = true := by
  unfold hasProtectedWriteConflictProto at h
  unfold hasProtectedLocalBorrowProto
  rw [List.any_eq_true] at h ⊢
  obtain ⟨e, he, hcond⟩ := h
  refine ⟨e, he, ?_⟩
  unfold entryAccessTransitionProto at hcond
  cases hT : entryTargetsProto e d loc with
  | false => simp [hT] at hcond
  | true =>
    cases hO : projectionsOverlap e.targetProjection proj with
    | false => simp [hT, hO, treeBorrowTransitionIsUB] at hcond
    | true =>
      cases hP : isProtectedProto prots e with
      | false => simp [hP] at hcond
      | true =>
        simp only [hT, hO, Bool.and_self, hP, Bool.true_and,
          treeBorrowProtectedForeignWriteUB_eq_preventsDeallocation] at hcond
        simp [deallocBlockedBy, hcond]

/-- **Downstream TCB compatibility (`L5_ControlAndCalls.lean:278`
`hasProtectedLocalBorrow_disableLocalBorrows`)**:
1. Disabling `(d₁, loc₁)` clears all deallocation-blocking borrows on `(d₁, loc₁)` itself
   (`hasProtectedLocalBorrowProto = false`, because `preventsDeallocation .disabled = false`);
2. For any other frame/local `(d₂, loc₂) ≠ (d₁, loc₁)` — or for all `(d₂, loc₂)` when
   `hasProtectedLocalBorrowProto {} borrows prots d₁ loc₁ = false` (the precondition of
   `StorageDead(loc₁)` in `evalStmt_storageDead_then_storageLive_revive`) —
   `disableLocalBorrowsProto` preserves `hasProtectedLocalBorrowProto`. -/
theorem hasProtectedLocalBorrowProto_disableLocalBorrowsProto
    (borrows : List ProtoBorrowEntry) (prots : List Nat) (d₁ loc₁ d₂ loc₂ : Nat) :
    hasProtectedLocalBorrowProto {} (disableLocalBorrowsProto borrows d₁ loc₁) prots d₁ loc₁ = false ∧
    (((d₁ ≠ d₂ ∨ loc₁ ≠ loc₂) ∨ hasProtectedLocalBorrowProto {} borrows prots d₁ loc₁ = false) →
      hasProtectedLocalBorrowProto {} (disableLocalBorrowsProto borrows d₁ loc₁) prots d₂ loc₂ =
        hasProtectedLocalBorrowProto {} borrows prots d₂ loc₂) := by
  have hself : hasProtectedLocalBorrowProto {} (disableLocalBorrowsProto borrows d₁ loc₁) prots d₁ loc₁ = false := by
    unfold hasProtectedLocalBorrowProto disableLocalBorrowsProto
    rw [List.any_map]
    apply List.any_eq_false.mpr
    intro e _
    have hT' : entryTargetsProto { e with perm := .disabled, allocDead := true } d₁ loc₁ =
        entryTargetsProto e d₁ loc₁ := rfl
    cases hT : entryTargetsProto e d₁ loc₁ <;>
      simp [Function.comp, hT, hT', deallocBlockedBy, preventsDeallocation]
  have hother : d₁ ≠ d₂ ∨ loc₁ ≠ loc₂ →
      hasProtectedLocalBorrowProto {} (disableLocalBorrowsProto borrows d₁ loc₁) prots d₂ loc₂ =
        hasProtectedLocalBorrowProto {} borrows prots d₂ loc₂ := by
    intro hne
    unfold hasProtectedLocalBorrowProto disableLocalBorrowsProto
    rw [List.any_map]
    congr 1; funext e
    simp only [Function.comp]
    cases hT1 : entryTargetsProto e d₁ loc₁ with
    | false => rfl
    | true =>
      have hT2 : entryTargetsProto e d₂ loc₂ = false := by
        unfold entryTargetsProto at hT1 ⊢
        rw [Bool.and_eq_true, nat_beq_eq_decide, nat_beq_eq_decide,
          decide_eq_true_eq, decide_eq_true_eq] at hT1
        rcases hT1 with ⟨rfl, rfl⟩
        rcases hne with hd | hl
        · have : Nat.beq e.targetFrameDepth d₂ = false := by rw [nat_beq_eq_decide]; simp [hd]
          simp [this]
        · have : Nat.beq e.targetLocal loc₂ = false := by rw [nat_beq_eq_decide]; simp [hl]
          simp [this]
      have hT2' : entryTargetsProto { e with perm := .disabled, allocDead := true } d₂ loc₂ = false := hT2
      simp [hT2, hT2']
  refine ⟨hself, fun hcond => ?_⟩
  rcases hcond with hne | hfalse
  · exact hother hne
  · by_cases hd : d₁ = d₂
    · by_cases hl : loc₁ = loc₂
      · subst hd hl; rw [hself, hfalse]
      · exact hother (Or.inr hl)
    · exact hother (Or.inl hd)


/-! ### Kernel-checked corpus agreement with the unpatched `Trusted` stepper -/

/-- Default scalar argument of a corpus body parameter (`5`, `true`, `'A'`). -/
def corpusArgOfTy : RigidTy → Option Value
  | .bool => .some (.scalar ⟨1, 1⟩)
  | .char => .some (.scalar ⟨0x41, 4⟩)
  | .uint .u8 => .some (.scalar ⟨5, 1⟩)
  | .int .i8 => .some (.scalar ⟨5, 1⟩)
  | .uint .u16 => .some (.scalar ⟨5, 2⟩)
  | .int .i16 => .some (.scalar ⟨5, 2⟩)
  | .uint .u32 => .some (.scalar ⟨5, 4⟩)
  | .int .i32 => .some (.scalar ⟨5, 4⟩)
  | .uint .u64 => .some (.scalar ⟨5, 8⟩)
  | .int .i64 => .some (.scalar ⟨5, 8⟩)
  | .uint .usize => .some (.scalar ⟨5, 8⟩)
  | .int .isize => .some (.scalar ⟨5, 8⟩)
  | .uint .u128 => .some (.scalar ⟨5, 16⟩)
  | .int .i128 => .some (.scalar ⟨5, 16⟩)
  | _ => .none

/-- Default scalar arguments of a corpus body (`none` for non-scalar parameters). -/
def corpusArgs (body : CapturedMir) : Option (List Value) :=
  ((body.localDecls.drop 1).take body.argCount).mapM (fun d => corpusArgOfTy d.ty.kind)

mutual
/-- Pointer-abstracting serialization of a `Value` (provenance tags are
implementation-specific, so pointers keep only their width). -/
def corpusEncodeVal : Value → List Nat
  | .unit => [0]
  | .scalar sc => [1, sc.bits, sc.sizeBytes]
  | .ptr _ sz => [2, sz]
  | .aggregate i vs => 3 :: i :: vs.length :: corpusEncodeVals vs
/-- Serialization of a field list. -/
def corpusEncodeVals : List Value → List Nat
  | [] => []
  | v :: vs => corpusEncodeVal v ++ corpusEncodeVals vs
end

/-- Outcome class of a run: a (pointer-abstracted) returned value, UB, or indefinite
(unsupported / out of fuel). -/
inductive CorpusOutcome : Type where
  | ok (enc : List Nat) : CorpusOutcome
  | ub : CorpusOutcome
  | indefinite : CorpusOutcome
  deriving DecidableEq

/-- Overlay outcome class (no callees). -/
def protoCorpusOutcome (body : CapturedMir) (args : List Value) : CorpusOutcome :=
  match runMirProto body [] args with
  | .ok v => .ok (corpusEncodeVal v)
  | .ub => .ub
  | _ => .indefinite

/-- Unpatched `Trusted` outcome class (`runA` / `faultsA`, fuel `256`, no callees). -/
def trustedCorpusOutcome (body : CapturedMir) (args : List Value) : CorpusOutcome :=
  match runA body 256 (initMachineStateWithCallees body args []) with
  | .some (_, .normal (v, _)) => .ok (corpusEncodeVal v)
  | .some _ => .indefinite
  | .none =>
    match faultsA body 256 (initMachineStateWithCallees body args []) with
    | true => .ub
    | false => .indefinite

/-- The overlay and the unpatched `Trusted` stepper agree on `body` at its default args. -/
def corpusAgrees (body : CapturedMir) : Bool :=
  match corpusArgs body with
  | .some args => decide (protoCorpusOutcome body args = trustedCorpusOutcome body args)
  | .none => false

/-- The single-function MiniRust witness bodies (default scalar arguments) on which the
overlay and the unpatched `Trusted` stepper both produce a definite outcome. -/
def corpusAgreementBodies : List CapturedMir := [
    MiniRustSpec.Correspondence.Witness.sumTo,
    MiniRustSpec.Correspondence.Witness.retUninit,
    MiniRustSpec.Correspondence.Witness.negMention,
    MiniRustSpec.Correspondence.Witness.signedEdge,
    MiniRustSpec.Correspondence.Witness.castBitNot,
    MiniRustSpec.Correspondence.Witness.divRemI8,
    MiniRustSpec.Correspondence.Witness.remOnlyI8,
    MiniRustSpec.Correspondence.Witness.uncheckedArithI8,
    MiniRustSpec.Correspondence.Witness.shiftI8,
    MiniRustSpec.Correspondence.Witness.shlUncheckedI8,
    MiniRustSpec.Correspondence.Witness.bitwiseI8,
    MiniRustSpec.Correspondence.Witness.heteroShiftSwitch,
    MiniRustSpec.Correspondence.Witness.uninitOperandUb,
    MiniRustSpec.Correspondence.Witness.cmpNotSwitch,
    MiniRustSpec.Correspondence.Witness.leNeGe,
    MiniRustSpec.Correspondence.Witness.boolCastI8,
    MiniRustSpec.Correspondence.Witness.uninitBool,
    MiniRustSpec.Correspondence.Witness.uninitBoolNot,
    MiniRustSpec.Correspondence.Witness.uninitBoolRel,
    MiniRustSpec.Correspondence.Witness.cmpSel,
    MiniRustSpec.Correspondence.Witness.uninitOrdering,
    MiniRustSpec.Correspondence.Witness.uninitBoolBitAnd,
    MiniRustSpec.Correspondence.Witness.uninitBoolBitOrRhs,
    MiniRustSpec.Correspondence.Witness.checkedTupleU32,
    MiniRustSpec.Correspondence.Witness.uninitTupleField0,
    MiniRustSpec.Correspondence.Witness.uninitTupleField1,
    MiniRustSpec.Correspondence.Witness.tempMove,
    MiniRustSpec.Correspondence.Witness.deadRead,
    MiniRustSpec.Correspondence.Witness.moveReuse,
    MiniRustSpec.Correspondence.Witness.crossBlockMove,
    MiniRustSpec.Correspondence.Witness.crossBlockMoveReuse,
    MiniRustSpec.Correspondence.Witness.unmarkedTempAssign,
    MiniRustSpec.Correspondence.Witness.loopTempMove,
    MiniRustSpec.Correspondence.Witness.loopBackEdgeReuse,
    MiniRustSpec.Correspondence.Witness.deadAssign,
    MiniRustSpec.Correspondence.Witness.deadDeinit,
    MiniRustSpec.Correspondence.Witness.deadPlaceMention,
    MiniRustSpec.Correspondence.Witness.storageDeadRet,
    MiniRustSpec.Correspondence.Witness.sameRvalueMoveReuse,
    MiniRustSpec.Correspondence.Witness.moveRetPlace,
    MiniRustSpec.Correspondence.Witness.storageLiveArgRet,
    MiniRustSpec.Correspondence.Witness.storageDeadArg,
    MiniRustSpec.Correspondence.Witness.storageDeadArgReadAfter,
    MiniRustSpec.Correspondence.Witness.diamondMoveJoin,
    MiniRustSpec.Correspondence.Witness.diamondHalfMoveReuse,
    MiniRustSpec.Correspondence.Witness.tupleAggCastMove,
    MiniRustSpec.Correspondence.Witness.projFieldMoveReuse,
    MiniRustSpec.Correspondence.Witness.ordBoolCastTempMove,
    MiniRustSpec.Correspondence.Witness.negI8Callee,
    MiniRustSpec.Correspondence.Witness.flipBoolCallee,
    MiniRustSpec.Correspondence.Witness.chainLeaf,
    MiniRustSpec.Correspondence.Witness.idU32Callee,
    MiniRustSpec.Correspondence.Witness.divTenI8Callee,
    MiniRustSpec.Correspondence.Witness.cAbiCallee,
    MiniRustSpec.Correspondence.Witness.badCallConvCallee,
    MiniRustSpec.Correspondence.Witness.badCallConvSysvBody,
    MiniRustSpec.Correspondence.Witness.idI8Callee,
    MiniRustSpec.Correspondence.Witness.const5Callee,
    MiniRustSpec.Correspondence.Witness.retUninitCallee,
    MiniRustSpec.Correspondence.Witness.assumeSub,
    MiniRustSpec.Correspondence.Witness.assumeChainCallee,
    MiniRustSpec.Correspondence.Witness.assumeDeadLocal,
    MiniRustSpec.Correspondence.Witness.assumeMoveReuse,
    MiniRustSpec.Correspondence.Witness.assumeAfterMove,
    MiniRustSpec.Correspondence.Witness.cmpDiscrSwitch,
    MiniRustSpec.Correspondence.PointerWitness.ptrRoundTrip,
    MiniRustSpec.Correspondence.PointerWitness.ptrCountdown,
    MiniRustSpec.Correspondence.PointerWitness.constBorrowLoop,
    MiniRustSpec.Correspondence.PointerWitness.uninitPtrReadUb,
    MiniRustSpec.Correspondence.PointerWitness.uninitPtrWriteUb,
    MiniRustSpec.Correspondence.PointerWitness.deadPtrReadUb,
    MiniRustSpec.Correspondence.PointerWitness.uninitPtrOffsetUb,
    MiniRustSpec.Correspondence.PointerWitness.derefWriteRhsUb,
    MiniRustSpec.Correspondence.PointerWitness.dangling,
    MiniRustSpec.Correspondence.PointerWitness.directWrite,
    MiniRustSpec.Correspondence.PointerWitness.frozenWrite,
    MiniRustSpec.Correspondence.RefWitness.refSharedRead,
    MiniRustSpec.Correspondence.RefWitness.refMutRoundTrip,
    MiniRustSpec.Correspondence.RefWitness.refMutReborrowWrite,
    MiniRustSpec.Correspondence.RefWitness.refLoopCountdown,
    MiniRustSpec.Correspondence.RefWitness.uninitRefReadUb,
    MiniRustSpec.Correspondence.RefWitness.uninitRefReborrowUb,
    MiniRustSpec.Correspondence.RefWitness.refMutDivZeroUb,
    MiniRustSpec.Correspondence.RefWitness.danglingRef,
    MiniRustSpec.Correspondence.RefWitness.refTwoPhaseBorrowRoundTrip,
    MiniRustSpec.Correspondence.RefWitness.twoPhaseForeignWriteDiscrepancy,
    MiniRustSpec.Correspondence.RefWitness.twoPhaseDirectWriteTreeBorrowsGap,
    MiniRustSpec.Correspondence.RefWitness.frozenRefMutReborrow,
    MiniRustSpec.Correspondence.RefWitness.disabledRefReborrow,
    MiniRustSpec.Correspondence.RefWitness.childReborrowWriteDisablesParent,
    MiniRustSpec.Correspondence.RefWitness.retagRefReborrowChain,
    MiniRustSpec.Correspondence.RefWitness.retagUninitRefUb,
    MiniRustSpec.Correspondence.RefWitness.retagFnEntryProtectorWrite,
    MiniRustSpec.Correspondence.RefWitness.retagDisabledRefDiscrepancy,
    MiniRustSpec.Correspondence.RefWitness.retagScalarDiscrepancy,
    MiniRustSpec.Correspondence.RefWitness.frozenRefMutReborrowWrite,
    MiniRustSpec.Correspondence.RefWitness.retagTrulyDisabledRefUb,
    MiniRustSpec.Correspondence.RefWitness.misalignedRaw,
    MiniRustSpec.Correspondence.RefWitness.rawAddrOfUninit,
    MiniRustSpec.Correspondence.RefWitness.retagRawOnRefLocal,
    MiniRustSpec.Correspondence.TbWitness.swapRefs,
    MiniRustSpec.Correspondence.TbWitness.derefCopyUninitSrcUb,
    MiniRustSpec.Correspondence.TbWitness.derefWriteMoveUninitUb,
    MiniRustSpec.Correspondence.TbWitness.boolMutRefToggle,
    MiniRustSpec.Correspondence.TbWitness.selfDerefCopyOk,
    MiniRustSpec.Correspondence.TbWitness.parentDerefCopyDisablesChild,
    MiniRustSpec.Correspondence.TbWitness.loopDerefCopyCountdown,
    MiniRustSpec.Correspondence.TbWitness.unitTupleMutRefRoundTrip,
    MiniRustSpec.Correspondence.TbWitness.storageCycleDisablesBorrowUb,
    MiniRustSpec.Correspondence.TbWitness.derefReadFreezesActiveMutUb,
    MiniRustSpec.Correspondence.TbWitness.mutReborrowForeignReadRoundTrip,
    MiniRustSpec.Correspondence.TbWitness.storageLiveReallocDisablesBorrowUb,
    MiniRustSpec.Correspondence.ProvenanceWitness.assumeReborrowFalseUb,
    MiniRustSpec.Correspondence.ProvenanceWitness.calleeScalarAssignLocal1Mir]

/-- **Kernel-checked corpus agreement**: on every one of these single-function MiniRust
witness bodies, the overlay `runMirProto` and the unpatched `Trusted` stepper (`runA` /
`faultsA`) produce the same outcome — the same returned value (pointer tags abstracted) or
UB — so the overlay's fixes do not perturb `Trusted`'s behavior outside the tracked
divergences. -/
theorem corpus_agreement_kernel : corpusAgreementBodies.all corpusAgrees = true := by
  decide +kernel

/-- **Out-of-fragment `Trusted` divergences fixed by the overlay** (found by the corpus
differential): `argCountMismatchCaller` calls the 0-argument `const5Callee` with a
mismatched argument list — the overlay faults with UB like MiniRust
(`Witness.argCountMismatch_minirust_ub`: "call ABI violation") while `Trusted` returns `5`;
`uninitProjCallDestCaller` writes a call result into a field of a live but uninitialized
tuple — the overlay returns `neg_i8(5) = 251` like MiniRust
(`Witness.uninitProjCallDest_minirust_ret`) while `Trusted` faults. -/
theorem corpus_out_of_fragment_fixes :
    runMirProto MiniRustSpec.Correspondence.Witness.argCountMismatchCaller [MiniRustSpec.Correspondence.Witness.const5Callee] [] = .ub ∧
    trustedRunScalar? MiniRustSpec.Correspondence.Witness.argCountMismatchCaller [MiniRustSpec.Correspondence.Witness.const5Callee] [] 20 = .some (5, 4) ∧
    runMirProto MiniRustSpec.Correspondence.Witness.uninitProjCallDestCaller [MiniRustSpec.Correspondence.Witness.negI8Callee] [.scalar ⟨5, 1⟩] =
      .ok (.scalar ⟨251, 1⟩) ∧
    trustedFaults MiniRustSpec.Correspondence.Witness.uninitProjCallDestCaller [MiniRustSpec.Correspondence.Witness.negI8Callee] [.scalar ⟨5, 1⟩] 20 = true := by
  refine ⟨ProtoOutcome.eq_ub_of_isUB (by decide +kernel), by decide +kernel,
    ProtoOutcome.eq_of_okScalar? (by decide +kernel), by decide +kernel⟩

end PartAWitnesses

/-! ## §5. Part B witnesses: IEEE-754 casts on raw bit patterns -/

section PartBWitnesses

/-- `evalFloatToIntSaturating` on an `f64` bit pattern, as `(bits, sizeBytes)`. -/
def f2i64 (bits : Nat) (t : IntTarget) (pw : PtrWidth := .bits64) : Nat × Nat :=
  let r := evalFloatToIntSaturating .binary64 bits t pw
  (r.bits, r.sizeBytes)

/-- `evalFloatToIntSaturating` on an `f32` bit pattern. -/
def f2i32 (bits : Nat) (t : IntTarget) (pw : PtrWidth := .bits64) : Nat × Nat :=
  let r := evalFloatToIntSaturating .binary32 bits t pw
  (r.bits, r.sizeBytes)

/-- **Saturating `FloatToInt` canaries**: NaN ↦ 0; ±∞ clamp; finite values truncate
toward zero (positive and negative fractions); exact boundary clamping for every integer
width (`i8`/`u8`/`i32`/`u32`/`i64`/`u64`/`i128`/`u128`/`isize`/`usize`). -/
theorem evalFloatToIntSaturating_canaries :
    -- NaN, ±∞, ±0
    f2i64 0x7FF8000000000000 (.signed .i32) = (0, 4) ∧
    f2i64 0xFFF8000000000001 (.unsigned .u64) = (0, 8) ∧
    f2i64 0x7FF0000000000000 (.signed .i32) = (0x7FFFFFFF, 4) ∧
    f2i64 0xFFF0000000000000 (.signed .i32) = (0x80000000, 4) ∧
    f2i64 0xFFF0000000000000 (.unsigned .u32) = (0, 4) ∧
    f2i64 0x8000000000000000 (.signed .i64) = (0, 8) ∧
    f2i32 0x7FC00000 (.unsigned .u16) = (0, 2) ∧
    -- truncation toward zero
    f2i64 0x400599999999999A (.signed .i32) = (2, 4) ∧
    f2i64 0xC00599999999999A (.signed .i32) = (0xFFFFFFFE, 4) ∧
    f2i32 0x3FC00000 (.signed .i8) = (1, 1) ∧
    -- u8 / i8 boundaries
    f2i64 0x406FFCCCCCCCCCCD (.unsigned .u8) = (255, 1) ∧
    f2i64 0x4072C00000000000 (.unsigned .u8) = (255, 1) ∧
    f2i64 0xBFF0000000000000 (.unsigned .u8) = (0, 1) ∧
    f2i64 0x405FF9999999999A (.signed .i8) = (127, 1) ∧
    f2i64 0x4060000000000000 (.signed .i8) = (127, 1) ∧
    f2i64 0xC0601CCCCCCCCCCD (.signed .i8) = (0x80, 1) ∧
    f2i64 0xC060200000000000 (.signed .i8) = (0x80, 1) ∧
    -- u16 / i16 boundaries
    f2i64 0x40DFFFC000000000 (.signed .i16) = (32767, 2) ∧
    f2i64 0x40E0000000000000 (.signed .i16) = (32767, 2) ∧
    f2i64 0xC0E0002000000000 (.signed .i16) = (0x8000, 2) ∧
    f2i64 0xC0E0004000000000 (.signed .i16) = (0x8000, 2) ∧
    f2i64 0x40EFFFE000000000 (.unsigned .u16) = (65535, 2) ∧
    f2i64 0x40F0000000000000 (.unsigned .u16) = (65535, 2) ∧
    f2i64 0xBFF0000000000000 (.unsigned .u16) = (0, 2) ∧
    -- i32 / u32 boundaries
    f2i64 0x41DFFFFFFFF9999A (.signed .i32) = (0x7FFFFFFF, 4) ∧
    f2i64 0x41E0000000000000 (.signed .i32) = (0x7FFFFFFF, 4) ∧
    f2i64 0xC1E00000001CCCCD (.signed .i32) = (0x80000000, 4) ∧
    f2i64 0xC1E0000000200000 (.signed .i32) = (0x80000000, 4) ∧
    f2i64 0x41F0000000000000 (.unsigned .u32) = (0xFFFFFFFF, 4) ∧
    -- i64 / u64 boundaries
    f2i64 0x43E0000000000000 (.signed .i64) = (0x7FFFFFFFFFFFFFFF, 8) ∧
    f2i64 0xC3E0000000000000 (.signed .i64) = (0x8000000000000000, 8) ∧
    f2i64 0x43F0000000000000 (.unsigned .u64) = (0xFFFFFFFFFFFFFFFF, 8) ∧
    -- i128 / u128 boundaries (including f32 exact 2^127 and -2^127 boundary)
    f2i64 0x483D6329F1C35CA5 (.signed .i128) = (2 ^ 127 - 1, 16) ∧
    f2i64 0xC83D6329F1C35CA5 (.signed .i128) = (2 ^ 127, 16) ∧
    f2i64 0x483D6329F1C35CA5 (.unsigned .u128) = (2 ^ 128 - 1, 16) ∧
    f2i32 0x7F000000 (.signed .i128) = (2 ^ 127 - 1, 16) ∧
    f2i32 0x7F000000 (.unsigned .u128) = (2 ^ 127, 16) ∧
    f2i32 0xFF000000 (.signed .i128) = (2 ^ 127, 16) ∧
    -- isize / usize on 64- and 32-bit targets
    f2i64 0x43E0000000000000 (.signed .isize) .bits64 = (0x7FFFFFFFFFFFFFFF, 8) ∧
    f2i64 0x43E0000000000000 (.signed .isize) .bits32 = (0x7FFFFFFF, 4) ∧
    f2i64 0xC1E0000000200000 (.signed .isize) .bits32 = (0x80000000, 4) ∧
    f2i64 0x43F0000000000000 (.unsigned .usize) .bits64 = (0xFFFFFFFFFFFFFFFF, 8) ∧
    f2i64 0x41F0000000000000 (.unsigned .usize) .bits32 = (0xFFFFFFFF, 4) ∧
    f2i64 0xBFF0000000000000 (.unsigned .usize) .bits32 = (0, 4) := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- **`b/585733184` (`cl/1021519279`) ties-to-even vs. half-away-from-zero separation
witnesses** on the integer rounding core (`0.5 ↦ 0` vs `1`, `-0.5 ↦ -0` vs `-1`,
`2.5 ↦ 2` vs `3`, `3.5 ↦ 4`) and on full int-to-float casts. -/
theorem b585733184_ties_to_even_separation :
    -- 0.5, -0.5 (sign carried separately: magnitude 0 is -0), 2.5, 3.5
    (roundQuotientTiesToEven 1 2, roundQuotientHalfAwayFromZero 1 2) = (0, 1) ∧
    ((true, roundQuotientTiesToEven 1 2), (true, roundQuotientHalfAwayFromZero 1 2)) =
      ((true, 0), (true, 1)) ∧
    (roundQuotientTiesToEven 5 2, roundQuotientHalfAwayFromZero 5 2) = (2, 3) ∧
    (roundQuotientTiesToEven 7 2, roundQuotientHalfAwayFromZero 7 2) = (4, 4) ∧
    -- 2^24 + 1 : u32 -> f32
    evalIntToFloatRoundTiesToEven false 32 16777217 .binary32 = 0x4B800000 ∧
    evalIntToFloatHalfAwayFromZero false 32 16777217 .binary32 = 0x4B800001 ∧
    -- 2^24 + 3 : u32 -> f32
    evalIntToFloatRoundTiesToEven false 32 16777219 .binary32 = 0x4B800002 ∧
    evalIntToFloatHalfAwayFromZero false 32 16777219 .binary32 = 0x4B800002 ∧
    -- -(2^24 + 1) : i32 -> f32
    evalIntToFloatRoundTiesToEven true 32 (2 ^ 32 - 16777217) .binary32 = 0xCB800000 ∧
    evalIntToFloatHalfAwayFromZero true 32 (2 ^ 32 - 16777217) .binary32 = 0xCB800001 ∧
    -- 2^53 + 1 : u64 -> f64
    evalIntToFloatRoundTiesToEven false 64 9007199254740993 .binary64 = 0x4340000000000000 ∧
    evalIntToFloatHalfAwayFromZero false 64 9007199254740993 .binary64 = 0x4340000000000001 := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- Int-to-float canaries: signed zero, `±1`, `i32::MIN`, `u32::MAX`, `i64::MAX`,
`u64::MAX`, and the exact `u128 -> f32` overflow threshold `2^128 - 2^103` (ties to the
even "significand" `2^24`, i.e. `+∞`), with `u128::MAX ↦ +∞`. -/
theorem evalIntToFloatRoundTiesToEven_canaries :
    evalIntToFloatRoundTiesToEven true 32 0 .binary32 = 0 ∧
    evalIntToFloatRoundTiesToEven true 32 1 .binary32 = 0x3F800000 ∧
    evalIntToFloatRoundTiesToEven true 32 0xFFFFFFFF .binary32 = 0xBF800000 ∧
    evalIntToFloatRoundTiesToEven true 32 0x80000000 .binary32 = 0xCF000000 ∧
    evalIntToFloatRoundTiesToEven true 32 0x7FFFFFFF .binary32 = 0x4F000000 ∧
    evalIntToFloatRoundTiesToEven false 32 0xFFFFFFFF .binary32 = 0x4F800000 ∧
    evalIntToFloatRoundTiesToEven false 32 0xFFFFFFFF .binary64 = 0x41EFFFFFFFE00000 ∧
    evalIntToFloatRoundTiesToEven true 64 0x7FFFFFFFFFFFFFFF .binary64 = 0x43E0000000000000 ∧
    evalIntToFloatRoundTiesToEven false 64 0xFFFFFFFFFFFFFFFF .binary64 = 0x43F0000000000000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 1) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103 - 1) .binary32 = 0x7F7FFFFF := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- **Signaling-NaN quietization negative canary**: `f64 -> f32` of the signaling NaN
`0x7FF0_0000_0000_0001` is the quiet NaN `0x7FC0_0000`, never `+∞` (`0x7F80_0000`). -/
theorem f64ToF32_signaling_nan_quietized :
    f64ToF32 0x7FF0000000000001#64 = 0x7FC00000#32 ∧
    f64ToF32 0x7FF0000000000001#64 ≠ 0x7F800000#32 ∧
    isQuietNaNBits .binary32 (f64ToF32 0x7FF0000000000001#64).toNat = true := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- Float-to-float canaries: NaN payload propagation (both directions), signed zeros,
subnormals (gradual underflow and ties at the subnormal boundary), overflow to `+∞` at
the exact tie `2^128 - 2^103`, and ties-to-even in the normal range. -/
theorem evalFloatToFloatRoundTiesToEven_canaries :
    -- NaN propagation
    f64ToF32 0x7FF8000000000123#64 = 0x7FC00000#32 ∧
    f64ToF32 0xFFF8000000000000#64 = 0xFFC00000#32 ∧
    f32ToF64 0x7F800001#32 = 0x7FF8000020000000#64 ∧
    f32ToF64 0x7FC00000#32 = 0x7FF8000000000000#64 ∧
    -- signed zeros
    f64ToF32 0x8000000000000000#64 = 0x80000000#32 ∧
    f32ToF64 0x80000000#32 = 0x8000000000000000#64 ∧
    -- exact widening of extremes
    f32ToF64 0x00000001#32 = 0x36A0000000000000#64 ∧
    f32ToF64 0x7F7FFFFF#32 = 0x47EFFFFFE0000000#64 ∧
    f32ToF64 0x3FC00000#32 = 0x3FF8000000000000#64 ∧
    -- underflow / gradual underflow
    f64ToF32 0x358DEE7A4AD4B81F#64 = 0x00000000#32 ∧
    f64ToF32 0xB58DEE7A4AD4B81F#64 = 0x80000000#32 ∧
    f64ToF32 0x3690000000000000#64 = 0x00000000#32 ∧
    f64ToF32 0x3690000000000001#64 = 0x00000001#32 ∧
    f64ToF32 0x36A8000000000000#64 = 0x00000002#32 ∧
    -- overflow
    f64ToF32 0x47EFFFFFF0000000#64 = 0x7F800000#32 ∧
    f64ToF32 0x47EFFFFFEFFFFFFF#64 = 0x7F7FFFFF#32 ∧
    f64ToF32 0x48078287F49C4A1D#64 = 0x7F800000#32 ∧
    f64ToF32 0x7FF0000000000000#64 = 0x7F800000#32 ∧
    -- ties to even in the normal range
    f64ToF32 0x3FF0000010000000#64 = 0x3F800000#32 ∧
    f64ToF32 0x3FF0000030000000#64 = 0x3F800002#32 ∧
    f64ToF32 0x3FD5555555555555#64 = 0x3EAAAAAB#32 := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- **Subnormal single-rounding (no double rounding) & carry-out canaries**:
1. At `e = -127` (`f32.minExponent - 1`), `0x3800_0000_5FFF_FFFF : f64`
   (`(2^22 + 1.5 - 2^-30) * 2^-149`) rounds in one step to the subnormal
   `0x0040_0001 : f32` (`(2^22 + 1) * 2^-149`), whereas first rounding the 53-bit
   significand to 24 bits (`roundQuotientTiesToEven (2^52 + 2^30 + 2^29 - 1) (2^29) = 2^23 + 3`)
   and then shifting into the subnormal slot (`roundQuotientTiesToEven (2^23 + 3) 2 = 2^22 + 2`,
   a tie broken to even) would double-round to `0x0040_0002`;
2. subnormal-to-normal carry-out: `0x380F_FFFF_DFFF_FFFF` rounds to the greatest `f32`
   subnormal `0x007F_FFFF`, while `0x380F_FFFF_E000_0000` (`2^-126 - 2^-150`, an exact tie)
   carries into the minimum normal `0x0080_0000` (`2^-126`);
3. `u64 -> f32` single rounding vs `u64 -> f64 -> f32` double rounding on
   `0x0040_0000_BFFF_FFFF = 2^54 + 3 * 2^30 - 1`: the direct cast yields `0x5A80_0001`,
   whereas routing through `f64` (`2^54 + 3 * 2^30`) double-rounds to `0x5A80_0002`. -/
theorem f64ToF32_subnormal_and_double_rounding_canaries :
    f64ToF32 0x380000005FFFFFFF#64 = 0x00400001#32 ∧
    roundQuotientTiesToEven
        (roundQuotientTiesToEven (2 ^ 52 + 2 ^ 30 + 2 ^ 29 - 1) (2 ^ 29)) 2 =
      0x00400002 ∧
    f64ToF32 0x380FFFFFDFFFFFFF#64 = 0x007FFFFF#32 ∧
    f64ToF32 0x380FFFFFE0000000#64 = 0x00800000#32 ∧
    evalIntToFloatRoundTiesToEven false 64 0x400000BFFFFFFF .binary32 = 0x5A800001 ∧
    evalFloatToFloatRoundTiesToEven .binary64 .binary32
        (evalIntToFloatRoundTiesToEven false 64 0x400000BFFFFFFF .binary64) =
      0x5A800002 := by
  repeat' apply And.intro
  all_goals decide +kernel

/-! ### `CastKind.{floatToInt, intToFloat, floatToFloat}` end-to-end through `runMirProto` -/

open MiniRustSpec.Correspondence.Witness (u32Ty u32Decl local_ fnAbi)
open MiniRustSpec.Correspondence.PointerWitness (ptrBody)

/-- `f32` / `f64` types and locals. -/
def f32TyP : Ty := { kind := .float .f32, layoutIdx := 0 }
def f64TyP : Ty := { kind := .float .f64, layoutIdx := 0 }
def f32DeclP : LocalDecl := { mutability := .mut, ty := f32TyP, debugName := none }
def f64DeclP : LocalDecl := { mutability := .mut, ty := f64TyP, debugName := none }
def i32TyP : Ty := { kind := .int .i32, layoutIdx := 0 }
def i32DeclP : LocalDecl := { mutability := .mut, ty := i32TyP, debugName := none }

/-- `_0 = copy _1 as T` with `_0 : T`, `_1 : S`. -/
def castBody (kind : CastKind) (srcDecl dstDecl : LocalDecl) : CapturedMir :=
  ptrBody "witness::cast" [dstDecl, srcDecl]
    [.assign (local_ 0) (.cast kind (.copy (local_ 1)) dstDecl.ty)]

/-- **End-to-end MIR `Rvalue.cast`**: `2.7_f64 as i32 = 2`, `-2.7_f64 as i32 = -2`,
`NaN as u32 = 0`, `16777217_u32 as f32 = 16777216.0`, `-1_i32 as f64 = -1.0`,
`sNaN_f64 as f32 = qNaN`, `1e-50_f64 as f32 = 0.0`, and `f32::MAX as f64` — each proved
by `rfl` (definitional unfolding of `runMirProto` on the real `CapturedMir`). -/
theorem castKind_end_to_end :
    runMirProto (castBody .floatToInt f64DeclP i32DeclP) [] [.scalar ⟨0x400599999999999A, 8⟩] =
      .ok (.scalar ⟨2, 4⟩) ∧
    runMirProto (castBody .floatToInt f64DeclP i32DeclP) [] [.scalar ⟨0xC00599999999999A, 8⟩] =
      .ok (.scalar ⟨0xFFFFFFFE, 4⟩) ∧
    runMirProto (castBody .floatToInt f64DeclP u32Decl) [] [.scalar ⟨0x7FF8000000000000, 8⟩] =
      .ok (.scalar ⟨0, 4⟩) ∧
    runMirProto (castBody .intToFloat u32Decl f32DeclP) [] [.scalar ⟨16777217, 4⟩] =
      .ok (.scalar ⟨0x4B800000, 4⟩) ∧
    runMirProto (castBody .intToFloat i32DeclP f64DeclP) [] [.scalar ⟨0xFFFFFFFF, 4⟩] =
      .ok (.scalar ⟨0xBFF0000000000000, 8⟩) ∧
    runMirProto (castBody .floatToFloat f64DeclP f32DeclP) [] [.scalar ⟨0x7FF0000000000001, 8⟩] =
      .ok (.scalar ⟨0x7FC00000, 4⟩) ∧
    runMirProto (castBody .floatToFloat f64DeclP f32DeclP) [] [.scalar ⟨0x358DEE7A4AD4B81F, 8⟩] =
      .ok (.scalar ⟨0, 4⟩) ∧
    runMirProto (castBody .floatToFloat f32DeclP f64DeclP) [] [.scalar ⟨0x7F7FFFFF, 4⟩] =
      .ok (.scalar ⟨0x47EFFFFFE0000000, 8⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The unpatched `Trusted.evalRvalue` has no float casts at all (`.unsupported`). -/
theorem castKind_trusted_unsupported :
    (match evalRvalue [.uninit, .init (.scalar ⟨0x400599999999999A, 8⟩)]
        (.cast .floatToInt (.copy (local_ 1)) i32TyP) {} [i32DeclP, f64DeclP] emptyLayoutTable with
      | .unsupported => true
      | _ => false) = true := by
  repeat' apply And.intro
  all_goals decide +kernel

end PartBWitnesses


/-! ## §6. Part B universal theorems -/

section PartBTheorems

theorem if_pos' {c : Prop} [Decidable c] (h : c) {α : Sort _} (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem if_neg' {c : Prop} [Decidable c] (h : ¬c) {α : Sort _} (a b : α) :
    (if c then a else b) = b := by simp [h]

/-! ### Constructive arithmetic helpers

In Lean `v4.34.1`, core's `Nat.pow_lt_pow_right`, `Nat.pow_lt_pow_iff_right`,
`Nat.mul_lt_mul_left`, `Nat.mul_lt_mul_right`, `Nat.div_lt_of_lt_mul`, and
`Nat.log2_two_pow` transitively depend on `Classical.choice`. The replacements below
depend on at most `propext`/`Quot.sound`. Likewise `omega` discharges a negated
conjunction `¬(A ∧ B)` (from a conjunction or iff goal, or such a hypothesis) through
`Classical.propDecidable`, so every `omega` call in this file is fed atomic goals. -/

theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : 2 ^ (a + 1) ≤ 2 ^ b := two_pow_le_two_pow h
  rw [Nat.pow_succ] at h1
  have := Nat.two_pow_pos a
  omega

theorem lt_of_two_pow_lt {a b : Nat} (h : 2 ^ a < 2 ^ b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl h' => exact h'
  | inr h' => have := two_pow_le_two_pow h'; omega

theorem nat_mul_lt_mul_right_iff {a b c : Nat} (hc : 0 < c) : a * c < b * c ↔ a < b :=
  ⟨fun h => by
    cases Nat.lt_or_ge a b with
    | inl h' => exact h'
    | inr h' => have := Nat.mul_le_mul_right c h'; omega,
   fun h => Nat.mul_lt_mul_of_pos_right h hc⟩

theorem nat_div_lt_of_lt_mul {m n k : Nat} (h : m < n * k) : m / n < k := by
  have hn : 0 < n := by
    cases n with
    | zero => rw [Nat.zero_mul] at h; exact absurd h (Nat.not_lt_zero m)
    | succ n => exact Nat.succ_pos n
  exact (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm]; exact h)


/-! ### Bit-field packing -/

theorem unpackBits_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    unpackBits f (encodeBits f neg E F) = ⟨neg, E, F⟩ := by
  cases f <;>
  · simp only [IeeeFormat.exponentBits, IeeeFormat.fractionBits, Nat.reducePow] at hE hF
    simp only [unpackBits, encodeBits, zeroBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, FloatComponents.mk.injEq,
      nat_beq_eq_decide]
    cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

theorem encodeBits_lt (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    encodeBits f neg E F < 2 ^ f.width := by
  cases f <;>
  · simp only [IeeeFormat.exponentBits, IeeeFormat.fractionBits, Nat.reducePow] at hE hF
    simp only [encodeBits, zeroBits, IeeeFormat.width, IeeeFormat.fractionBits, Nat.reducePow,
      Nat.reduceSub]
    cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

/-- `pack ∘ unpack = id` on every `F32Bits`. -/
theorem pack_unpack_f32 (x : F32Bits) : packF32 (unpackF32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [packF32, unpackF32, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    nat_beq_eq_decide] at hx ⊢
  generalize x.toNat = n at hx ⊢
  by_cases h : n / 2147483648 % 2 = 1
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, ite_false, Bool.false_eq_true]; omega

/-- `pack ∘ unpack = id` on every `F64Bits`. -/
theorem pack_unpack_f64 (x : F64Bits) : packF64 (unpackF64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [packF64, unpackF64, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    nat_beq_eq_decide] at hx ⊢
  generalize x.toNat = n at hx ⊢
  by_cases h : n / 9223372036854775808 % 2 = 1
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, ite_false, Bool.false_eq_true]; omega

/-- `unpack ∘ pack = id` on well-formed `binary32` fields. -/
theorem unpack_pack_f32 (c : FloatComponents) (he : c.exponent < 2 ^ 8) (hf : c.fraction < 2 ^ 23) :
    unpackF32 (packF32 c) = c := by
  obtain ⟨neg, e, fr⟩ := c
  simp only [Nat.reducePow] at he hf
  simp only [packF32, unpackF32, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    FloatComponents.mk.injEq, nat_beq_eq_decide]
  cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

/-- `unpack ∘ pack = id` on well-formed `binary64` fields. -/
theorem unpack_pack_f64 (c : FloatComponents) (he : c.exponent < 2 ^ 11) (hf : c.fraction < 2 ^ 52) :
    unpackF64 (packF64 c) = c := by
  obtain ⟨neg, e, fr⟩ := c
  simp only [Nat.reducePow] at he hf
  simp only [packF64, unpackF64, packBits, unpackBits, BitVec.toNat_ofNat, IeeeFormat.width,
    IeeeFormat.fractionBits, IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub,
    FloatComponents.mk.injEq, nat_beq_eq_decide]
  cases neg <;> simp <;> (repeat' apply And.intro) <;> omega

/-! ### Decoding agrees with Miri -/

theorem powScale_zero_fst (d : Nat) (e : Int) : (powScale 0 d e).1 = 0 := by
  cases e <;> simp [powScale]

/-- `Nat`'s `==` is `decide (· = ·)` by definition (`instBEqOfDecidableEq`); unlike
`BEq.rfl`, this rewrite is axiom-free. -/
theorem nat_beq_op_eq_decide (a b : Nat) : (a == b) = decide (a = b) := rfl

/-- `decodeBits` agrees with the literal transliteration of
`Miri.Interpreter.FloatBits.decode` on every in-width bit pattern. -/
theorem decodeBits_agrees_miriDecode (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    miriDecode f bits = some ((decodeBits f bits).toMiri f) := by
  have hnot : ¬ (bits ≥ 2 ^ f.width) := by omega
  unfold miriDecode
  simp only [hnot, ↓reduceIte]
  have hneg : (bits / 2 ^ (f.width - 1) != 0) = Nat.beq ((bits / 2 ^ (f.width - 1)) % 2) 1 := by
    have h2 : bits / 2 ^ (f.width - 1) < 2 := by
      cases f <;> simp only [IeeeFormat.width, Nat.reducePow, Nat.reduceSub] at h ⊢ <;> omega
    rw [nat_beq_eq_decide]
    generalize bits / 2 ^ (f.width - 1) = q at h2
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  simp only [decodeBits, unpackBits, hneg]
  generalize Nat.beq ((bits / 2 ^ (f.width - 1)) % 2) 1 = neg
  by_cases hE : (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits = 2 ^ f.exponentBits - 1
  · by_cases hF : bits % 2 ^ f.fractionBits = 0
    · simp only [hE, nat_beq_op_eq_decide, decide_true, ↓reduceIte, hF, FloatKind.toMiri]
    · simp only [hE, nat_beq_op_eq_decide, Bool.false_eq_true, decide_true, decide_false, ↓reduceIte, hF,
        FloatKind.toMiri]
  · by_cases hZ : (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits = 0
    · have h0 : ¬ ((0 : Nat) = 2 ^ f.exponentBits - 1) := by cases f <;> decide
      by_cases hF : bits % 2 ^ f.fractionBits = 0
      · simp only [hZ, nat_beq_op_eq_decide, Bool.false_eq_true, h0, decide_true, decide_false, ↓reduceIte, hF,
          powScale_zero_fst, FloatKind.toMiri]
      · simp only [hZ, nat_beq_op_eq_decide, Bool.false_eq_true, h0, decide_true, decide_false, ↓reduceIte, hF,
          FloatKind.toMiri]
    · simp only [nat_beq_op_eq_decide, Bool.false_eq_true, hE, decide_false, ↓reduceIte, hZ, Int.natCast_emod,
        Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int, FloatKind.toMiri]


/-! ### Float → int soundness -/

theorem floatToIntValue_mem (k : FloatKind) (lo hi : Int) (h0 : lo ≤ 0) (h1 : 0 ≤ hi) :
    lo ≤ floatToIntValue k lo hi ∧ floatToIntValue k lo hi ≤ hi := by
  cases k with
  | nan => simp only [floatToIntValue]; exact ⟨by omega, by omega⟩
  | inf neg => cases neg <;> simp only [floatToIntValue, Bool.false_eq_true, ite_false, ite_true] <;>
      exact ⟨by omega, by omega⟩
  | zero => simp only [floatToIntValue]; exact ⟨by omega, by omega⟩
  | finite neg n d => simp only [floatToIntValue, clampInt]; exact ⟨by omega, by omega⟩

theorem twos_roundtrip (signed : Bool) (w : Nat)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (v : Int)
    (hlo : (if signed = true then -((2 ^ (w - 1) : Nat) : Int) else 0) ≤ v)
    (hhi : v ≤ (if signed = true then ((2 ^ (w - 1) : Nat) : Int) - 1 else ((2 ^ w : Nat) : Int) - 1)) :
    intValueOfBits signed w (encodeTwosComplement w v) = v ∧ encodeTwosComplement w v < 2 ^ w := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> cases signed <;>
    simp only [intValueOfBits, encodeTwosComplement, Nat.reducePow, Nat.reduceSub, Bool.false_eq_true,
      ite_false, ite_true, true_and, false_and] at hlo hhi ⊢ <;>
    (repeat' apply And.intro) <;> omega

theorem IntTarget.bitWidth_cases (t : IntTarget) (pw : PtrWidth) :
    t.bitWidth pw = 8 ∨ t.bitWidth pw = 16 ∨ t.bitWidth pw = 32 ∨ t.bitWidth pw = 64 ∨
      t.bitWidth pw = 128 := by
  cases t <;> rename_i w <;> cases w <;> cases pw <;>
    simp [IntTarget.bitWidth, IntTy.bitWidth, UintTy.bitWidth, PtrWidth.bits]

theorem scalarModulus_div8 (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) :
    scalarModulus (w / 8) = 2 ^ w ∧ w / 8 * 8 = w := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide +kernel, rfl⟩

/-- **`evalFloatToIntSaturating_sound`**: the result is a canonical two's-complement
`ScalarInt` of the target width whose integer value is exactly the saturating,
truncating Rust `as` result `floatToIntValue` (NaN ↦ 0, ±∞ ↦ max/min, finite ↦
`clamp (trunc x)`), and lies in `[min, max]`. -/
theorem evalFloatToIntSaturating_sound (src : IeeeFormat) (bits : Nat) (t : IntTarget)
    (pw : PtrWidth) :
    (evalFloatToIntSaturating src bits t pw).sizeBytes * 8 = t.bitWidth pw ∧
    (evalFloatToIntSaturating src bits t pw).bits <
      scalarModulus (evalFloatToIntSaturating src bits t pw).sizeBytes ∧
    intValueOfBits t.isSigned (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits =
      floatToIntValue (decodeBits src bits) (t.minValue pw) (t.maxValue pw) ∧
    t.minValue pw ≤
      intValueOfBits t.isSigned (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits ∧
    intValueOfBits t.isSigned (t.bitWidth pw) (evalFloatToIntSaturating src bits t pw).bits ≤
      t.maxValue pw := by
  have hw := IntTarget.bitWidth_cases t pw
  obtain ⟨hmod, hdiv⟩ := scalarModulus_div8 _ hw
  have hpos : 1 ≤ t.bitWidth pw := by rcases hw with h | h | h | h | h <;> omega
  have hp1 : 1 ≤ 2 ^ (t.bitWidth pw - 1) := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ t.bitWidth pw := Nat.one_le_two_pow
  have h0 : t.minValue pw ≤ 0 := by
    unfold IntTarget.minValue; split <;> omega
  have h1 : 0 ≤ t.maxValue pw := by
    unfold IntTarget.maxValue; split <;> omega
  obtain ⟨hlo, hhi⟩ := floatToIntValue_mem (decodeBits src bits) _ _ h0 h1
  have hrt := twos_roundtrip t.isSigned (t.bitWidth pw) hw
    (floatToIntValue (decodeBits src bits) (t.minValue pw) (t.maxValue pw))
    (by unfold IntTarget.minValue at hlo; exact hlo)
    (by unfold IntTarget.maxValue at hhi; exact hhi)
  simp only [evalFloatToIntSaturating]
  refine ⟨hdiv, ?_, hrt.1, ?_, ?_⟩
  · rw [hmod]; exact hrt.2
  · rw [hrt.1]; exact hlo
  · rw [hrt.1]; exact hhi

/-- NaN inputs produce `0`. -/
theorem evalFloatToIntSaturating_nan (src : IeeeFormat) (bits : Nat) (t : IntTarget) (pw : PtrWidth)
    (h : isNaNBits src bits = true) : (evalFloatToIntSaturating src bits t pw).bits = 0 := by
  simp only [isNaNBits] at h
  simp only [evalFloatToIntSaturating, encodeTwosComplement]
  split at h <;> simp_all [floatToIntValue]

/-! ### Rounding core -/

/-- **`<= 0.5` ULP**: the ties-to-even quotient is within half a unit of the exact
quotient. -/
theorem roundQuotientTiesToEven_half_ulp (n d : Nat) (hd : 0 < d) :
    2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs ≤ d := by
  have hdm := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  unfold roundQuotientTiesToEven
  simp only
  split
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]
    generalize d * (n / d) = D at hdm ⊢
    omega
  · rw [Nat.mul_comm (n / d) d]
    generalize d * (n / d) = D at hdm ⊢
    omega

/-- **Even-LSB tie-breaking**: at an exact tie, the ties-to-even quotient is even. -/
theorem roundQuotientTiesToEven_tie_even (n d : Nat) (hd : 0 < d)
    (htie : 2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs = d) :
    roundQuotientTiesToEven n d % 2 = 0 := by
  have hdm := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  unfold roundQuotientTiesToEven at htie ⊢
  simp only at htie ⊢
  split at htie <;> rename_i hc <;> simp only [hc, ite_true, ite_false] at ⊢
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d] at htie
    generalize d * (n / d) = D at hdm htie
    omega
  · rw [Nat.mul_comm (n / d) d] at htie
    by_cases hE : n % d * 2 = d
    · cases Nat.mod_two_eq_zero_or_one (n / d) with
      | inl h' => exact h'
      | inr h' => exact absurd (Or.inr ⟨hE, h'⟩) hc
    · clear hc
      generalize d * (n / d) = D at hdm htie
      omega


/-! ### Exactness machinery for `roundRatioBits` -/

theorem nat_log2_eq_of_bounds (m L : Nat) (h1 : 2 ^ L ≤ m) (h2 : m < 2 ^ (L + 1)) :
    Nat.log2 m = L := by
  have hm : m ≠ 0 := by have := Nat.one_le_two_pow (n := L); omega
  have ha : L ≤ Nat.log2 m := (Nat.le_log2 hm).mpr h1
  have hb : Nat.log2 m < L + 1 := (Nat.log2_lt hm).mpr h2
  omega

theorem nat_log2_two_pow (L : Nat) : Nat.log2 (2 ^ L) = L :=
  nat_log2_eq_of_bounds (2 ^ L) L (Nat.le_refl _) (two_pow_lt_two_pow (Nat.lt_succ_self L))

theorem pow_mul_pow (a b : Nat) : 2 ^ a * 2 ^ b = 2 ^ (a + b) := (Nat.pow_add 2 a b).symm

/-- `ratioExponent (S * 2^k) 1 = log2 S + k`. -/
theorem ratioExponent_mul_pow (S k : Nat) (hS : 0 < S) :
    ratioExponent (S * 2 ^ k) 1 = ((Nat.log2 S + k : Nat) : Int) := by
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hS)
  have hL2 := Nat.lt_log2_self (n := S)
  have hk := Nat.one_le_two_pow (n := k)
  unfold ratioExponent
  have h1 : 1 ≤ S * 2 ^ k := Nat.mul_le_mul hS hk
  rw [if_pos' h1, Nat.div_one]
  congr 1
  apply nat_log2_eq_of_bounds
  · rw [← pow_mul_pow]; exact Nat.mul_le_mul_right _ hL1
  · rw [show Nat.log2 S + k + 1 = (Nat.log2 S + 1) + k by omega, ← pow_mul_pow]
    exact Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos k)

/-- `ratioExponent S (2^j) = log2 S - j`. -/
theorem ratioExponent_div_pow (S j : Nat) (hS : 0 < S) :
    ratioExponent S (2 ^ j) = (Nat.log2 S : Int) - (j : Int) := by
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hS)
  have hL2 := Nat.lt_log2_self (n := S)
  generalize hL : Nat.log2 S = L at hL1 hL2
  unfold ratioExponent
  by_cases hc : 2 ^ j ≤ S
  · rw [if_pos' hc]
    have hjL : j ≤ L := by
      have : 2 ^ j < 2 ^ (L + 1) := Nat.lt_of_le_of_lt hc hL2
      have := lt_of_two_pow_lt this
      omega
    have hlog : Nat.log2 (S / 2 ^ j) = L - j := by
      apply nat_log2_eq_of_bounds
      · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos j), pow_mul_pow, Nat.sub_add_cancel hjL]
        exact hL1
      · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), pow_mul_pow,
          show L - j + 1 + j = L + 1 by omega]
        exact hL2
    rw [hlog]; omega
  · rw [if_neg' hc]
    have hLj : L < j := by
      have : 2 ^ L < 2 ^ j := Nat.lt_of_le_of_lt hL1 (Nat.lt_of_not_le hc)
      exact lt_of_two_pow_lt this
    by_cases hp : S = 2 ^ L
    · subst hp
      have hdiv : 2 ^ j / 2 ^ L = 2 ^ (j - L) := Nat.pow_div (Nat.le_of_lt hLj) (by decide)
      simp only [hdiv, nat_log2_two_pow]
      have : 2 ^ j ≤ 2 ^ L * 2 ^ (j - L) := by
        rw [pow_mul_pow, Nat.add_sub_cancel' (Nat.le_of_lt hLj)]; exact Nat.le_refl _
      rw [if_pos' this]; omega
    · have hgt : 2 ^ L < S := Nat.lt_of_le_of_ne hL1 (Ne.symm hp)
      have hlog : Nat.log2 (2 ^ j / S) = j - L - 1 := by
        apply nat_log2_eq_of_bounds
        · rw [Nat.le_div_iff_mul_le hS]
          have : 2 ^ (j - L - 1) * S < 2 ^ (j - L - 1) * 2 ^ (L + 1) :=
            Nat.mul_lt_mul_of_pos_left hL2 (Nat.two_pow_pos _)
          rw [pow_mul_pow, show j - L - 1 + (L + 1) = j by omega] at this
          exact Nat.le_of_lt this
        · rw [Nat.div_lt_iff_lt_mul hS, show j - L - 1 + 1 = j - L by omega]
          have : 2 ^ (j - L) * 2 ^ L < 2 ^ (j - L) * S :=
            Nat.mul_lt_mul_of_pos_left hgt (Nat.two_pow_pos _)
          rw [pow_mul_pow, show j - L + L = j by omega] at this
          exact this
      rw [hlog]
      have hnot : ¬ (2 ^ j ≤ S * 2 ^ (j - L - 1)) := by
        have : S * 2 ^ (j - L - 1) < 2 ^ (L + 1) * 2 ^ (j - L - 1) :=
          Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
        rw [pow_mul_pow, show L + 1 + (j - L - 1) = j by omega] at this
        omega
      rw [if_neg' hnot]; omega


/-- Scale invariance of `ratioExponent`. -/
theorem ratioExponent_mul (n d c : Nat) (hc : 0 < c) :
    ratioExponent (n * c) (d * c) = ratioExponent n d := by
  unfold ratioExponent
  have e1 : (d * c ≤ n * c) ↔ d ≤ n := Nat.mul_le_mul_right_iff hc
  have e2 : n * c / (d * c) = n / d := Nat.mul_div_mul_right n d hc
  have e3 : d * c / (n * c) = d / n := Nat.mul_div_mul_right d n hc
  have e4 : ∀ k, (d * c ≤ n * c * 2 ^ k) ↔ d ≤ n * 2 ^ k := fun k => by
    rw [Nat.mul_right_comm n c]; exact Nat.mul_le_mul_right_iff hc
  by_cases h : d ≤ n
  · rw [if_pos' (e1.mpr h), if_pos' h, e2]
  · rw [if_neg' (fun h' => h (e1.mp h')), if_neg' h, e3]
    by_cases h' : d ≤ n * 2 ^ (d / n).log2
    · rw [if_pos' ((e4 _).mpr h'), if_pos' h']
    · rw [if_neg' (fun h'' => h' ((e4 _).mp h'')), if_neg' h']

/-- Scale invariance of `powScale`. -/
theorem powScale_mul (n d c : Nat) (e : Int) :
    powScale (n * c) (d * c) e = ((powScale n d e).1 * c, (powScale n d e).2 * c) := by
  cases e <;> simp [powScale, Nat.mul_right_comm]

/-- Scale invariance of the rounding core. -/
theorem roundQuotient_mul (mode : RoundingMode) (a b c : Nat) (hc : 0 < c) :
    roundQuotient mode (a * c) (b * c) = roundQuotient mode a b := by
  have hq : a * c / (b * c) = a / b := Nat.mul_div_mul_right a b hc
  have hr : a * c % (b * c) = a % b * c := Nat.mul_mod_mul_right c a b
  have g1 : (a % b * c * 2 > b * c) ↔ (a % b * 2 > b) := by
    rw [Nat.mul_right_comm]; exact nat_mul_lt_mul_right_iff hc
  have g2 : (a % b * c * 2 = b * c) ↔ (a % b * 2 = b) := by
    rw [Nat.mul_right_comm]; exact Nat.mul_right_cancel_iff hc
  have g3 : (a % b * c * 2 ≥ b * c) ↔ (a % b * 2 ≥ b) := by
    rw [Nat.mul_right_comm]; exact Nat.mul_le_mul_right_iff hc
  cases mode <;> simp only [roundQuotient, roundQuotientTiesToEven, roundQuotientHalfAwayFromZero, hq, hr, g1, g2, g3]

/-- Exact quotients are returned unchanged. -/
theorem roundQuotient_exact (mode : RoundingMode) (S c : Nat) (hc : 0 < c) :
    roundQuotient mode (S * c) c = S := by
  have hq : S * c / c = S := Nat.mul_div_cancel S hc
  have hr : S * c % c = 0 := Nat.mul_mod_left S c
  cases mode <;> simp only [roundQuotient, roundQuotientTiesToEven, roundQuotientHalfAwayFromZero, hq, hr] <;>
    simp only [Nat.zero_mul] <;> split <;> omega

/-- **Scale invariance of `roundRatioBits`**. -/
theorem roundRatioBits_mul (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d c : Nat)
    (hc : 0 < c) : roundRatioBits mode f neg (n * c) (d * c) = roundRatioBits mode f neg n d := by
  have hd : (d * c = 0) ↔ d = 0 := by
    constructor
    · intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega
    · intro h; simp [h]
  have hn : (n * c = 0) ↔ n = 0 := by
    constructor
    · intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega
    · intro h; simp [h]
  unfold roundRatioBits
  simp only [hd, hn, ratioExponent_mul n d c hc, powScale_mul, roundQuotient_mul mode _ _ c hc]

/-- **Rational congruence of `roundRatioBits`**: equal rationals round identically. -/
theorem roundRatioBits_congr (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n₁ d₁ n₂ d₂ : Nat)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : n₁ * d₂ = n₂ * d₁) :
    roundRatioBits mode f neg n₁ d₁ = roundRatioBits mode f neg n₂ d₂ := by
  rw [← roundRatioBits_mul mode f neg n₁ d₁ d₂ h₂, ← roundRatioBits_mul mode f neg n₂ d₂ d₁ h₁, h,
    Nat.mul_comm d₁ d₂]


theorem powScale_snd_pos (S : Nat) (t : Int) : 0 < (powScale S 1 t).2 := by
  cases t <;> simp [powScale, Nat.two_pow_pos]

theorem powScale_fst_pos (S d : Nat) (t : Int) (hS : 0 < S) : 0 < (powScale S d t).1 := by
  cases t with
  | ofNat k => exact Nat.mul_pos hS (Nat.two_pow_pos k)
  | negSucc k => exact hS

/-- `roundQuotient` undoes the scaling `powScale (powScale S 1 t) (-t)`. -/
theorem roundQuotient_powScale_neg (mode : RoundingMode) (S : Nat) (t : Int) :
    roundQuotient mode (powScale (powScale S 1 t).1 (powScale S 1 t).2 (-t)).1
      (powScale (powScale S 1 t).1 (powScale S 1 t).2 (-t)).2 = S := by
  match t with
  | .ofNat 0 =>
    simp only [powScale, Nat.pow_zero, Nat.mul_one]
    exact roundQuotient_exact mode S 1 (by decide) |>.trans rfl |> fun h => by simpa using h
  | .ofNat (k + 1) =>
    show roundQuotient mode (powScale (S * 2 ^ (k + 1)) 1 (Int.negSucc k)).1
      (powScale (S * 2 ^ (k + 1)) 1 (Int.negSucc k)).2 = S
    simp only [powScale, Nat.one_mul]
    exact roundQuotient_exact mode S _ (Nat.two_pow_pos _)
  | .negSucc k =>
    show roundQuotient mode (powScale S (1 * 2 ^ (k + 1)) (Int.ofNat (k + 1))).1
      (powScale S (1 * 2 ^ (k + 1)) (Int.ofNat (k + 1))).2 = S
    simp only [powScale, Nat.one_mul]
    exact roundQuotient_exact mode S _ (Nat.two_pow_pos _)

/-- `ratioExponent` of `powScale S 1 t` is `log2 S + t`. -/
theorem ratioExponent_powScale (S : Nat) (t : Int) (hS : 0 < S) :
    ratioExponent (powScale S 1 t).1 (powScale S 1 t).2 = (Nat.log2 S : Int) + t := by
  cases t with
  | ofNat k =>
    simp only [powScale]
    rw [ratioExponent_mul_pow S k hS, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    simp only [powScale, Nat.one_mul]
    rw [ratioExponent_div_pow S (k + 1) hS]; omega

theorem IeeeFormat.fb_le_bias (f : IeeeFormat) : f.fractionBits + 1 ≤ f.bias := by
  cases f <;> decide

theorem IeeeFormat.one_le_fb (f : IeeeFormat) : 1 ≤ f.fractionBits := by
  cases f <;> decide

/-- **Exactness (normal)**: a value `S * 2^t` with a normal significand
`2^fb ≤ S < 2^(fb+1)` and in-range exponent `t + fb` is encoded exactly, in every
rounding mode. -/
theorem roundRatioBits_normal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat) (t : Int)
    (hS1 : 2 ^ f.fractionBits ≤ S) (hS2 : S < 2 ^ (f.fractionBits + 1))
    (hE1 : f.minExponent ≤ t + f.fractionBits) (hE2 : t + f.fractionBits ≤ f.maxExponent) :
    roundRatioBits mode f neg (powScale S 1 t).1 (powScale S 1 t).2 =
      encodeBits f neg (t + f.fractionBits + f.bias).toNat (S - 2 ^ f.fractionBits) := by
  have hSpos : 0 < S := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hS1
  have hlog : Nat.log2 S = f.fractionBits := nat_log2_eq_of_bounds S _ hS1 hS2
  have hd : (powScale S 1 t).2 ≠ 0 := Nat.pos_iff_ne_zero.mp (powScale_snd_pos S t)
  have hn : (powScale S 1 t).1 ≠ 0 := Nat.pos_iff_ne_zero.mp (powScale_fst_pos S 1 t hSpos)
  have hre := ratioExponent_powScale S t hSpos
  rw [hlog] at hre
  have hmax : max (ratioExponent (powScale S 1 t).1 (powScale S 1 t).2) f.minExponent =
      t + f.fractionBits := by rw [hre]; omega
  have hsc : (f.fractionBits : Int) - (t + f.fractionBits) = -t := by omega
  have hsig := roundQuotient_powScale_neg mode S t
  have hcarry : ¬ (2 ^ (f.fractionBits + 1) ≤ S) := Nat.not_le.mpr hS2
  have hlt : ¬ (S < 2 ^ f.fractionBits) := Nat.not_lt.mpr hS1
  have hgt : ¬ (t + f.fractionBits > f.maxExponent) := by omega
  unfold roundRatioBits
  simp only [hd, hn, hmax, hsc, hsig, hcarry, hlt, hgt, decide_false, Bool.false_eq_true, ite_false]

/-- **Exactness (subnormal)**: `S * 2^(minExp - fb)` with `0 < S < 2^fb` is encoded as
the subnormal `(0, S)`, in every rounding mode. -/
theorem roundRatioBits_subnormal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat)
    (hS0 : 0 < S) (hS : S < 2 ^ f.fractionBits) :
    roundRatioBits mode f neg (powScale S 1 (f.minExponent - f.fractionBits)).1
        (powScale S 1 (f.minExponent - f.fractionBits)).2 =
      encodeBits f neg 0 S := by
  have hlogS : Nat.log2 S < f.fractionBits := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hS0)).mpr hS
  have hfb := IeeeFormat.fb_le_bias f
  have hd : (powScale S 1 (f.minExponent - f.fractionBits)).2 ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (powScale_snd_pos S _)
  have hn : (powScale S 1 (f.minExponent - f.fractionBits)).1 ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (powScale_fst_pos S 1 _ hS0)
  have hre := ratioExponent_powScale S (f.minExponent - f.fractionBits) hS0
  have hmax : max (ratioExponent (powScale S 1 (f.minExponent - f.fractionBits)).1
      (powScale S 1 (f.minExponent - f.fractionBits)).2) f.minExponent = f.minExponent := by
    rw [hre]; simp only [IeeeFormat.minExponent] at *; omega
  have hsc : (f.fractionBits : Int) - f.minExponent = -(f.minExponent - f.fractionBits) := by omega
  have hsig := roundQuotient_powScale_neg mode S (f.minExponent - f.fractionBits)
  have hcarry : ¬ (2 ^ (f.fractionBits + 1) ≤ S) := by
    have : 2 ^ f.fractionBits < 2 ^ (f.fractionBits + 1) :=
      two_pow_lt_two_pow (by omega)
    omega
  have hgt : ¬ (f.minExponent > f.maxExponent) := by
    simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent]; omega
  unfold roundRatioBits
  simp only [hd, hn, hmax, hsc, hsig, hcarry, hS, hgt, decide_false, Bool.false_eq_true, ite_false,
    ite_true]

/-- Decoding of explicitly encoded fields. -/
theorem decodeBits_encodeBits (f : IeeeFormat) (neg : Bool) (E F : Nat)
    (hE : E < 2 ^ f.exponentBits) (hF : F < 2 ^ f.fractionBits) :
    decodeBits f (encodeBits f neg E F) =
      if E = 2 ^ f.exponentBits - 1 then
        (if F = 0 then .inf neg
         else .nan neg (Nat.beq ((F / 2 ^ (f.fractionBits - 1)) % 2) 1) F)
      else if E = 0 then
        (if F = 0 then .zero neg
         else .finite neg (powScale F 1 (f.minExponent - f.fractionBits)).1
           (powScale F 1 (f.minExponent - f.fractionBits)).2)
      else .finite neg (powScale (2 ^ f.fractionBits + F) 1 ((E : Int) - f.bias - f.fractionBits)).1
        (powScale (2 ^ f.fractionBits + F) 1 ((E : Int) - f.bias - f.fractionBits)).2 := by
  unfold decodeBits
  rw [unpackBits_encodeBits f neg E F hE hF]

/-- Re-encoding the unpacked fields reproduces the bit pattern. -/
theorem encodeBits_unpackBits (f : IeeeFormat) (bits : Nat) (h : bits < 2 ^ f.width) :
    encodeBits f (unpackBits f bits).neg (unpackBits f bits).exponent (unpackBits f bits).fraction =
      bits := by
  cases f
  · simp only [IeeeFormat.width, Nat.reducePow] at h
    simp only [encodeBits, zeroBits, unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, nat_beq_eq_decide]
    by_cases hb : bits / 2147483648 % 2 = 1
    · simp only [hb, decide_true, ite_true]; omega
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false]; omega
  · simp only [IeeeFormat.width, Nat.reducePow] at h
    simp only [encodeBits, zeroBits, unpackBits, IeeeFormat.width, IeeeFormat.fractionBits,
      IeeeFormat.exponentBits, Nat.reducePow, Nat.reduceSub, nat_beq_eq_decide]
    by_cases hb : bits / 9223372036854775808 % 2 = 1
    · simp only [hb, decide_true, ite_true]; omega
    · simp only [hb, decide_false, Bool.false_eq_true, ite_false]; omega

theorem unpackBits_exponent_lt (f : IeeeFormat) (bits : Nat) :
    (unpackBits f bits).exponent < 2 ^ f.exponentBits := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem unpackBits_fraction_lt (f : IeeeFormat) (bits : Nat) :
    (unpackBits f bits).fraction < 2 ^ f.fractionBits := Nat.mod_lt _ (Nat.two_pow_pos _)


theorem IeeeFormat.two_bias_lt (f : IeeeFormat) : 2 * f.bias < 2 ^ f.exponentBits - 1 := by
  cases f <;> decide

theorem IeeeFormat.max_exp_ne_zero (f : IeeeFormat) : ¬ ((0 : Nat) = 2 ^ f.exponentBits - 1) := by
  cases f <;> decide

/-- Decoding a correctly rounded normal value recovers it exactly. -/
theorem decodeBits_roundRatio_normal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat)
    (t : Int) (hS1 : 2 ^ f.fractionBits ≤ S) (hS2 : S < 2 ^ (f.fractionBits + 1))
    (hE1 : f.minExponent ≤ t + f.fractionBits) (hE2 : t + f.fractionBits ≤ f.maxExponent) :
    decodeBits f (roundRatioBits mode f neg (powScale S 1 t).1 (powScale S 1 t).2) =
      .finite neg (powScale S 1 t).1 (powScale S 1 t).2 := by
  rw [roundRatioBits_normal mode f neg S t hS1 hS2 hE1 hE2]
  have hb := IeeeFormat.two_bias_lt f
  simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hE1 hE2
  have hEnn : 0 ≤ t + f.fractionBits + f.bias := by omega
  have hE : ((t + f.fractionBits + f.bias).toNat : Int) = t + f.fractionBits + f.bias :=
    Int.toNat_of_nonneg hEnn
  have hEub : (t + f.fractionBits + f.bias).toNat < 2 ^ f.exponentBits := by omega
  have hEne : ¬ ((t + f.fractionBits + f.bias).toNat = 2 ^ f.exponentBits - 1) := by omega
  have hE0 : ¬ ((t + f.fractionBits + f.bias).toNat = 0) := by omega
  have hF : S - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
    have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by rw [Nat.pow_succ]; omega
    omega
  rw [decodeBits_encodeBits f neg _ _ hEub hF, if_neg' hEne, if_neg' hE0,
    Nat.add_sub_cancel' hS1]
  have ht : (((t + f.fractionBits + f.bias).toNat : Nat) : Int) - f.bias - f.fractionBits = t := by
    omega
  rw [ht]

/-- Decoding a correctly rounded subnormal value recovers it exactly. -/
theorem decodeBits_roundRatio_subnormal (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (S : Nat)
    (hS0 : 0 < S) (hS : S < 2 ^ f.fractionBits) :
    decodeBits f (roundRatioBits mode f neg (powScale S 1 (f.minExponent - f.fractionBits)).1
        (powScale S 1 (f.minExponent - f.fractionBits)).2) =
      .finite neg (powScale S 1 (f.minExponent - f.fractionBits)).1
        (powScale S 1 (f.minExponent - f.fractionBits)).2 := by
  rw [roundRatioBits_subnormal mode f neg S hS0 hS,
    decodeBits_encodeBits f neg 0 S (Nat.two_pow_pos _) hS, if_neg' (IeeeFormat.max_exp_ne_zero f),
    if_pos' rfl, if_neg' (by omega)]

/-- Shifting the significand by `2^j` and the exponent by `-j` preserves the rational
value (cross-multiplication form). -/
theorem powScale_shift_cross (S j : Nat) (t : Int) :
    (powScale (S * 2 ^ j) 1 (t - j)).1 * (powScale S 1 t).2 =
      (powScale S 1 t).1 * (powScale (S * 2 ^ j) 1 (t - j)).2 := by
  have key : ∀ (S' : Nat) (u : Int), powScale S' 1 u =
      if 0 ≤ u then (S' * 2 ^ u.toNat, 1) else (S', 2 ^ (-u).toNat) := by
    intro S' u
    cases u with
    | ofNat k => simp [powScale]
    | negSucc k =>
      simp only [powScale, Nat.one_mul]
      have : ¬ (0 ≤ Int.negSucc k) := by omega
      rw [if_neg' this]
      simp [Int.neg_negSucc]
  rw [key S t, key (S * 2 ^ j) (t - j)]
  by_cases h2 : 0 ≤ t
  · by_cases h1 : 0 ≤ t - (j : Int)
    · rw [if_pos' h1, if_pos' h2]
      simp only [Nat.mul_one, Nat.mul_assoc, pow_mul_pow]
      congr 2; omega
    · rw [if_neg' h1, if_pos' h2]
      simp only [Nat.mul_one, Nat.mul_assoc, pow_mul_pow]
      congr 2; omega
  · have h1 : ¬ (0 ≤ t - (j : Int)) := by omega
    rw [if_neg' h1, if_neg' h2]
    simp only [Nat.mul_assoc, pow_mul_pow]
    congr 2; omega

/-- `k` denotes exactly the integer `v`. -/
def FloatKind.denotesInt : FloatKind → Int → Prop
  | .zero neg, v => v = 0 ∧ neg = false
  | .finite neg n d, v => 0 < d ∧ n = v.natAbs * d ∧ neg = decide (v < 0)
  | _, _ => False

theorem IeeeFormat.fb_add_bias_lt (f : IeeeFormat) :
    f.fractionBits + f.bias < 2 ^ f.exponentBits - 1 := by
  cases f <;> decide

/-- **Exactness on representable integers**: every integer `v` with
`|v| < 2^(fb+1)` (in particular every `i32` / `u32` into `binary64`) converts exactly. -/
theorem evalIntToFloatRoundTiesToEven_exact (signed : Bool) (w bits : Nat) (dst : IeeeFormat)
    (h : (intValueOfBits signed w bits).natAbs < 2 ^ (dst.fractionBits + 1)) :
    (decodeBits dst (evalIntToFloatRoundTiesToEven signed w bits dst)).denotesInt
      (intValueOfBits signed w bits) := by
  simp only [evalIntToFloatRoundTiesToEven]
  generalize intValueOfBits signed w bits = v at h ⊢
  by_cases hv : v = 0
  · subst hv
    have hz : roundRatioBits .tiesToEven dst (decide ((0 : Int) < 0)) (Int.natAbs 0) 1 =
        encodeBits dst false 0 0 := by
      simp [roundRatioBits, zeroBits, encodeBits]
    rw [hz, decodeBits_encodeBits dst false 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
      if_neg' (IeeeFormat.max_exp_ne_zero dst), if_pos' rfl, if_pos' rfl]
    exact ⟨rfl, rfl⟩
  · have hm : 0 < v.natAbs := by omega
    generalize hmv : v.natAbs = m at hm h
    have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hm)
    have hL2 := Nat.lt_log2_self (n := m)
    generalize hLv : Nat.log2 m = L at hL1 hL2
    have hLfb : L ≤ dst.fractionBits := by
      have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hm)).mpr h
      omega
    have hfb := IeeeFormat.fb_le_bias dst
    have hS1 : 2 ^ dst.fractionBits ≤ m * 2 ^ (dst.fractionBits - L) := by
      have := Nat.mul_le_mul_right (2 ^ (dst.fractionBits - L)) hL1
      rwa [pow_mul_pow, Nat.add_sub_cancel' hLfb] at this
    have hS2 : m * 2 ^ (dst.fractionBits - L) < 2 ^ (dst.fractionBits + 1) := by
      have := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos (dst.fractionBits - L))
      rwa [pow_mul_pow, show L + 1 + (dst.fractionBits - L) = dst.fractionBits + 1 by omega] at this
    have hcross := powScale_shift_cross m (dst.fractionBits - L) 0
    have h0 : powScale m 1 0 = (m, 1) := by simp [powScale]
    rw [h0] at hcross
    simp only [Nat.mul_one] at hcross
    have hcong : roundRatioBits .tiesToEven dst (decide (v < 0)) m 1 =
        roundRatioBits .tiesToEven dst (decide (v < 0))
          (powScale (m * 2 ^ (dst.fractionBits - L)) 1 (0 - ((dst.fractionBits - L : Nat) : Int))).1
          (powScale (m * 2 ^ (dst.fractionBits - L)) 1 (0 - ((dst.fractionBits - L : Nat) : Int))).2 :=
      roundRatioBits_congr _ _ _ _ _ _ _ (by decide) (powScale_snd_pos _ _)
        (by rw [Nat.mul_one]; exact hcross.symm)
    rw [hcong, decodeBits_roundRatio_normal _ _ _ _ _ hS1 hS2
      (by simp only [IeeeFormat.minExponent]; omega) (by simp only [IeeeFormat.maxExponent]; omega)]
    refine ⟨powScale_snd_pos _ _, ?_, rfl⟩
    rw [hmv]; exact hcross

/-- Every `i32` / `u32` converts to `binary64` exactly. -/
theorem evalIntToFloat_i32_u32_to_f64_exact (signed : Bool) (bits : Nat) :
    (decodeBits .binary64 (evalIntToFloatRoundTiesToEven signed 32 bits .binary64)).denotesInt
      (intValueOfBits signed 32 bits) := by
  apply evalIntToFloatRoundTiesToEven_exact
  simp only [intValueOfBits, IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceSub]
  have := Nat.mod_lt bits (show 0 < 4294967296 by decide)
  split <;> omega


/-- Two decoded values are the same extended real (same sign; equal rationals). -/
def FloatKind.sameValue : FloatKind → FloatKind → Prop
  | .zero n₁, .zero n₂ => n₁ = n₂
  | .finite s₁ a₁ b₁, .finite s₂ a₂ b₂ => s₁ = s₂ ∧ a₁ * b₂ = a₂ * b₁ ∧ 0 < b₁ ∧ 0 < b₂
  | .inf n₁, .inf n₂ => n₁ = n₂
  | _, _ => False

theorem zeroBits_eq_encodeBits (f : IeeeFormat) (neg : Bool) : zeroBits f neg = encodeBits f neg 0 0 := by
  simp [encodeBits]

/-- Normal `binary64` side conditions as hypotheses (avoids multi-line nested `by`). -/
theorem f64_encode_lt (neg : Bool) (E F : Nat) (hE : E < 2048) (hF : F < 4503599627370496) :
    encodeBits .binary64 neg E F < 2 ^ 64 := encodeBits_lt .binary64 neg E F hE hF

theorem convertFloatBits_of_zero (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat) (neg : Bool)
    (h : decodeBits src bits = .zero neg) : convertFloatBits mode src dst bits = zeroBits dst neg := by
  unfold convertFloatBits; rw [h]

theorem convertFloatBits_of_inf (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat) (neg : Bool)
    (h : decodeBits src bits = .inf neg) : convertFloatBits mode src dst bits = infBits dst neg := by
  unfold convertFloatBits; rw [h]

theorem convertFloatBits_of_finite (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat) (neg : Bool)
    (n d : Nat) (h : decodeBits src bits = .finite neg n d) :
    convertFloatBits mode src dst bits = roundRatioBits mode dst neg n d := by
  unfold convertFloatBits; rw [h]

theorem isNaNBits_of_nan (f : IeeeFormat) (bits : Nat) (neg q : Bool) (p : Nat)
    (h : decodeBits f bits = .nan neg q p) : isNaNBits f bits = true := by
  unfold isNaNBits; rw [h]

/-- Round-trip obligation for one `binary32` bit pattern. -/
def F32RoundTrip (b : Nat) : Prop :=
  ∃ W, W < 2 ^ 64 ∧
    convertFloatBits .tiesToEven .binary32 .binary64 b = W ∧
    (decodeBits .binary64 W).sameValue (decodeBits .binary32 b) ∧
    convertFloatBits .tiesToEven .binary64 .binary32 W = b

theorem f32_rt_inf (neg : Bool) : F32RoundTrip (encodeBits .binary32 neg 255 0) := by
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 255 0) = .inf neg := by
    rw [decodeBits_encodeBits .binary32 neg 255 0 (by decide) (by decide)]
    simp [IeeeFormat.exponentBits]
  have hd64 : decodeBits .binary64 (infBits .binary64 neg) = .inf neg := by
    simp only [infBits]
    rw [decodeBits_encodeBits .binary64 neg _ 0 (by decide) (by decide)]
    simp
  have hback : infBits .binary32 neg = encodeBits .binary32 neg 255 0 := by
    simp [infBits, IeeeFormat.exponentBits]
  refine ⟨infBits .binary64 neg, f64_encode_lt neg _ _ (by decide) (by decide), ?_, ?_, ?_⟩
  · exact convertFloatBits_of_inf _ _ _ _ _ hdec32
  · rw [hd64, hdec32]; exact rfl
  · rw [convertFloatBits_of_inf _ _ _ _ _ hd64]; exact hback

theorem f32_rt_zero (neg : Bool) : F32RoundTrip (encodeBits .binary32 neg 0 0) := by
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 0 0) = .zero neg := by
    rw [decodeBits_encodeBits .binary32 neg 0 0 (by decide) (by decide)]
    simp [IeeeFormat.exponentBits]
  have hd64 : decodeBits .binary64 (zeroBits .binary64 neg) = .zero neg := by
    rw [zeroBits_eq_encodeBits, decodeBits_encodeBits .binary64 neg 0 0 (by decide) (by decide)]
    simp [IeeeFormat.exponentBits]
  have hz64 : zeroBits .binary64 neg < 2 ^ 64 := by
    rw [zeroBits_eq_encodeBits]; exact f64_encode_lt neg 0 0 (by decide) (by decide)
  refine ⟨zeroBits .binary64 neg, hz64, ?_, ?_, ?_⟩
  · exact convertFloatBits_of_zero _ _ _ _ _ hdec32
  · rw [hd64, hdec32]; exact rfl
  · rw [convertFloatBits_of_zero _ _ _ _ _ hd64]; exact zeroBits_eq_encodeBits .binary32 neg

theorem f32_rt_subnormal (neg : Bool) (F : Nat) (hF0 : F ≠ 0) (hFl : F < 8388608) :
    F32RoundTrip (encodeBits .binary32 neg 0 F) := by
  have hdec := decodeBits_encodeBits .binary32 neg 0 F (by decide) hFl
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 0 F) =
      .finite neg (powScale F 1 (IeeeFormat.binary32.minExponent - IeeeFormat.binary32.fractionBits)).1
        (powScale F 1 (IeeeFormat.binary32.minExponent - IeeeFormat.binary32.fractionBits)).2 := by
    rw [hdec]; simp [hF0, IeeeFormat.exponentBits, IeeeFormat.fractionBits, IeeeFormat.bias,
      IeeeFormat.minExponent]
  have hFpos : 0 < F := Nat.pos_of_ne_zero hF0
  have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hFpos)
  have hL2 := Nat.lt_log2_self (n := F)
  generalize hLv : Nat.log2 F = L at hL1 hL2
  have hL23 : L < 23 := by
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hFpos)).mpr (show F < 2 ^ 23 from hFl)
    omega
  have hS1 : 2 ^ IeeeFormat.binary64.fractionBits ≤ F * 2 ^ (52 - L) := by
    have := Nat.mul_le_mul_right (2 ^ (52 - L)) hL1
    rwa [pow_mul_pow, show L + (52 - L) = 52 by omega] at this
  have hS2 : F * 2 ^ (52 - L) < 2 ^ (IeeeFormat.binary64.fractionBits + 1) := by
    have := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos (52 - L))
    rwa [pow_mul_pow, show L + 1 + (52 - L) = 52 + 1 by omega] at this
  generalize ht : (IeeeFormat.binary32.minExponent - IeeeFormat.binary32.fractionBits : Int) = t
    at hdec32
  have htv : t = -149 := by
    rw [← ht]; simp [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]
  have hcross := powScale_shift_cross F (52 - L) t
  have hE1 : IeeeFormat.binary64.minExponent ≤ t - ((52 - L : Nat) : Int) + IeeeFormat.binary64.fractionBits := by
    simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hE2 : t - ((52 - L : Nat) : Int) + IeeeFormat.binary64.fractionBits ≤ IeeeFormat.binary64.maxExponent := by
    simp only [IeeeFormat.maxExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hcong := fun f => roundRatioBits_congr .tiesToEven f neg
    (powScale F 1 t).1 (powScale F 1 t).2
    (powScale (F * 2 ^ (52 - L)) 1 (t - ((52 - L : Nat) : Int))).1
    (powScale (F * 2 ^ (52 - L)) 1 (t - ((52 - L : Nat) : Int))).2
    (powScale_snd_pos _ _) (powScale_snd_pos _ _) hcross.symm
  have hn64 := roundRatioBits_normal .tiesToEven .binary64 neg _ _ hS1 hS2 hE1 hE2
  have hd64 := decodeBits_roundRatio_normal .tiesToEven .binary64 neg _ _ hS1 hS2 hE1 hE2
  have hsub32 := roundRatioBits_subnormal .tiesToEven .binary32 neg F hFpos hFl
  rw [ht] at hsub32
  have hWlt : encodeBits .binary64 neg
      (t - ((52 - L : Nat) : Int) + IeeeFormat.binary64.fractionBits + IeeeFormat.binary64.bias).toNat
      (F * 2 ^ (52 - L) - 2 ^ IeeeFormat.binary64.fractionBits) < 2 ^ 64 := by
    apply f64_encode_lt
    · simp only [IeeeFormat.fractionBits, IeeeFormat.bias]; omega
    · simp only [IeeeFormat.fractionBits] at hS1 hS2 ⊢; simp only [Nat.reducePow, Nat.reduceAdd] at hS1 hS2 ⊢; omega
  refine ⟨roundRatioBits .tiesToEven .binary64 neg (powScale F 1 t).1 (powScale F 1 t).2,
    ?_, ?_, ?_, ?_⟩
  · rw [hcong, hn64]; exact hWlt
  · exact convertFloatBits_of_finite _ _ _ _ _ _ _ hdec32
  · rw [hcong, hd64, hdec32]
    exact ⟨rfl, hcross, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
  · rw [hcong, convertFloatBits_of_finite _ _ _ _ _ _ _ hd64, ← hcong .binary32]
    exact hsub32

theorem f32_rt_normal (neg : Bool) (E F : Nat) (hE255 : ¬ E = 255) (hE0 : ¬ E = 0) (hEl : E < 256)
    (hFl : F < 8388608) : F32RoundTrip (encodeBits .binary32 neg E F) := by
  have hdec := decodeBits_encodeBits .binary32 neg E F hEl hFl
  have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg E F) =
      .finite neg (powScale (2 ^ IeeeFormat.binary32.fractionBits + F) 1
          ((E : Int) - IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits)).1
        (powScale (2 ^ IeeeFormat.binary32.fractionBits + F) 1
          ((E : Int) - IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits)).2 := by
    rw [hdec]
    have h1 : ¬ (E = 2 ^ IeeeFormat.binary32.exponentBits - 1) := by
      simp only [IeeeFormat.exponentBits]; omega
    rw [if_neg' h1, if_neg' hE0]
  generalize hS : 2 ^ IeeeFormat.binary32.fractionBits + F = S at hdec32
  generalize ht : ((E : Int) - IeeeFormat.binary32.bias - IeeeFormat.binary32.fractionBits) = t at hdec32
  have hSv : S = 8388608 + F := by rw [← hS]; rfl
  have htv : t = (E : Int) - 150 := by rw [← ht]; simp [IeeeFormat.bias, IeeeFormat.fractionBits]; omega
  have hS1 : 2 ^ IeeeFormat.binary32.fractionBits ≤ S := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
  have hS2 : S < 2 ^ (IeeeFormat.binary32.fractionBits + 1) := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceAdd]; omega
  have hT1 : 2 ^ IeeeFormat.binary64.fractionBits ≤ S * 2 ^ 29 := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
  have hT2 : S * 2 ^ 29 < 2 ^ (IeeeFormat.binary64.fractionBits + 1) := by
    simp only [IeeeFormat.fractionBits, Nat.reducePow, Nat.reduceAdd]; omega
  have hcross := powScale_shift_cross S 29 t
  have hE1 : IeeeFormat.binary64.minExponent ≤ t - ((29 : Nat) : Int) + IeeeFormat.binary64.fractionBits := by
    simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hE2 : t - ((29 : Nat) : Int) + IeeeFormat.binary64.fractionBits ≤ IeeeFormat.binary64.maxExponent := by
    simp only [IeeeFormat.maxExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hF1 : IeeeFormat.binary32.minExponent ≤ t + IeeeFormat.binary32.fractionBits := by
    simp only [IeeeFormat.minExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hF2 : t + IeeeFormat.binary32.fractionBits ≤ IeeeFormat.binary32.maxExponent := by
    simp only [IeeeFormat.maxExponent, IeeeFormat.fractionBits, IeeeFormat.bias]; omega
  have hcong := fun f => roundRatioBits_congr .tiesToEven f neg
    (powScale S 1 t).1 (powScale S 1 t).2
    (powScale (S * 2 ^ 29) 1 (t - ((29 : Nat) : Int))).1
    (powScale (S * 2 ^ 29) 1 (t - ((29 : Nat) : Int))).2
    (powScale_snd_pos _ _) (powScale_snd_pos _ _) hcross.symm
  have hn64 := roundRatioBits_normal .tiesToEven .binary64 neg _ _ hT1 hT2 hE1 hE2
  have hd64 := decodeBits_roundRatio_normal .tiesToEven .binary64 neg _ _ hT1 hT2 hE1 hE2
  have hn32 := roundRatioBits_normal .tiesToEven .binary32 neg S t hS1 hS2 hF1 hF2
  have hWlt : encodeBits .binary64 neg
      (t - ((29 : Nat) : Int) + IeeeFormat.binary64.fractionBits + IeeeFormat.binary64.bias).toNat
      (S * 2 ^ 29 - 2 ^ IeeeFormat.binary64.fractionBits) < 2 ^ 64 := by
    apply f64_encode_lt
    · simp only [IeeeFormat.fractionBits, IeeeFormat.bias]; omega
    · simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
  refine ⟨roundRatioBits .tiesToEven .binary64 neg (powScale S 1 t).1 (powScale S 1 t).2,
    ?_, ?_, ?_, ?_⟩
  · rw [hcong, hn64]; exact hWlt
  · exact convertFloatBits_of_finite _ _ _ _ _ _ _ hdec32
  · rw [hcong, hd64, hdec32]
    exact ⟨rfl, hcross, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
  · rw [hcong, convertFloatBits_of_finite _ _ _ _ _ _ _ hd64, ← hcong .binary32, hn32]
    have hEeq : (t + IeeeFormat.binary32.fractionBits + IeeeFormat.binary32.bias).toNat = E := by
      simp only [IeeeFormat.fractionBits, IeeeFormat.bias]; omega
    have hFeq : S - 2 ^ IeeeFormat.binary32.fractionBits = F := by
      simp only [IeeeFormat.fractionBits, Nat.reducePow]; omega
    rw [hEeq, hFeq]


/-- Per-case witness for the `f32 → f64 → f32` round trip. -/
theorem f32_roundtrip_core (x : F32Bits) (hx : isNaNBits .binary32 x.toNat = false) :
    F32RoundTrip x.toNat := by
  have hxlt := x.isLt
  have henc := encodeBits_unpackBits .binary32 x.toNat hxlt
  have hEl := unpackBits_exponent_lt .binary32 x.toNat
  have hFl := unpackBits_fraction_lt .binary32 x.toNat
  generalize unpackBits .binary32 x.toNat = c at henc hEl hFl
  obtain ⟨neg, E, F⟩ := c
  simp only at henc hEl hFl
  rw [← henc] at hx ⊢
  simp only [IeeeFormat.exponentBits, IeeeFormat.fractionBits, Nat.reducePow] at hEl hFl
  by_cases hE255 : E = 255
  · subst hE255
    by_cases hF0 : F = 0
    · subst hF0; exact f32_rt_inf neg
    · have hdec32 : decodeBits .binary32 (encodeBits .binary32 neg 255 F) =
          .nan neg (Nat.beq ((F / 2 ^ 22) % 2) 1) F := by
        rw [decodeBits_encodeBits .binary32 neg 255 F (by decide) hFl]
        simp [hF0, IeeeFormat.exponentBits, IeeeFormat.fractionBits]
      rw [isNaNBits_of_nan _ _ _ _ _ hdec32] at hx
      exact Bool.noConfusion hx
  · by_cases hE0 : E = 0
    · subst hE0
      by_cases hF0 : F = 0
      · subst hF0; exact f32_rt_zero neg
      · exact f32_rt_subnormal neg F hF0 hFl
    · exact f32_rt_normal neg E F hE255 hE0 hEl hFl

/-- **`f32 → f64` exact rational preservation and `f64ToF32 (f32ToF64 x) = x`** for
every non-NaN `F32Bits`. -/
theorem f32ToF64_exact_and_roundtrip (x : F32Bits) (hx : isNaNBits .binary32 x.toNat = false) :
    (decodeBits .binary64 (f32ToF64 x).toNat).sameValue (decodeBits .binary32 x.toNat) ∧
    f64ToF32 (f32ToF64 x) = x := by
  obtain ⟨W, hW, hw, hsame, hn⟩ := f32_roundtrip_core x hx
  have hwide : (f32ToF64 x).toNat = W := by
    simp only [f32ToF64, evalFloatToFloatRoundTiesToEven, BitVec.toNat_ofNat, hw]
    exact Nat.mod_eq_of_lt hW
  refine ⟨by rw [hwide]; exact hsame, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [f64ToF32, evalFloatToFloatRoundTiesToEven, BitVec.toNat_ofNat, hwide, hn]
  exact Nat.mod_eq_of_lt x.isLt


theorem isQuietNaNBits_of_nan (f : IeeeFormat) (bits : Nat) (neg q : Bool) (p : Nat)
    (h : decodeBits f bits = .nan neg q p) : isQuietNaNBits f bits = q := by
  unfold isQuietNaNBits; rw [h]

/-- **Universal quiet-NaN guarantee**: every NaN input converts to a *quiet* NaN in
every direction (`f32 → f64`, `f64 → f32`, and same-format). -/
theorem convertFloatBits_nan_quiet (mode : RoundingMode) (src dst : IeeeFormat) (bits : Nat)
    (h : isNaNBits src bits = true) :
    isNaNBits dst (convertFloatBits mode src dst bits) = true ∧
      isQuietNaNBits dst (convertFloatBits mode src dst bits) = true := by
  have hFl := unpackBits_fraction_lt src bits
  have hdecNaN : ∃ neg q, decodeBits src bits = .nan neg q (unpackBits src bits).fraction := by
    unfold isNaNBits at h
    unfold decodeBits at h ⊢
    simp only at h ⊢
    by_cases hE : (unpackBits src bits).exponent = 2 ^ src.exponentBits - 1
    · by_cases hF : (unpackBits src bits).fraction = 0
      · rw [if_pos' hE, if_pos' hF] at h; simp at h
      · rw [if_pos' hE, if_neg' hF]
        exact ⟨_, _, rfl⟩
    · rw [if_neg' hE] at h
      by_cases hZ : (unpackBits src bits).exponent = 0
      · rw [if_pos' hZ] at h
        by_cases hF : (unpackBits src bits).fraction = 0
        · rw [if_pos' hF] at h; simp at h
        · rw [if_neg' hF] at h; simp at h
      · rw [if_neg' hZ] at h; simp at h
  obtain ⟨neg, q, hdec⟩ := hdecNaN
  generalize (unpackBits src bits).fraction = F at hFl hdec
  have hconv : convertFloatBits mode src dst bits =
      encodeBits dst neg (2 ^ dst.exponentBits - 1)
        (Nat.lor (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor F (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else Nat.lor F (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits))
          (2 ^ (dst.fractionBits - 1))) := by
    unfold convertFloatBits; rw [hdec]
  have hs1 := IeeeFormat.one_le_fb src
  have hd1 := IeeeFormat.one_le_fb dst
  have hq : Nat.lor F (2 ^ (src.fractionBits - 1)) < 2 ^ src.fractionBits :=
    Nat.or_lt_two_pow hFl (two_pow_lt_two_pow (by omega))
  have hp : (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor F (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else Nat.lor F (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits)) <
        2 ^ dst.fractionBits := by
    split
    · rename_i hle
      have := Nat.mul_lt_mul_of_pos_right hq (Nat.two_pow_pos (dst.fractionBits - src.fractionBits))
      rwa [pow_mul_pow, Nat.add_sub_cancel' hle] at this
    · rename_i hle
      apply nat_div_lt_of_lt_mul
      rw [pow_mul_pow, show src.fractionBits - dst.fractionBits + dst.fractionBits = src.fractionBits by omega]
      exact hq
  generalize (if src.fractionBits ≤ dst.fractionBits then
            Nat.lor F (2 ^ (src.fractionBits - 1)) * 2 ^ (dst.fractionBits - src.fractionBits)
          else Nat.lor F (2 ^ (src.fractionBits - 1)) / 2 ^ (src.fractionBits - dst.fractionBits)) = p
    at hp hconv
  have hP : Nat.lor p (2 ^ (dst.fractionBits - 1)) < 2 ^ dst.fractionBits :=
    Nat.or_lt_two_pow hp (two_pow_lt_two_pow (by omega))
  have hbit : (Nat.lor p (2 ^ (dst.fractionBits - 1))).testBit (dst.fractionBits - 1) = true := by
    show (p ||| 2 ^ (dst.fractionBits - 1)).testBit (dst.fractionBits - 1) = true
    rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
  have hP0 : Nat.lor p (2 ^ (dst.fractionBits - 1)) ≠ 0 := by
    intro h0; rw [h0] at hbit; simp at hbit
  have hqbit : Nat.beq ((Nat.lor p (2 ^ (dst.fractionBits - 1)) / 2 ^ (dst.fractionBits - 1)) % 2) 1 = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
    have := of_decide_eq_true hbit
    rw [this]; rfl
  have hE : 2 ^ dst.exponentBits - 1 < 2 ^ dst.exponentBits := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hdec' := decodeBits_encodeBits dst neg (2 ^ dst.exponentBits - 1) _ hE hP
  rw [if_pos' rfl, if_neg' hP0] at hdec'
  rw [hconv]
  exact ⟨isNaNBits_of_nan _ _ _ _ _ hdec', by rw [isQuietNaNBits_of_nan _ _ _ _ _ hdec']; exact hqbit⟩

/-! ### Float-level ½-ULP & unreachability of `inconsistentRounding` in `roundRatioBits` -/

theorem powScale_snd_pos_gen (n d : Nat) (hd : 0 < d) (t : Int) : 0 < (powScale n d t).2 := by
  cases t with
  | ofNat _ => exact hd
  | negSucc k => exact Nat.mul_pos hd (Nat.two_pow_pos (k + 1))

theorem powScale_diff_cross (n d : Nat) (a b : Int) (hab : a ≤ b) :
    (powScale n d a).1 * (powScale n d b).2 * 2 ^ (b - a).toNat =
      (powScale n d b).1 * (powScale n d a).2 := by
  have key : ∀ (u : Int), powScale n d u =
      if 0 ≤ u then (n * 2 ^ u.toNat, d) else (n, d * 2 ^ (-u).toNat) := by
    intro u
    cases u with
    | ofNat k => simp [powScale]
    | negSucc k =>
      simp only [powScale]
      have : ¬ (0 ≤ Int.negSucc k) := by omega
      rw [if_neg' this]
      simp [Int.neg_negSucc]
  rw [key a, key b]
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := by omega
    rw [if_pos' ha, if_pos' hb]
    simp only [Nat.mul_right_comm _ d, Nat.mul_assoc, pow_mul_pow]
    congr 3; omega
  · by_cases hb : 0 ≤ b
    · rw [if_neg' ha, if_pos' hb]
      simp only
      rw [← Nat.mul_assoc (n * 2 ^ b.toNat), Nat.mul_right_comm n (2 ^ b.toNat) d,
        Nat.mul_assoc (n * d), pow_mul_pow]
      congr 2; omega
    · rw [if_neg' ha, if_neg' hb]
      simp only [Nat.mul_assoc, pow_mul_pow]
      congr 3; omega

theorem powScale_neg_ratioExponent_bounds (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    (powScale n d (- ratioExponent n d)).2 ≤ (powScale n d (- ratioExponent n d)).1 ∧
    (powScale n d (- ratioExponent n d)).1 < 2 * (powScale n d (- ratioExponent n d)).2 := by
  unfold ratioExponent
  by_cases hdn : d ≤ n
  · rw [if_pos' hdn]
    have hq : n / d ≠ 0 := by
      have : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
      omega
    have hL1 : d * 2 ^ (n / d).log2 ≤ n := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp (Nat.log2_self_le hq)
    have hL2 : n < 2 * (d * 2 ^ (n / d).log2) := by
      have := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_log2_self (n := n / d))
      rw [Nat.pow_succ, Nat.mul_right_comm (2 ^ (n / d).log2) 2 d, Nat.mul_comm _ 2,
        Nat.mul_comm (2 ^ (n / d).log2) d] at this
      exact this
    cases hL : (n / d).log2 with
    | zero =>
      rw [hL] at hL1 hL2
      simp only [Int.natCast_zero, Int.neg_zero, powScale, Nat.pow_zero, Nat.mul_one] at hL1 hL2 ⊢
      exact ⟨hL1, hL2⟩
    | succ m =>
      rw [hL] at hL1 hL2
      have hneg : -(((m + 1 : Nat) : Int)) = Int.negSucc m := rfl
      rw [hneg]
      simp only [powScale]
      exact ⟨hL1, hL2⟩
  · rw [if_neg' hdn]
    have hq : d / n ≠ 0 := by
      have : 1 ≤ d / n := (Nat.le_div_iff_mul_le hn).mpr (by omega)
      omega
    have hk1 : n * 2 ^ (d / n).log2 ≤ d := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hn).mp (Nat.log2_self_le hq)
    have hk2 : d < n * 2 ^ ((d / n).log2 + 1) := by
      rw [Nat.mul_comm]
      exact (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_log2_self (n := d / n))
    generalize (d / n).log2 = k at hk1 hk2
    by_cases hle : d ≤ n * 2 ^ k
    · rw [if_pos' hle, Int.neg_neg]
      have hof : ((k : Nat) : Int) = Int.ofNat k := rfl
      rw [hof]
      simp only [powScale]
      exact ⟨hle, by omega⟩
    · rw [if_neg' hle]
      have hneg : -(-((k : Int) + 1)) = ((k + 1 : Nat) : Int) := by omega
      rw [hneg]
      have hof : ((k + 1 : Nat) : Int) = Int.ofNat (k + 1) := rfl
      rw [hof]
      simp only [powScale]
      have hlt : n * 2 ^ (k + 1) < 2 * d := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨Nat.le_of_lt hk2, hlt⟩

theorem scale_lo_helper {A1 A2 B1 B2 F : Nat} (hd : 0 < A2) (hb1 : A2 ≤ A1)
    (hc : A1 * B2 * F = B1 * A2) : F * B2 ≤ B1 := by
  apply (Nat.mul_le_mul_right_iff hd).mp
  have h1 : A2 * (F * B2) ≤ A1 * (F * B2) := Nat.mul_le_mul_right (F * B2) hb1
  have h2 : A2 * (F * B2) = F * B2 * A2 := Nat.mul_comm _ _
  have h3 : A1 * (F * B2) = A1 * B2 * F := by
    rw [Nat.mul_comm F B2, ← Nat.mul_assoc]
  omega

theorem scale_hi_helper {A1 A2 B1 B2 F : Nat} (hd : 0 < A2) (hb2 : A1 < 2 * A2)
    (hdse : 0 < B2) (hc : A1 * B2 * F = B1 * A2) (hF : 0 < F) : B1 < F * 2 * B2 := by
  apply (nat_mul_lt_mul_right_iff hd).mp
  have h1 : A1 * B2 * F < 2 * A2 * B2 * F :=
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hb2 hdse) hF
  have h2 : 2 * A2 * B2 * F = F * 2 * B2 * A2 := by
    rw [Nat.mul_right_comm (2 * A2) B2 F, Nat.mul_right_comm 2 A2 F,
      Nat.mul_right_comm (2 * F) A2 B2, Nat.mul_comm 2 F]
  omega

theorem scale_sub_helper {S1 S2 B1 B2 F P : Nat} (hdse : 0 < B2) (hP : 2 ≤ P)
    (hc : S1 * B2 * P = B1 * S2) (hhi : B1 < F * 2 * B2) (hS2 : 0 < S2) : S1 < F * S2 := by
  apply (nat_mul_lt_mul_right_iff hdse).mp
  have h1 : S1 * B2 * 2 ≤ S1 * B2 * P := Nat.mul_le_mul_left (S1 * B2) hP
  have h2 : B1 * S2 < F * 2 * B2 * S2 := Nat.mul_lt_mul_of_pos_right hhi hS2
  have h3 : F * 2 * B2 * S2 = F * S2 * B2 * 2 := by
    rw [Nat.mul_right_comm (F * 2) B2 S2, Nat.mul_right_comm F 2 S2,
      Nat.mul_assoc (F * S2) 2 B2, Nat.mul_comm 2 B2, ← Nat.mul_assoc]
  have h4 : S1 * B2 * 2 < F * S2 * B2 * 2 := by omega
  exact (nat_mul_lt_mul_right_iff (by decide : 0 < 2)).mp h4

theorem powScale_roundRatio_scaled_bounds (f : IeeeFormat) (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    let e := ratioExponent n d
    let exponent := max e f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    scaled.1 < 2 ^ (f.fractionBits + 1) * scaled.2 ∧
      (f.minExponent ≤ e → 2 ^ f.fractionBits * scaled.2 ≤ scaled.1) ∧
      (e < f.minExponent → scaled.1 < 2 ^ f.fractionBits * scaled.2) := by
  intro e exponent scaled
  obtain ⟨hb1, hb2⟩ := powScale_neg_ratioExponent_bounds n d hn hd
  have hde : 0 < (powScale n d (-e)).2 := powScale_snd_pos_gen n d hd (-e)
  have hdse : 0 < (powScale n d ((f.fractionBits : Int) - e)).2 :=
    powScale_snd_pos_gen n d hd ((f.fractionBits : Int) - e)
  have hcross1 := powScale_diff_cross n d (-e) ((f.fractionBits : Int) - e) (by omega)
  have hto1 : (((f.fractionBits : Int) - e) - (-e)).toNat = f.fractionBits := by omega
  rw [hto1] at hcross1
  have hse_lo : 2 ^ f.fractionBits * (powScale n d ((f.fractionBits : Int) - e)).2 ≤
      (powScale n d ((f.fractionBits : Int) - e)).1 :=
    scale_lo_helper hde hb1 hcross1
  have hse_hi : (powScale n d ((f.fractionBits : Int) - e)).1 <
      2 ^ (f.fractionBits + 1) * (powScale n d ((f.fractionBits : Int) - e)).2 := by
    rw [Nat.pow_succ]
    exact scale_hi_helper hde hb2 hdse hcross1 (Nat.two_pow_pos _)
  by_cases hme : f.minExponent ≤ e
  · have hexp : exponent = e := by simp only [exponent]; omega
    have hsc : scaled = powScale n d ((f.fractionBits : Int) - e) := by
      simp only [scaled, hexp]
    refine ⟨by rw [hsc]; exact hse_hi, fun _ => by rw [hsc]; exact hse_lo, fun hlt => by omega⟩
  · have hexp : exponent = f.minExponent := by simp only [exponent]; omega
    have hcross2 := powScale_diff_cross n d ((f.fractionBits : Int) - exponent)
      ((f.fractionBits : Int) - e) (by omega)
    have hge1 : 1 ≤ (((f.fractionBits : Int) - e) - ((f.fractionBits : Int) - exponent)).toNat := by
      omega
    have hpow2 : 2 ≤ 2 ^ (((f.fractionBits : Int) - e) - ((f.fractionBits : Int) - exponent)).toNat :=
      two_pow_le_two_pow hge1
    have hse_hi' : (powScale n d ((f.fractionBits : Int) - e)).1 <
        2 ^ f.fractionBits * 2 * (powScale n d ((f.fractionBits : Int) - e)).2 := by
      rwa [Nat.pow_succ] at hse_hi
    have hlt_fb : scaled.1 < 2 ^ f.fractionBits * scaled.2 :=
      scale_sub_helper hdse hpow2 hcross2 hse_hi' (powScale_snd_pos_gen n d hd _)
    have hlt_fb1 : scaled.1 < 2 ^ (f.fractionBits + 1) * scaled.2 := by
      have : 2 ^ (f.fractionBits + 1) * scaled.2 =
          2 ^ f.fractionBits * scaled.2 + 2 ^ f.fractionBits * scaled.2 := by
        rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_two]
      omega
    exact ⟨hlt_fb1, fun hge => by omega, fun _ => hlt_fb⟩

theorem roundQuotient_bounds (mode : RoundingMode) (a b : Nat) :
    a / b ≤ roundQuotient mode a b ∧ roundQuotient mode a b ≤ a / b + 1 := by
  cases mode <;> simp only [roundQuotient, roundQuotientTiesToEven, roundQuotientHalfAwayFromZero] <;>
    split <;> first | exact ⟨Nat.le_succ _, Nat.le_refl _⟩ | exact ⟨Nat.le_refl _, Nat.le_succ _⟩

theorem roundQuotient_le_of_lt_mul (mode : RoundingMode) (a b M : Nat) (_hb : 0 < b)
    (h : a < M * b) : roundQuotient mode a b ≤ M := by
  have hdiv : a / b < M := nat_div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  have := (roundQuotient_bounds mode a b).2
  omega

theorem roundQuotient_ge_of_mul_le (mode : RoundingMode) (a b M : Nat) (hb : 0 < b)
    (h : M * b ≤ a) : M ≤ roundQuotient mode a b := by
  have hdiv : M ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr h
  have := (roundQuotient_bounds mode a b).1
  omega

theorem int_le_max_right (a b : Int) : b ≤ max a b := by omega

theorem int_max_eq_right {a b : Int} (h : ¬ b ≤ a) : max a b = b := by omega

/-- **Unreachability of `inconsistentRounding` (`preferredNaNBits`) in `roundRatioBits`**:
for every rounding mode, format `f`, sign `neg`, numerator `n`, and positive denominator
`0 < d`, `roundRatioBits mode f neg n d` is an in-width bit pattern (`< 2 ^ f.width`) that
never decodes to NaN (`isNaNBits = false`). -/
theorem roundRatioBits_valid_and_not_nan (mode : RoundingMode) (f : IeeeFormat) (neg : Bool)
    (n d : Nat) (hd : 0 < d) :
    roundRatioBits mode f neg n d < 2 ^ f.width ∧
      isNaNBits f (roundRatioBits mode f neg n d) = false := by
  have hd0 : d ≠ 0 := by omega
  have hmaxE := IeeeFormat.two_bias_lt f
  have hnez := IeeeFormat.max_exp_ne_zero f
  by_cases hn0 : n = 0
  · subst hn0
    have hz : roundRatioBits mode f neg 0 d = encodeBits f neg 0 0 := by
      simp [roundRatioBits, hd0, zeroBits, encodeBits]
    rw [hz]
    refine ⟨encodeBits_lt f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _), ?_⟩
    unfold isNaNBits
    rw [decodeBits_encodeBits f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
      if_neg' hnez, if_pos' rfl, if_pos' rfl]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨hhi, hlo_ge, hlt_sub⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
    clear hlt_sub
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hhi hlo_ge
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hhi hlo_ge
    have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
    have hsig_le : roundQuotient mode scaled.1 scaled.2 ≤ 2 ^ (f.fractionBits + 1) :=
      roundQuotient_le_of_lt_mul mode scaled.1 scaled.2 _ hds hhi
    unfold roundRatioBits
    simp only [hd0, hn0, ↓reduceIte, hexp, hsc]
    have hinf_lt : infBits f neg < 2 ^ f.width := by
      simp only [infBits]
      have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
        Nat.sub_lt (Nat.two_pow_pos _) (by decide)
      exact encodeBits_lt f neg _ 0 hE (Nat.two_pow_pos _)
    have hinf_nan : isNaNBits f (infBits f neg) = false := by
      simp only [infBits, isNaNBits]
      have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
        Nat.sub_lt (Nat.two_pow_pos _) (by decide)
      rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]
    by_cases hov1 : exponent > f.maxExponent
    · rw [if_pos' hov1]; exact ⟨hinf_lt, hinf_nan⟩
    · rw [if_neg' hov1]
      generalize hsig : roundQuotient mode scaled.1 scaled.2 = sig at hsig_le
      have hmin_le : f.minExponent ≤ exponent := by
        rw [← hexp]; exact int_le_max_right _ _
      by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
      · clear hlo_ge hexp hsc hsig
        have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by omega
        have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by
          rw [hsig_eq, Nat.pow_succ]; omega
        simp only [hcarry, decide_true, ↓reduceIte, hdiv2]
        by_cases hov2 : exponent + 1 > f.maxExponent
        · rw [if_pos' hov2]; exact ⟨hinf_lt, hinf_nan⟩
        · rw [if_neg' hov2]
          have hlt_false : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
          have hge_false : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
            have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); omega
          rw [if_neg' hlt_false, if_neg' hge_false, Nat.sub_self]
          simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2
          have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
          have hEne : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
          have hE0 : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 0) := by omega
          refine ⟨encodeBits_lt f neg _ 0 hE (Nat.two_pow_pos _), ?_⟩
          unfold isNaNBits
          rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_neg' hEne, if_neg' hE0]
      · simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hov1]
        by_cases hsub : sig < 2 ^ f.fractionBits
        · rw [if_pos' hsub]
          have hexp_min : exponent = f.minExponent := by
            by_cases hge : f.minExponent ≤ ratioExponent n d
            · have hge_sig : 2 ^ f.fractionBits ≤ sig := by
                rw [← hsig]
                exact roundQuotient_ge_of_mul_le mode scaled.1 scaled.2 _ hds (hlo_ge hge)
              clear hlo_ge hexp hsc hsig; omega
            · rw [← hexp]; exact int_max_eq_right hge
          rw [if_pos' hexp_min]
          refine ⟨encodeBits_lt f neg 0 sig (Nat.two_pow_pos _) hsub, ?_⟩
          unfold isNaNBits
          rw [decodeBits_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub, if_neg' hnez, if_pos' rfl]
          by_cases hsig0 : sig = 0 <;> simp [hsig0]
        · clear hlo_ge hexp hsc hsig
          rw [if_neg' hsub]
          simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov1
          have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
          have hEne : ¬ ((exponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
          have hE0 : ¬ ((exponent + (f.bias : Int)).toNat = 0) := by omega
          have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
            have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
              rw [Nat.pow_succ]; omega
            omega
          refine ⟨encodeBits_lt f neg _ _ hE hF, ?_⟩
          unfold isNaNBits
          rw [decodeBits_encodeBits f neg _ _ hE hF, if_neg' hEne, if_neg' hE0]

/-- **Float-level `<= 0.5 ULP` + even-tie theorem for `roundRatioTiesToEven`**:
for every format `f`, sign `neg`, and positive rational `n / d` (`0 < n`, `0 < d`), let
`exponent := max (ratioExponent n d) f.minExponent`,
`scaled := powScale n d ((f.fractionBits : Int) - exponent)` (so `scaled.1 / scaled.2 =
(n / d) / 2 ^ (exponent - f.fractionBits)`), and
`sig := roundQuotientTiesToEven scaled.1 scaled.2`.
Then:
1. `sig` is within `0.5` ULP of `n / d` at quantum `2 ^ (exponent - f.fractionBits)`:
   `2 * |sig * scaled.2 - scaled.1| ≤ scaled.2`, with `sig % 2 = 0` on ties;
2. Whenever `roundRatioTiesToEven f neg n d` does not overflow to `.inf neg`, the decoded
   float `decodeBits f (roundRatioTiesToEven f neg n d)` has the exact rational value
   `(-1)^neg * sig * 2 ^ (exponent - f.fractionBits)` (across normal, subnormal,
   gradual-underflow-to-zero, and carry-out-to-`exponent + 1` regimes). -/
theorem roundRatioTiesToEven_float_half_ulp (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d) :
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
      (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
        sig % 2 = 0) ∧
      (decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg →
        (decodeBits f (roundRatioTiesToEven f neg n d)).sameValue
          (if sig = 0 then .zero neg
           else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
             (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  dsimp only
  have hd0 : d ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hmaxE := IeeeFormat.two_bias_lt f
  have hnez := IeeeFormat.max_exp_ne_zero f
  obtain ⟨hhi, hlo_ge, hlt_sub⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
  clear hlt_sub
  generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hhi hlo_ge
  generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hhi hlo_ge
  have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
  have hsig_le : roundQuotient .tiesToEven scaled.1 scaled.2 ≤ 2 ^ (f.fractionBits + 1) :=
    roundQuotient_le_of_lt_mul .tiesToEven scaled.1 scaled.2 _ hds hhi
  simp only [roundQuotient] at hsig_le
  refine ⟨roundQuotientTiesToEven_half_ulp scaled.1 scaled.2 hds,
    roundQuotientTiesToEven_tie_even scaled.1 scaled.2 hds, ?_⟩
  intro hno_inf
  have hinf_dec : decodeBits f (infBits f neg) = .inf neg := by
    simp only [infBits]
    have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
      Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]
  unfold roundRatioTiesToEven roundRatioBits at hno_inf ⊢
  simp only [hd0, hn0, ↓reduceIte, hexp, hsc, roundQuotient] at hno_inf ⊢
  by_cases hov1 : exponent > f.maxExponent
  · rw [if_pos' hov1, hinf_dec] at hno_inf; exact absurd rfl hno_inf
  · rw [if_neg' hov1] at hno_inf ⊢
    generalize hsig : roundQuotientTiesToEven scaled.1 scaled.2 = sig at hsig_le hno_inf ⊢
    have hmin_le : f.minExponent ≤ exponent := by
      rw [← hexp]; exact int_le_max_right _ _
    by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
    · clear hlo_ge hexp hsc hsig
      have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by clear hno_inf; omega
      have hsig_nz : sig ≠ 0 := by have := Nat.two_pow_pos (f.fractionBits + 1); clear hno_inf; omega
      have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by rw [hsig_eq, Nat.pow_succ]; clear hno_inf; omega
      simp only [hcarry, decide_true, ↓reduceIte, hdiv2] at hno_inf ⊢
      by_cases hov2 : exponent + 1 > f.maxExponent
      · rw [if_pos' hov2, hinf_dec] at hno_inf; exact absurd rfl hno_inf
      · clear hno_inf
        rw [if_neg' hov2]
        have hlt_false : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
        have hge_false : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
          have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); omega
        rw [if_neg' hlt_false, if_neg' hge_false, Nat.sub_self, if_neg' hsig_nz]
        simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2
        have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
        have hEne : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
        have hE0 : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 0) := by omega
        rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_neg' hEne, if_neg' hE0,
          Nat.add_zero]
        have ht : (((exponent + 1 + (f.bias : Int)).toNat : Nat) : Int) - f.bias - f.fractionBits =
            exponent + 1 - f.fractionBits := by omega
        rw [ht]
        have hcross := powScale_shift_cross (2 ^ f.fractionBits) 1 (exponent + 1 - f.fractionBits)
        have hmul : 2 ^ f.fractionBits * 2 ^ 1 = sig := by rw [hsig_eq, Nat.pow_succ]; rfl
        have hsub : exponent + 1 - (f.fractionBits : Int) - ((1 : Nat) : Int) =
            exponent - f.fractionBits := by omega
        rw [hmul, hsub] at hcross
        exact ⟨rfl, hcross.symm, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
    · clear hno_inf
      simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hov1]
      by_cases hsub : sig < 2 ^ f.fractionBits
      · rw [if_pos' hsub]
        have hexp_min : exponent = f.minExponent := by
          by_cases hge : f.minExponent ≤ ratioExponent n d
          · have hge_sig : 2 ^ f.fractionBits ≤ sig := by
              rw [← hsig]
              exact roundQuotient_ge_of_mul_le .tiesToEven scaled.1 scaled.2 _ hds (hlo_ge hge)
            clear hlo_ge hexp hsc hsig; omega
          · rw [← hexp]; exact int_max_eq_right hge
        rw [if_pos' hexp_min, decodeBits_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub,
          if_neg' hnez, if_pos' rfl]
        by_cases hsig0 : sig = 0
        · rw [if_pos' hsig0, if_pos' hsig0]; rfl
        · rw [if_neg' hsig0, if_neg' hsig0, hexp_min]
          exact ⟨rfl, rfl, powScale_snd_pos _ _, powScale_snd_pos _ _⟩
      · clear hlo_ge hexp hsc hsig
        rw [if_neg' hsub]
        have hsig_ge : 2 ^ f.fractionBits ≤ sig := Nat.le_of_not_lt hsub
        have hsig_nz : sig ≠ 0 := by have := Nat.two_pow_pos f.fractionBits; omega
        rw [if_neg' hsig_nz]
        simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov1
        have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by omega
        have hEne : ¬ ((exponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by omega
        have hE0 : ¬ ((exponent + (f.bias : Int)).toNat = 0) := by omega
        have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
          have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
            rw [Nat.pow_succ]; omega
          omega
        rw [decodeBits_encodeBits f neg _ _ hE hF, if_neg' hEne, if_neg' hE0,
          Nat.add_sub_cancel' hsig_ge]
        have ht : (((exponent + (f.bias : Int)).toNat : Nat) : Int) - f.bias - f.fractionBits =
            exponent - f.fractionBits := by omega
        rw [ht]
        exact ⟨rfl, rfl, powScale_snd_pos _ _, powScale_snd_pos _ _⟩

/-- **Correct rounding of `roundRatioTiesToEven`** (strengthens
`roundRatioTiesToEven_float_half_ulp` by pinning the rounding quantum to the IEEE-754 ULP):
for `0 < n`, `0 < d`, with `e := ratioExponent n d`, `exponent := max e minExponent`,
`scaled := powScale n d (fb - exponent)` (`scaled.1 / scaled.2 = (n/d) / 2^(exponent - fb)`)
and `sig := roundQuotientTiesToEven scaled.1 scaled.2`:
1. `e = ⌊log2 (n/d)⌋`, i.e. `1 ≤ (n/d) / 2^e < 2`;
2. the quantum `2^(exponent - fb)` is the ULP of the binade of `n/d`:
   `scaled < 2^(fb+1)`, and `2^fb ≤ scaled` whenever `n/d` is in the normal range
   (`minExponent ≤ e`; otherwise `exponent = minExponent` is the subnormal quantum);
3. `sig` is within `½` of `scaled`, resolving exact ties to an even significand;
4. unless the result overflows to `±∞`, it decodes to exactly
   `(-1)^neg * sig * 2^(exponent - fb)`. -/
theorem roundRatioTiesToEven_correctly_rounded (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d) :
    let e := ratioExponent n d
    let exponent := max e f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    ((powScale n d (-e)).2 ≤ (powScale n d (-e)).1 ∧
      (powScale n d (-e)).1 < 2 * (powScale n d (-e)).2) ∧
    scaled.1 < 2 ^ (f.fractionBits + 1) * scaled.2 ∧
    (f.minExponent ≤ e → 2 ^ f.fractionBits * scaled.2 ≤ scaled.1) ∧
    2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
    (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 → sig % 2 = 0) ∧
    (decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg →
      (decodeBits f (roundRatioTiesToEven f neg n d)).sameValue
        (if sig = 0 then .zero neg
         else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
           (powScale sig 1 (exponent - f.fractionBits)).2)) := by
  intro e exponent scaled sig
  have hb := powScale_roundRatio_scaled_bounds f n d hn hd
  have hh := roundRatioTiesToEven_float_half_ulp f neg n d hn hd
  exact ⟨powScale_neg_ratioExponent_bounds n d hn hd, hb.1, hb.2.1, hh.1, hh.2.1, hh.2.2⟩

/-- **Overflow to `±∞`** (sufficiency): `roundRatioTiesToEven` returns `±∞` when the exact
value's binade exceeds `maxExponent`, or when it lies in the top binade and rounds up to
`2^(fb+1) * 2^(maxExponent - fb) = 2^(maxExponent + 1)` (carry-out past the largest
finite value, e.g. the `binary32` tie `2^128 - 2^103`). -/
theorem roundRatioTiesToEven_overflow_of (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d)
    (h : f.maxExponent < max (ratioExponent n d) f.minExponent ∨
      (max (ratioExponent n d) f.minExponent = f.maxExponent ∧
        roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1))) :
    roundRatioTiesToEven f neg n d = infBits f neg := by
  have hd0 : d ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  unfold roundRatioTiesToEven roundRatioBits
  simp only [hd0, hn0, ↓reduceIte, roundQuotient]
  generalize hexp : max (ratioExponent n d) f.minExponent = exponent at h ⊢
  generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at h ⊢
  rcases h with h | ⟨he, hs⟩
  · rw [if_pos' h]
  · have hnot : ¬ (exponent > f.maxExponent) := by omega
    have hov : exponent + 1 > f.maxExponent := by omega
    rw [if_neg' hnot]
    simp only [hs, Nat.le_refl, decide_true, ↓reduceIte, if_pos' hov]

theorem decodeBits_zeroBits (f : IeeeFormat) (neg : Bool) :
    decodeBits f (zeroBits f neg) = .zero neg := by
  rw [zeroBits_eq_encodeBits,
    decodeBits_encodeBits f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _),
    if_neg' (IeeeFormat.max_exp_ne_zero f), if_pos' rfl, if_pos' rfl]

theorem decodeBits_infBits (f : IeeeFormat) (neg : Bool) :
    decodeBits f (infBits f neg) = .inf neg := by
  simp only [infBits]
  have hE : 2 ^ f.exponentBits - 1 < 2 ^ f.exponentBits :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_pos' rfl, if_pos' rfl]

/-- **Necessary and sufficient (`↔`) overflow characterization for `roundRatioTiesToEven`**
(strengthens `roundRatioTiesToEven_overflow_of` to a full biconditional): for `0 < n` and
`0 < d`, `roundRatioTiesToEven f neg n d` equals `infBits f neg` (and equivalently decodes
to `.inf neg`) **if and only if** the clamped binade `exponent := max (ratioExponent n d)
f.minExponent` exceeds `f.maxExponent`, or `exponent = f.maxExponent` and the rounded
significand carries out to `2 ^ (f.fractionBits + 1)`. -/
theorem roundRatioTiesToEven_overflow_iff (f : IeeeFormat) (neg : Bool) (n d : Nat)
    (hn : 0 < n) (hd : 0 < d) :
    let exponent := max (ratioExponent n d) f.minExponent
    let scaled := powScale n d ((f.fractionBits : Int) - exponent)
    let sig := roundQuotientTiesToEven scaled.1 scaled.2
    (roundRatioTiesToEven f neg n d = infBits f neg ↔
      (f.maxExponent < exponent ∨ (exponent = f.maxExponent ∧ sig = 2 ^ (f.fractionBits + 1)))) ∧
    (decodeBits f (roundRatioTiesToEven f neg n d) = .inf neg ↔
      roundRatioTiesToEven f neg n d = infBits f neg) := by
  dsimp only
  have hnot_inf_of_not_ov :
      ¬ (f.maxExponent < max (ratioExponent n d) f.minExponent) →
      ¬ (max (ratioExponent n d) f.minExponent = f.maxExponent ∧
          roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1)) →
      decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg := by
    intro hno1 hno2 hdec
    have hd0 : d ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hmaxE := IeeeFormat.two_bias_lt f
    have hnez := IeeeFormat.max_exp_ne_zero f
    obtain ⟨hhi, hlo_ge, hlt_sub⟩ := powScale_roundRatio_scaled_bounds f n d hn hd
    clear hlt_sub
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hhi hlo_ge hno1 hno2
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hhi hlo_ge hno2
    have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
    have hsig_le : roundQuotient .tiesToEven scaled.1 scaled.2 ≤ 2 ^ (f.fractionBits + 1) :=
      roundQuotient_le_of_lt_mul .tiesToEven scaled.1 scaled.2 _ hds hhi
    simp only [roundQuotient] at hsig_le
    unfold roundRatioTiesToEven roundRatioBits at hdec
    simp only [hd0, hn0, ↓reduceIte, hexp, hsc, roundQuotient] at hdec
    rw [if_neg' hno1] at hdec
    generalize hsig : roundQuotientTiesToEven scaled.1 scaled.2 = sig at hsig_le hno2 hdec
    have hmin_le : f.minExponent ≤ exponent := by
      rw [← hexp]; exact int_le_max_right _ _
    by_cases hcarry : 2 ^ (f.fractionBits + 1) ≤ sig
    · clear hlo_ge hexp hsc hsig
      have hsig_eq : sig = 2 ^ (f.fractionBits + 1) := by clear hno2 hdec; omega
      have hexp_ne : exponent ≠ f.maxExponent := fun he => hno2 ⟨he, hsig_eq⟩
      clear hno2
      have hov2 : ¬ (exponent + 1 > f.maxExponent) := by clear hdec; omega
      have hdiv2 : sig / 2 = 2 ^ f.fractionBits := by rw [hsig_eq, Nat.pow_succ]; clear hdec; omega
      simp only [hcarry, decide_true, ↓reduceIte, hdiv2] at hdec
      rw [if_neg' hov2] at hdec
      have hlt_false : ¬ (2 ^ f.fractionBits < 2 ^ f.fractionBits) := Nat.lt_irrefl _
      have hge_false : ¬ (2 ^ (f.fractionBits + 1) ≤ 2 ^ f.fractionBits) := by
        have := two_pow_lt_two_pow (Nat.lt_succ_self f.fractionBits); clear hdec; omega
      rw [if_neg' hlt_false, if_neg' hge_false, Nat.sub_self] at hdec
      simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hov2
      have hE : (exponent + 1 + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by clear hdec; omega
      have hEne : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by clear hdec; omega
      have hE0 : ¬ ((exponent + 1 + (f.bias : Int)).toNat = 0) := by clear hdec; omega
      rw [decodeBits_encodeBits f neg _ 0 hE (Nat.two_pow_pos _), if_neg' hEne, if_neg' hE0] at hdec
      cases hdec
    · clear hno2
      simp only [hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hno1] at hdec
      by_cases hsub : sig < 2 ^ f.fractionBits
      · rw [if_pos' hsub] at hdec
        have hexp_min : exponent = f.minExponent := by
          by_cases hge : f.minExponent ≤ ratioExponent n d
          · have hge_sig : 2 ^ f.fractionBits ≤ sig := by
              rw [← hsig]
              exact roundQuotient_ge_of_mul_le .tiesToEven scaled.1 scaled.2 _ hds (hlo_ge hge)
            clear hlo_ge hexp hsc hsig hdec; omega
          · rw [← hexp]; exact int_max_eq_right hge
        rw [if_pos' hexp_min, decodeBits_encodeBits f neg 0 sig (Nat.two_pow_pos _) hsub,
          if_neg' hnez, if_pos' rfl] at hdec
        by_cases hsig0 : sig = 0 <;> simp [hsig0] at hdec
      · clear hlo_ge hexp hsc hsig
        rw [if_neg' hsub] at hdec
        simp only [IeeeFormat.minExponent, IeeeFormat.maxExponent] at hmin_le hno1
        have hE : (exponent + (f.bias : Int)).toNat < 2 ^ f.exponentBits := by clear hdec; omega
        have hEne : ¬ ((exponent + (f.bias : Int)).toNat = 2 ^ f.exponentBits - 1) := by clear hdec; omega
        have hE0 : ¬ ((exponent + (f.bias : Int)).toNat = 0) := by clear hdec; omega
        have hF : sig - 2 ^ f.fractionBits < 2 ^ f.fractionBits := by
          have : 2 ^ (f.fractionBits + 1) = 2 * 2 ^ f.fractionBits := by
            rw [Nat.pow_succ]; clear hdec; omega
          clear hdec; omega
        rw [decodeBits_encodeBits f neg _ _ hE hF, if_neg' hEne, if_neg' hE0] at hdec
        cases hdec
  have hiff1 : roundRatioTiesToEven f neg n d = infBits f neg ↔
      (f.maxExponent < max (ratioExponent n d) f.minExponent ∨
        (max (ratioExponent n d) f.minExponent = f.maxExponent ∧
          roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1))) := by
    constructor
    · intro heq
      have hdec : decodeBits f (roundRatioTiesToEven f neg n d) = .inf neg := by
        rw [heq, decodeBits_infBits]
      by_cases hov1 : f.maxExponent < max (ratioExponent n d) f.minExponent
      · exact Or.inl hov1
      · by_cases hov2 : max (ratioExponent n d) f.minExponent = f.maxExponent ∧
            roundQuotientTiesToEven
              (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
              (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
            2 ^ (f.fractionBits + 1)
        · exact Or.inr hov2
        · exact absurd hdec (hnot_inf_of_not_ov hov1 hov2)
    · exact roundRatioTiesToEven_overflow_of f neg n d hn hd
  refine ⟨hiff1, ?_⟩
  constructor
  · intro hdec
    apply hiff1.mpr
    by_cases hov1 : f.maxExponent < max (ratioExponent n d) f.minExponent
    · exact Or.inl hov1
    · by_cases hov2 : max (ratioExponent n d) f.minExponent = f.maxExponent ∧
          roundQuotientTiesToEven
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).1
            (powScale n d ((f.fractionBits : Int) - max (ratioExponent n d) f.minExponent)).2 =
          2 ^ (f.fractionBits + 1)
      · exact Or.inr hov2
      · exact absurd hdec (hnot_inf_of_not_ov hov1 hov2)
  · intro heq
    rw [heq, decodeBits_infBits]

/-- **Universal signed-zero & gradual-underflow sign preservation**:
1. `roundRatioBits mode f neg 0 d = zeroBits f neg` (decoding to `.zero neg`) for every
   `0 < d`;
2. Whenever `0 < n`, `0 < d`, and `roundQuotient mode scaled.1 scaled.2 = 0` (gradual
   underflow past the smallest subnormal), `roundRatioBits mode f neg n d = zeroBits f neg`
   and `decodeBits f (roundRatioBits mode f neg n d) = .zero neg` (preserving `-0.0` when
   `neg = true`);
3. `evalFloatToFloatRoundTiesToEven` preserves `.zero neg` and `.inf neg` (including their
   sign `neg`) across all source and destination formats;
4. Concrete negative-finite gradual-underflow canary: `-2^-150` (`0xB690_0000_0000_0000 : f64`)
   narrows to `-0.0` (`0x8000_0000 : f32`, never `+0.0`), while `-(2^-150 + 2^-202)`
   (`0xB690_0000_0000_0001 : f64`) narrows to negative smallest subnormal `0x8000_0001 : f32`. -/
theorem roundRatioBits_sign_and_underflow_zero_preserved :
    (∀ (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (d : Nat), 0 < d →
      roundRatioBits mode f neg 0 d = zeroBits f neg ∧
        decodeBits f (roundRatioBits mode f neg 0 d) = .zero neg) ∧
    (∀ (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d : Nat), 0 < n → 0 < d →
      let exponent := max (ratioExponent n d) f.minExponent
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      roundQuotient mode scaled.1 scaled.2 = 0 →
      roundRatioBits mode f neg n d = zeroBits f neg ∧
        decodeBits f (roundRatioBits mode f neg n d) = .zero neg) ∧
    (∀ (src dst : IeeeFormat) (bits : Nat) (neg : Bool),
      decodeBits src bits = .zero neg →
      decodeBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = .zero neg) ∧
    (∀ (src dst : IeeeFormat) (bits : Nat) (neg : Bool),
      decodeBits src bits = .inf neg →
      decodeBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = .inf neg) ∧
    f64ToF32 0xB690000000000000#64 = 0x80000000#32 ∧
    f64ToF32 0xB690000000000001#64 = 0x80000001#32 := by
  refine ⟨?_, ?_, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · intro mode f neg d hd
    have hd0 : d ≠ 0 := by omega
    have hz : roundRatioBits mode f neg 0 d = zeroBits f neg := by
      simp [roundRatioBits, hd0]
    rw [hz]
    exact ⟨rfl, decodeBits_zeroBits f neg⟩
  · intro mode f neg n d hn hd
    dsimp only
    intro hsig0
    have hd0 : d ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hlo_ge := (powScale_roundRatio_scaled_bounds f n d hn hd).2.1
    generalize hexp : max (ratioExponent n d) f.minExponent = exponent at hlo_ge hsig0
    generalize hsc : powScale n d ((f.fractionBits : Int) - exponent) = scaled at hlo_ge hsig0
    have hds : 0 < scaled.2 := by rw [← hsc]; exact powScale_snd_pos_gen n d hd _
    have hexp_min : exponent = f.minExponent := by
      by_cases hge : f.minExponent ≤ ratioExponent n d
      · have hge_sig : 2 ^ f.fractionBits ≤ roundQuotient mode scaled.1 scaled.2 :=
          roundQuotient_ge_of_mul_le mode scaled.1 scaled.2 _ hds (hlo_ge hge)
        rw [hsig0] at hge_sig
        have := Nat.two_pow_pos f.fractionBits
        clear hlo_ge hexp hsc hds; omega
      · rw [← hexp]; exact int_max_eq_right hge
    have hov1 : ¬ (exponent > f.maxExponent) := by
      rw [hexp_min]
      cases f <;> decide
    have hcarry : ¬ (2 ^ (f.fractionBits + 1) ≤ 0) := by
      cases f <;> decide
    have hsub : 0 < 2 ^ f.fractionBits := Nat.two_pow_pos _
    have hr : roundRatioBits mode f neg n d = zeroBits f neg := by
      unfold roundRatioBits
      simp only [hd0, hn0, ↓reduceIte, hexp, hsc]
      rw [if_neg' hov1]
      simp only [hsig0, hcarry, decide_false, Bool.false_eq_true, ↓reduceIte, hov1]
      rw [if_pos' hsub, if_pos' hexp_min, ← zeroBits_eq_encodeBits]
    rw [hr]
    exact ⟨rfl, decodeBits_zeroBits f neg⟩
  · intro src dst bits neg h
    unfold evalFloatToFloatRoundTiesToEven
    rw [convertFloatBits_of_zero _ _ _ _ _ h, decodeBits_zeroBits]
  · intro src dst bits neg h
    unfold evalFloatToFloatRoundTiesToEven
    rw [convertFloatBits_of_inf _ _ _ _ _ h, decodeBits_infBits]

/-! ### Part B soundness bundles -/

/-- **`evalIntToFloatRoundTiesToEven_sound`**: (1) every representable integer
`|v| < 2^(fb+1)` converts exactly (universal); (2) every `i32` / `u32` converts to
`binary64` losslessly (universal); (3) the `roundTiesToEven` core of
`roundRatioTiesToEven` is within `½` ULP of the exact quotient and resolves exact ties to an
even significand, and at the float level `roundRatioTiesToEven` never produces NaN (`inconsistentRounding`
is unreachable) and every non-overflowing result decodes to `sig * 2 ^ (exponent - fb)` within
`½` ULP; (4) `u128::MAX` and the exact tie `2^128 - 2^103` overflow to `+∞` in `binary32`,
while `2^128 - 2^103 - 1` rounds down to `f32::MAX`; (5) every int-to-float cast *is*
`roundRatioTiesToEven` of the exact integer (so `roundRatioTiesToEven_correctly_rounded`
applies verbatim). -/
theorem evalIntToFloatRoundTiesToEven_sound :
    (∀ (signed : Bool) (w bits : Nat) (dst : IeeeFormat),
      (intValueOfBits signed w bits).natAbs < 2 ^ (dst.fractionBits + 1) →
      (decodeBits dst (evalIntToFloatRoundTiesToEven signed w bits dst)).denotesInt
        (intValueOfBits signed w bits)) ∧
    (∀ (signed : Bool) (bits : Nat),
      (decodeBits .binary64 (evalIntToFloatRoundTiesToEven signed 32 bits .binary64)).denotesInt
        (intValueOfBits signed 32 bits)) ∧
    (∀ n d : Nat, 0 < d →
      2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs ≤ d) ∧
    (∀ n d : Nat, 0 < d →
      2 * (((roundQuotientTiesToEven n d * d : Nat) : Int) - (n : Int)).natAbs = d →
      roundQuotientTiesToEven n d % 2 = 0) ∧
    (∀ (mode : RoundingMode) (f : IeeeFormat) (neg : Bool) (n d : Nat), 0 < d →
      roundRatioBits mode f neg n d < 2 ^ f.width ∧
        isNaNBits f (roundRatioBits mode f neg n d) = false) ∧
    (∀ (f : IeeeFormat) (neg : Bool) (n d : Nat), 0 < n → 0 < d →
      let exponent := max (ratioExponent n d) f.minExponent
      let scaled := powScale n d ((f.fractionBits : Int) - exponent)
      let sig := roundQuotientTiesToEven scaled.1 scaled.2
      2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs ≤ scaled.2 ∧
        (2 * (((sig * scaled.2 : Nat) : Int) - (scaled.1 : Int)).natAbs = scaled.2 →
          sig % 2 = 0) ∧
        (decodeBits f (roundRatioTiesToEven f neg n d) ≠ .inf neg →
          (decodeBits f (roundRatioTiesToEven f neg n d)).sameValue
            (if sig = 0 then .zero neg
             else .finite neg (powScale sig 1 (exponent - f.fractionBits)).1
               (powScale sig 1 (exponent - f.fractionBits)).2))) ∧
    (∀ (signed : Bool) (w bits : Nat) (dst : IeeeFormat),
      evalIntToFloatRoundTiesToEven signed w bits dst =
        roundRatioTiesToEven dst (decide (intValueOfBits signed w bits < 0))
          (intValueOfBits signed w bits).natAbs 1) ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 1) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103) .binary32 = 0x7F800000 ∧
    evalIntToFloatRoundTiesToEven false 128 (2 ^ 128 - 2 ^ 103 - 1) .binary32 = 0x7F7FFFFF :=
  ⟨evalIntToFloatRoundTiesToEven_exact, evalIntToFloat_i32_u32_to_f64_exact,
   roundQuotientTiesToEven_half_ulp, roundQuotientTiesToEven_tie_even,
   roundRatioBits_valid_and_not_nan, roundRatioTiesToEven_float_half_ulp,
   fun _ _ _ _ => rfl,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`evalFloatToFloatRoundTiesToEven_sound`**: (1) `f32 → f64` preserves the exact value
of, and round-trips, every non-NaN `F32Bits`; (2) every NaN input converts to a quiet NaN
in every direction; (3) the signaling-NaN quietization canary (`0x7FF0_0000_0000_0001 ↦
0x7FC0_0000`, never `+∞`); (4) `f64 → f32` narrowing of `-0.0`, gradual underflow to `+0`,
the smallest subnormal at the half-way boundary, and overflow to `+∞` at the exact tie;
(5) every finite nonzero input converts to `roundRatioTiesToEven` of its exact rational value
(so `roundRatioTiesToEven_correctly_rounded` applies verbatim to `f64 → f32` narrowing). -/
theorem evalFloatToFloatRoundTiesToEven_sound :
    (∀ x : F32Bits, isNaNBits .binary32 x.toNat = false →
      (decodeBits .binary64 (f32ToF64 x).toNat).sameValue (decodeBits .binary32 x.toNat) ∧
      f64ToF32 (f32ToF64 x) = x) ∧
    (∀ (src dst : IeeeFormat) (bits : Nat), isNaNBits src bits = true →
      isNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = true ∧
        isQuietNaNBits dst (evalFloatToFloatRoundTiesToEven src dst bits) = true) ∧
    (f64ToF32 0x7FF0000000000001#64 = 0x7FC00000#32 ∧
      f64ToF32 0x7FF0000000000001#64 ≠ 0x7F800000#32) ∧
    f64ToF32 0x8000000000000000#64 = 0x80000000#32 ∧
    f64ToF32 0x3690000000000000#64 = 0x00000000#32 ∧
    f64ToF32 0x3690000000000001#64 = 0x00000001#32 ∧
    f64ToF32 0x47EFFFFFF0000000#64 = 0x7F800000#32 ∧
    (∀ (src dst : IeeeFormat) (bits : Nat) (neg : Bool) (n d : Nat),
      decodeBits src bits = .finite neg n d →
      evalFloatToFloatRoundTiesToEven src dst bits = roundRatioTiesToEven dst neg n d) :=
  ⟨f32ToF64_exact_and_roundtrip,
   fun src dst bits h => convertFloatBits_nan_quiet .tiesToEven src dst bits h,
   ⟨f64ToF32_signaling_nan_quietized.1, f64ToF32_signaling_nan_quietized.2.1⟩,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   fun src dst bits neg n d h => convertFloatBits_of_finite .tiesToEven src dst bits neg n d h⟩

end PartBTheorems

/-! ## §7. Axiom guards

Every headline theorem is pinned to the standard axioms (`propext` / `Quot.sound`, or
none): `#guard_msgs` fails the build if a proof ever starts depending on
`Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any other non-standard
axioms (including placeholder proofs).
`scripts/test_tcb_correspondence_div8_proto.py` additionally replays `#print axioms` for
*every* declaration of this file. -/

section AxiomGuards

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.intrinsicOfDefPathSF_table' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms intrinsicOfDefPathSF_table

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.translateProgWithIntrinsicsSF_witnesses_isSome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms translateProgWithIntrinsicsSF_witnesses_isSome

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_trusted_baseline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_trusted_baseline

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_trusted_137' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_trusted_137

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_mach_tb_42' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_mach_tb_42

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_repaired_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_write_back_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_write_back_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_write_back_trusted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_write_back_trusted

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_caller_borrow_across_scalar_call_trusted_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_caller_borrow_across_scalar_call_trusted_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_caller_borrow_across_scalar_call_mach_tb_42' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_caller_borrow_across_scalar_call_mach_tb_42

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_caller_borrow_across_scalar_call_repaired_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_caller_borrow_across_scalar_call_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_caller_borrow_frame_isolation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_caller_borrow_frame_isolation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.updateBorrowPermAtProjProto_other_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms updateBorrowPermAtProjProto_other_frame

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.entryAccessTransitionProto_other_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms entryAccessTransitionProto_other_frame

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_twophase_direct_write_repaired_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_twophase_direct_write_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_fnentry_local_dealloc_trusted_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_fnentry_local_dealloc_trusted_ret

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_fnentry_local_dealloc_repaired_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_fnentry_local_dealloc_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_fnentry_local_dealloc_ub_at_return' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_fnentry_local_dealloc_ub_at_return

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_fnentry_local_dealloc_callee_return_canary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_fnentry_local_dealloc_callee_return_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.preventsDeallocation_eq_miniRust' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms preventsDeallocation_eq_miniRust

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.preventsDeallocation_table' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms preventsDeallocation_table

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_unsafecell_protected_im_repaired_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_unsafecell_protected_im_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_unsafecell_coupling_legacy_breaks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_unsafecell_coupling_legacy_breaks

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_unsafecell_storage_dead_canary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_unsafecell_storage_dead_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_raw_overwrite_char_copy_trusted_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_raw_overwrite_char_copy_trusted_steps

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_raw_overwrite_char_copy_repaired_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_raw_overwrite_char_copy_repaired_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_raw_overwrite_char_copy_ub_at_load' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_raw_overwrite_char_copy_ub_at_load

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_raw_overwrite_char_copy_valid_accepted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_raw_overwrite_char_copy_valid_accepted

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.isValidCharCode_iff_isValidChar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isValidCharCode_iff_isValidChar

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.validateLoadedValueProto_char_eq_miri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validateLoadedValueProto_char_eq_miri

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.miriValidateCharScalar_boundaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms miriValidateCharScalar_boundaries

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_disabled_trusted_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_disabled_trusted_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_trusted_evalPtrOffsetBinOp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_trusted_evalPtrOffsetBinOp

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_disabled_repaired_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_disabled_repaired_steps

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_disabled_deref_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_disabled_deref_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalBinOpOffset_lockstep_miri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalBinOpOffset_lockstep_miri

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_disabled_tag_repaired_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_disabled_tag_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_lockstep_examples' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_lockstep_examples

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_trusted_uninit_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_trusted_uninit_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_trusted_faults' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_trusted_faults

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_uninit_repaired_agrees' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_uninit_repaired_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_observed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_observed

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_payload_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_payload_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_dead_and_init' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_dead_and_init

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.pack_unpack_f32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_unpack_f32

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.unpack_pack_f32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unpack_pack_f32

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.pack_unpack_f64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_unpack_f64

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.unpack_pack_f64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unpack_pack_f64

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.decodeBits_agrees_miriDecode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeBits_agrees_miriDecode

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalFloatToIntSaturating_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_sound

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalFloatToIntSaturating_nan' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_nan

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalFloatToIntSaturating_canaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToIntSaturating_canaries

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundQuotientTiesToEven_half_ulp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundQuotientTiesToEven_half_ulp

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundQuotientTiesToEven_tie_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundQuotientTiesToEven_tie_even

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioBits_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_congr

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioBits_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_normal

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioBits_subnormal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_subnormal

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalIntToFloatRoundTiesToEven_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_exact

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalIntToFloat_i32_u32_to_f64_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloat_i32_u32_to_f64_exact

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.b585733184_ties_to_even_separation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms b585733184_ties_to_even_separation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalIntToFloatRoundTiesToEven_canaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_canaries

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalIntToFloatRoundTiesToEven_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalIntToFloatRoundTiesToEven_sound

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.f32ToF64_exact_and_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f32ToF64_exact_and_roundtrip

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.convertFloatBits_nan_quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convertFloatBits_nan_quiet

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.f64ToF32_signaling_nan_quietized' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms f64ToF32_signaling_nan_quietized

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalFloatToFloatRoundTiesToEven_canaries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_canaries

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalFloatToFloatRoundTiesToEven_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalFloatToFloatRoundTiesToEven_sound

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.castKind_end_to_end' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms castKind_end_to_end

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.castKind_trusted_unsupported' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms castKind_trusted_unsupported

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_target_local_reborrow_in_callee_canary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_target_local_reborrow_in_callee_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.reborrow_inherits_targetFrameDepth' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms reborrow_inherits_targetFrameDepth

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.direct_write_disables_reservedFrz_preserves_cell_and_reservedIM' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_write_disables_reservedFrz_preserves_cell_and_reservedIM

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_twophase_direct_write_reservedIM_and_cell_survive_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_twophase_direct_write_reservedIM_and_cell_survive_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.hasProtectedLocalBorrowProto_cell_exempt_reservedIM_blocks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms hasProtectedLocalBorrowProto_cell_exempt_reservedIM_blocks

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.disableFrameBorrowsProto_frame_isolation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms disableFrameBorrowsProto_frame_isolation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_tb_fnentry_dangling_callee_raw_ptr_return_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_raw_overwrite_char_projected_move_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_raw_overwrite_char_projected_move_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.evalRetagProto_raw_uninit_or_dead_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalRetagProto_raw_uninit_or_dead_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.disabled_tag_deref_and_reborrow_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms disabled_tag_deref_and_reborrow_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_protected_conflict_ub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_protected_conflict_ub

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_enum_set_discr_borrow_invalidation_and_protector_canary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_enum_set_discr_borrow_invalidation_and_protector_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.f64ToF32_subnormal_and_double_rounding_canaries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms f64ToF32_subnormal_and_double_rounding_canaries

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioBits_valid_and_not_nan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_valid_and_not_nan

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioTiesToEven_float_half_ulp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_float_half_ulp

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.writePlaceProto_direct_frame_isolation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms writePlaceProto_direct_frame_isolation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.writePlaceProto_deref_frame_isolation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms writePlaceProto_deref_frame_isolation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.overlay_coverage_canaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overlay_coverage_canaries

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioTiesToEven_correctly_rounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_correctly_rounded

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioTiesToEven_overflow_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_overflow_of

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_offset_dead_alloc_lockstep_miri' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_offset_dead_alloc_lockstep_miri

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_lm_d6_wit_lm3_1_four_witnesses_and_revive_canary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_lm_d6_wit_lm3_1_four_witnesses_and_revive_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.writePlaceProto_frame_local_isolation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms writePlaceProto_frame_local_isolation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.readPlaceProto_and_stmt_borrow_frame_isolation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms readPlaceProto_and_stmt_borrow_frame_isolation

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_call_ref_mut_protected_roundtrip_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_call_ref_mut_protected_roundtrip_agrees

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.div_mr_return_destination_invalidation_and_protector_canary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_mr_return_destination_invalidation_and_protector_canary

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.hasProtectedLocalBorrowProto_of_hasProtectedWriteConflictProto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasProtectedLocalBorrowProto_of_hasProtectedWriteConflictProto

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.hasProtectedLocalBorrowProto_disableLocalBorrowsProto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasProtectedLocalBorrowProto_disableLocalBorrowsProto

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioTiesToEven_overflow_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioTiesToEven_overflow_iff

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.roundRatioBits_sign_and_underflow_zero_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundRatioBits_sign_and_underflow_zero_preserved

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.corpus_agreement_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corpus_agreement_kernel

/-- info: 'Anneal.TcbCorrespondenceDiv8AndFloatPrototype.corpus_out_of_fragment_fixes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corpus_out_of_fragment_fixes

end AxiomGuards

end Anneal.TcbCorrespondenceDiv8AndFloatPrototype
