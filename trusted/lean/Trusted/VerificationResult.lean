import Trusted.Refinement
import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Layout
import Trusted.MirAst
import Trusted.MirSemantics

namespace Trusted.VerificationResult

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Layout
open Trusted.MirAst
open Trusted.MirSemantics

/-!
Trusted verification gate types (`Claim`, `VerificationResult`, `StatefulClaim`,
`StatefulVerificationResult`, `ModularClaim`, `ModularVerificationResult`,
`TraceClaim`, `TraceVerificationResult`, `TotalClaim`, and
`TotalVerificationResult`) over MIR interaction trees (`mirTree`), checked by
the Lean 4 kernel and audited by `trusted/audit/check_trusted.py` (`#100`,
`#102`, `#103`).

Because `mirTree` models unresolved external calls through `MirCallE`, the
default `Claim` and `StatefulClaim` gates leave external calls unconstrained: a
proof of `VerificationResult` or `StatefulVerificationResult` must hold across
all possible external-call answers `MirCallAns` (including distinct answers
across consecutive calls, mutated memories, and unwinding). Explicit rely
assumptions on external callees are stated via `ModularClaim` as predicates on
`ExternalCallHandler`s interpreted through `ITree.interp`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/

/-- Cryptographic and toolchain identity of a verified compilation unit. -/
structure ArtifactIdentity : Type where
  /-- Crate-qualified `DefId` path of the verified item. -/
  defPath : DefPath
  /-- Recorded MIR dialect tag (e.g., `"V2026_06_01"`). -/
  mirDialect : String
  /-- SHA-256 hex digest of the generated `Mir/<Item>.lean` module. -/
  mirModuleSha256 : String
  deriving DecidableEq, Repr

/--
Initial `MachineState` for `body` with incoming `args` and initial `Memory`
`mem`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L368>

> "At any point during the execution of a function, each local is either
> allocated or unallocated. Except as noted below, all locals except function
> parameters are initially unallocated."
-/
def initMachineStateWithMemory
    (body : CapturedMir) (args : List Value) (mem : Memory) : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals body args
    }
    memory := mem
  }

/--
Verify that a `ScalarInt` is a valid 4-byte Unicode scalar value
(`0x0000..=0xD7FF` or `0xE000..=0x10FFFF`).

Reference (The Rust Reference, "Textual types"):
<https://doc.rust-lang.org/1.98.0/reference/types/textual.html>

> "A value of type char is a Unicode scalar value (i.e. a code point that is not
> a surrogate), represented as a 32-bit unsigned word in the 0x0000 to 0xD7FF or
> 0xE000 to 0x10FFFF range."
-/
@[reducible, simp]
def isValidChar (sv : ScalarInt) : Prop :=
  sv.sizeBytes = 4 ∧
    (sv.bits ≤ 0xD7FF ∨ (0xE000 ≤ sv.bits ∧ sv.bits ≤ 0x10FFFF))

/--
Maximum signed `isize::MAX` byte count for allocations and wide slices on target
pointer bit-width `ptrBits` (`2^31 - 1` on 32-bit targets, `2^63 - 1` on 64-bit
targets).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The size of the referenced value cannot exceed `isize::MAX`."
-/
@[reducible, simp]
def maxIsizeBytes (ptrBits : Nat) : Nat :=
  match Nat.beq ptrBits 32 with
  | true => 2147483647
  | false => 9223372036854775807

/--
Test whether `layout` is the synthetic generic-parameter placeholder entry
(`size = 0`, `variants = .empty`, `isUninhabited = false`) emitted for an
unsubstituted `RigidTy.param` (`@[reducible]` for `dsimp` reduction).
-/
@[reducible, simp]
def sigIsParamPlaceholder (layout : TypeLayout) : Bool :=
  match layout.variants with
  | .empty => Nat.beq layout.size.bytes 0 && !layout.isUninhabited
  | _ => false

/--
Test whether `val` lies within `range : WrappingRange` (`@[reducible]` for
`dsimp` reduction).
-/
@[reducible, simp]
def sigWrappingRangeContains (range : WrappingRange) (val : Nat) : Bool :=
  match Nat.ble range.start range.end_ with
  | true => Nat.ble range.start val && Nat.ble val range.end_
  | false => Nat.ble range.start val || Nat.ble val range.end_

/--
Byte width of a `PrimitiveKind` scalar (`@[reducible]` for `dsimp` reduction).
-/
@[reducible, simp]
def sigPrimitiveByteWidth : PrimitiveKind → Option Nat
  | .int bits _ =>
    match Nat.beq (bits % 8) 0 && Nat.blt 0 bits with
    | true => .some (bits / 8)
    | false => .none
  | .float bits =>
    match Nat.beq (bits % 8) 0 && Nat.blt 0 bits with
    | true => .some (bits / 8)
    | false => .none
  | .pointer _ => .none

/--
Byte width of a `ScalarLayout` (`@[reducible]` for `dsimp` reduction).
-/
@[reducible, simp]
def sigScalarLayoutByteWidth : ScalarLayout → Option Nat
  | .initialized prim _ => sigPrimitiveByteWidth prim
  | .union prim => sigPrimitiveByteWidth prim

/--
Check that a scalar bit pattern `bits` satisfies any `WrappingRange` validity
constraint recorded on `repr`
(`BackendRepr.scalar (.initialized _ validRange)`).

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1539-L1559>

> "Initialized { value: Primitive, valid_range: WrappingRange }"
-/
@[reducible, simp]
def scalarMatchesBackendRepr (repr : BackendRepr) (bits : Nat) : Prop :=
  match repr with
  | .scalar (.initialized _ validRange) =>
    sigWrappingRangeContains validRange bits = true
  | _ => True

/--
Check that a scalar or enum discriminant bit pattern `bits` satisfies the
`WrappingRange` constraint of `sl : ScalarLayout`.
-/
@[reducible, simp]
def tagMatchesScalarLayout (sl : ScalarLayout) (bits : Nat) : Prop :=
  match sl with
  | .initialized _ validRange =>
    sigWrappingRangeContains validRange bits = true
  | .union _ => True

/--
Validate a `Value` against a single `ScalarLayout` component (used for scalar
and scalar-pair struct fields when only `BackendRepr` metadata is present).
-/
@[reducible, simp]
def valueMatchesScalarLayout (sl : ScalarLayout) (val : Value) : Prop :=
  match sigScalarLayoutByteWidth sl with
  | .none => False
  | .some expectedBytes =>
    match val with
    | .scalar sv =>
      0 < expectedBytes ∧
        sv.sizeBytes = expectedBytes ∧
        sv.bits < 2 ^ (sv.sizeBytes * 8) ∧
        tagMatchesScalarLayout sl sv.bits
    | .ptr _ ptrSz =>
      0 < expectedBytes ∧
        ptrSz = expectedBytes ∧
        match sl with
        | .initialized (.pointer _) _ => True
        | .union (.pointer _) => True
        | _ => False
    | _ => False

/--
Look up the element at 0-based index `idx` in `xs` by structural recursion on
`xs` (`@[reducible]` so `dsimp` unfolds concrete layout and variant lookups).
-/
@[reducible, simp]
def sigGet? {α : Type u} : List α → Nat → Option α
  | .nil, _ => .none
  | x :: _, 0 => .some x
  | _ :: xs, n + 1 => sigGet? xs n

/--
Look up the global `CapturedAllocation` with identifier `id` in `globals`
(`@[reducible]` for `dsimp` reduction).
-/
@[reducible, simp]
def sigLookupGlobalAlloc :
    List CapturedAllocation → AllocId → Option CapturedAllocation
  | .nil, _ => .none
  | a :: rest, id =>
    match Nat.beq a.allocId id with
    | true => .some a
    | false => sigLookupGlobalAlloc rest id

/--
Look up the `BorrowEntry` with provenance tag `tag` in `borrows` (`@[reducible]`
for `dsimp` reduction).
-/
@[reducible, simp]
def sigLookupBorrow : List BorrowEntry → Nat → Option BorrowEntry
  | .nil, _ => .none
  | entry :: rest, tag =>
    match Nat.beq entry.tag tag with
    | true => .some entry
    | false => sigLookupBorrow rest tag

/--
Byte width of an unsigned integer type `UintTy` on a target with pointer
bit-width `ptrBits` (`@[reducible]` for `dsimp` reduction).
-/
@[reducible, simp]
def sigUintByteWidth (ptrBits : Nat) : UintTy → Nat
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .u64 => 8
  | .u128 => 16
  | .usize => Nat.div ptrBits 8

/--
Byte width of a signed integer type `IntTy` on a target with pointer bit-width
`ptrBits` (`@[reducible]` for `dsimp` reduction).
-/
@[reducible, simp]
def sigIntByteWidth (ptrBits : Nat) : IntTy → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16
  | .isize => Nat.div ptrBits 8

/--
Search `decls` for the first `LocalDecl` whose `ty.kind` is an `.adt`, returning
its `layoutIdx`.
-/
@[reducible, simp]
def findAdtDeclLayoutIdx : List LocalDecl → Option LayoutIdx
  | .nil => .none
  | d :: rest =>
    match d.ty.kind with
    | .adt _ _ => .some d.ty.layoutIdx
    | _ => findAdtDeclLayoutIdx rest

/--
Test whether any `LocalDecl` in `decls` references layout table slot `idx`.
-/
@[reducible, simp]
def localDeclsUseLayoutIdx : List LocalDecl → LayoutIdx → Bool
  | .nil, _ => false
  | d :: rest, idx =>
    match Nat.beq d.ty.layoutIdx idx with
    | true => true
    | false => localDeclsUseLayoutIdx rest idx

/--
Find the first non-placeholder `TypeLayout` in `entries` (starting at index
`currIdx`) that is not directly referenced by any `LocalDecl` in `decls`.
`anneal-rustc-capture` interns pointee layouts of `&T` / `*const T` parameters
into `body.layouts.entries` immediately after the reference layout.
-/
@[reducible, simp]
def findUnusedLayoutInTable
    (decls : List LocalDecl) :
    List TypeLayout → Nat → Option TypeLayout
  | .nil, _ => .none
  | l :: rest, currIdx =>
    match
      Bool.or
        (localDeclsUseLayoutIdx decls currIdx)
        (sigIsParamPlaceholder l)
    with
    | false => .some l
    | true => findUnusedLayoutInTable decls rest (currIdx + 1)

/--
Resolve the concrete `TypeLayout` of an inner `RigidTy` `childKind` (such as a
reference pointee, slice/array element, tuple element, or ADT field) inside
`parentLayout` (at `parentLayoutIdx`) within `body`.
-/
@[reducible, simp]
def resolveChildLayout
    (body : CapturedMir)
    (parentLayout : TypeLayout)
    (parentLayoutIdx : LayoutIdx)
    (fieldPos : Option Nat)
    (childKind : RigidTy) :
    Option TypeLayout :=
  let fromFieldLayouts : Option TypeLayout :=
    match fieldPos with
    | .some pos =>
      match sigGet? parentLayout.fieldLayouts pos with
      | .some fIdx => sigGet? body.layouts.entries fIdx
      | .none => .none
    | .none =>
      match parentLayout.fieldLayouts with
      | fIdx :: .nil => sigGet? body.layouts.entries fIdx
      | _ => .none
  match fromFieldLayouts with
  | .some l => .some l
  | .none =>
    let effPtrBits :=
      match Nat.beq body.layouts.pointerBits 0 with
      | true => 64
      | false => body.layouts.pointerBits
    match childKind with
    | .uint w =>
      let sz := maxNat 1 (sigUintByteWidth effPtrBits w)
      let bits := sz * 8
      .some
        { size := ⟨sz⟩
          align := ⟨sz⟩
          backendRepr :=
            .scalar (.initialized (.int bits false) ⟨0, 2 ^ bits - 1⟩)
          fields := .primitive
          variants := .single 0
          isUninhabited := false }
    | .int w =>
      let sz := maxNat 1 (sigIntByteWidth effPtrBits w)
      let bits := sz * 8
      .some
        { size := ⟨sz⟩
          align := ⟨sz⟩
          backendRepr :=
            .scalar (.initialized (.int bits true) ⟨0, 2 ^ bits - 1⟩)
          fields := .primitive
          variants := .single 0
          isUninhabited := false }
    | .adt _ adtArgs =>
      let nextIdx := parentLayoutIdx + 1
      let fallback :=
        match findAdtDeclLayoutIdx body.localDecls with
        | .some declIdx => sigGet? body.layouts.entries declIdx
        | .none =>
          findUnusedLayoutInTable body.localDecls body.layouts.entries 0
      let candOpt : Option TypeLayout :=
        match localDeclsUseLayoutIdx body.localDecls nextIdx with
        | false =>
          match sigGet? body.layouts.entries nextIdx with
          | .some candL =>
            match sigIsParamPlaceholder candL with
            | false => .some candL
            | true => fallback
          | .none => fallback
        | true => fallback
      match adtArgs with
      | .nil => candOpt
      | _ :: _ =>
        RigidTy.computeLayout
          body.layouts.pointerBits
          body.layouts.entries
          .nil
          candOpt
          childKind
    | _ =>
      RigidTy.computeLayout
        body.layouts.pointerBits
        body.layouts.entries
        .nil
        .none
        childKind

/--
Check whether Tree Borrows permission `perm` permits a reference with mutability
`refMut` (`&T` allows `.active`, `.reserved`, and `.frozen`; `&mut T` requires
`.active` or `.reserved`).
-/
@[reducible, simp]
def borrowPermAllowsRef : Mutability → TreeBorrowPerm → Bool
  | .not, .disabled => false
  | .not, _ => true
  | .mut, .active => true
  | .mut, .reserved => true
  | .mut, _ => false

/--
Select the remaining generic type arguments `adtArgs` applicable to variant
`variantIdx` of a multi-variant enum (`VariantsShape.multiple`), skipping
zero-field variants (such as `Option::None`) and advancing across payload
variants (such as `Result::Ok(T)` before `Result::Err(E)`).
-/
@[reducible, simp]
def selectVariantTypeArgs :
    Nat → List FieldsShape → List RigidTy → List RigidTy
  | 0, _, adtArgs => adtArgs
  | _ + 1, .nil, adtArgs => adtArgs
  | v + 1, .arbitrary .nil _ :: restShapes, adtArgs =>
    selectVariantTypeArgs v restShapes adtArgs
  | v + 1, .primitive :: restShapes, adtArgs =>
    selectVariantTypeArgs v restShapes adtArgs
  | v + 1, _ :: restShapes, adtArgs =>
    let nextArgs :=
      match adtArgs with
      | _ :: tail@(_ :: _) => tail
      | _ => adtArgs
    selectVariantTypeArgs v restShapes nextArgs

/--
Recursively validate every `Value` in a list using `elemPred`.
-/
@[reducible, simp]
def arrayElemsMatchWith (elemPred : Value → Prop) : List Value → Prop
  | .nil => True
  | e :: rest => elemPred e ∧ arrayElemsMatchWith elemPred rest

/--
Validate an untyped interior field `Value` when neither `adtArgs` nor
`fieldLayouts` nor `Scalar`/`ScalarPair` `BackendRepr` specifies its layout.
-/
@[reducible, simp]
def valueMatchesUntypedField : Nat → Value → Prop
  | 0, _ => False
  | _ + 1, .unit => True
  | _ + 1, .scalar sv =>
    0 < sv.sizeBytes ∧ sv.bits < 2 ^ (sv.sizeBytes * 8)
  | _ + 1, .ptr _ ptrSz => 0 < ptrSz
  | fuel' + 1, .aggregate _ fields =>
    arrayElemsMatchWith (valueMatchesUntypedField fuel') fields

/--
Recursively validate each field of an untyped ADT against `parentLayout` using
`layoutPred` when `fieldLayouts` is populated.
-/
@[reducible, simp]
def adtFieldsLayoutOnlyWith
    (fuel' : Nat)
    (body : CapturedMir)
    (parentLayout : TypeLayout)
    (layoutPred : Option TypeLayout → LayoutIdx → Value → Prop) :
    Nat → List Value → Prop
  | _, .nil => True
  | pos, v :: restV =>
    let ok : Prop :=
      match sigGet? parentLayout.fieldLayouts pos with
      | .some fIdx =>
        layoutPred (sigGet? body.layouts.entries fIdx) fIdx v
      | .none =>
        match parentLayout.variants, parentLayout.backendRepr with
        | .single _, .scalar sl =>
          match pos, restV with
          | 0, .nil => valueMatchesScalarLayout sl v
          | _, _ => valueMatchesUntypedField fuel' v
        | .single _, .scalarPair sl0 sl1 =>
          match pos with
          | 0 => valueMatchesScalarLayout sl0 v
          | 1 => valueMatchesScalarLayout sl1 v
          | _ => valueMatchesUntypedField fuel' v
        | _, _ => valueMatchesUntypedField fuel' v
    ok ∧
      adtFieldsLayoutOnlyWith fuel' body parentLayout layoutPred (pos + 1) restV

/--
Recursively validate each element of an untyped ADT with `FieldsShape.array`.
-/
@[reducible, simp]
def adtArrayLayoutOnlyWith
    (body : CapturedMir)
    (parentLayout : TypeLayout)
    (strideBytes : Nat)
    (layoutPred : Option TypeLayout → LayoutIdx → Value → Prop) :
    List Value → Prop
  | .nil => True
  | e :: rest =>
    let elemOk : Prop :=
      match parentLayout.fieldLayouts with
      | fIdx :: _ =>
        layoutPred (sigGet? body.layouts.entries fIdx) fIdx e
      | .nil =>
        match e with
        | .scalar sv =>
          sv.sizeBytes = strideBytes ∧
            0 < sv.sizeBytes ∧
            sv.bits < 2 ^ (sv.sizeBytes * 8)
        | _ => False
    elemOk ∧
      adtArrayLayoutOnlyWith body parentLayout strideBytes layoutPred rest

/--
Validate a `Value` when only its `TypeLayout` (from `fieldLayouts`) is known.
-/
@[reducible, simp]
def valueMatchesLayoutOnly :
    Nat → CapturedMir → Option TypeLayout → LayoutIdx → Value → Memory → Prop
  | 0, _, _, _, _, _ => False
  | _ + 1, _, .none, _, _, _ => False
  | _ + 1, _, .some layout, _, .unit, _ =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      match layout.variants, layout.fields with
      | .single 0, .arbitrary .nil _ => layout.size.bytes = 0
      | .single 0, .array _ 0 => layout.size.bytes = 0
      | _, _ => False
  | _ + 1, _, .some layout, _, .scalar sv, _ =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      match layout.variants, layout.fields with
      | .single _, .primitive =>
        match layout.backendRepr with
        | .scalar sl =>
          valueMatchesScalarLayout sl (.scalar sv) ∧
            sv.sizeBytes = layout.size.bytes
        | _ => False
      | .single _, .union count =>
        0 < count ∧
          sv.sizeBytes = layout.size.bytes ∧
          0 < sv.sizeBytes ∧
          sv.bits < 2 ^ (sv.sizeBytes * 8)
      | _, _ => False
  | _ + 1, _, .some layout, _, .ptr p ptrSz, _ =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      match layout.variants, layout.fields, layout.backendRepr with
      | .single _, .primitive, .scalar sl =>
        valueMatchesScalarLayout sl (.ptr p ptrSz) ∧
          ptrSz = layout.size.bytes
      | _, _, _ => False
  | fuel' + 1, body, .some layout, _layoutIdx, .aggregate vIdx fields, mem =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      let recPred := fun optFl fIdx v =>
        valueMatchesLayoutOnly fuel' body optFl fIdx v mem
      match layout.variants with
      | .empty => False
      | .single expectedVar =>
        match layout.fields with
        | .primitive => False
        | .arbitrary offsets _ =>
          match offsets with
          | .nil =>
            layout.size.bytes = 0 ∧ vIdx = expectedVar ∧ fields = .nil
          | _ :: _ =>
            vIdx = expectedVar ∧
              fields.length = offsets.length ∧
              adtFieldsLayoutOnlyWith fuel' body layout recPred 0 fields
        | .array stride count =>
          match count with
          | 0 =>
            layout.size.bytes = 0 ∧ vIdx = expectedVar ∧ fields = .nil
          | _ + 1 =>
            vIdx = expectedVar ∧
              fields.length = count ∧
              adtArrayLayoutOnlyWith body layout stride.bytes recPred fields
        | .union count =>
          0 < count ∧
            match fields with
            | .cons fVal .nil =>
              vIdx = expectedVar ∧
                adtFieldsLayoutOnlyWith
                  fuel' body layout recPred 0 (.cons fVal .nil)
            | _ => False
      | .multiple tag _ variantShapes =>
        vIdx < variantShapes.length ∧
          tagMatchesScalarLayout tag vIdx ∧
          match sigGet? variantShapes vIdx with
          | .some (.arbitrary varOffsets _) =>
            fields.length = varOffsets.length ∧
              adtFieldsLayoutOnlyWith fuel' body layout recPred 0 fields
          | .some .primitive => fields = .nil
          | _ => False

/--
Recursively validate each field of a tuple or closure aggregate against its
corresponding `RigidTy` and resolved field `TypeLayout`.
-/
@[reducible, simp]
def tupleFieldsMatchWith
    (body : CapturedMir)
    (parentLayout : TypeLayout)
    (parentLayoutIdx : LayoutIdx)
    (tyPred : RigidTy → Option TypeLayout → LayoutIdx → Value → Prop) :
    Nat → List RigidTy → List Value → Prop
  | _, .nil, .nil => True
  | pos, k :: restK, v :: restV =>
    tyPred
      k
      (resolveChildLayout body parentLayout parentLayoutIdx (.some pos) k)
      parentLayoutIdx
      v ∧
      tupleFieldsMatchWith
        body parentLayout parentLayoutIdx tyPred (pos + 1) restK restV
  | _, _, _ => False

/--
Recursively validate each element of an ADT with `FieldsShape.array`.
-/
@[reducible, simp]
def adtArrayElemsMatchWith
    (fuel' : Nat)
    (body : CapturedMir)
    (parentLayout : TypeLayout)
    (parentLayoutIdx : LayoutIdx)
    (strideBytes : Nat)
    (adtArgs : List RigidTy)
    (tyPred : RigidTy → Option TypeLayout → LayoutIdx → Value → Prop)
    (mem : Memory) :
    List Value → Prop
  | .nil => True
  | e :: rest =>
    let elemOk : Prop :=
      match adtArgs with
      | elemKind :: _ =>
        tyPred
          elemKind
          (resolveChildLayout
            body parentLayout parentLayoutIdx (.some 0) elemKind)
          parentLayoutIdx
          e
      | .nil =>
        match parentLayout.fieldLayouts with
        | fIdx :: _ =>
          valueMatchesLayoutOnly
            fuel' body (sigGet? body.layouts.entries fIdx) fIdx e mem
        | .nil =>
          match e with
          | .scalar sv =>
            sv.sizeBytes = strideBytes ∧
              0 < sv.sizeBytes ∧
              sv.bits < 2 ^ (sv.sizeBytes * 8)
          | _ => False
    elemOk ∧
      adtArrayElemsMatchWith
        fuel' body parentLayout parentLayoutIdx strideBytes adtArgs tyPred
        mem rest

/--
Recursively validate each field of an ADT variant against `adtArgs`,
`parentLayout.fieldLayouts`, or `parentLayout.backendRepr`.
-/
@[reducible, simp]
def adtFieldsMatchWith
    (fuel' : Nat)
    (body : CapturedMir)
    (parentLayout : TypeLayout)
    (parentLayoutIdx : LayoutIdx)
    (tyPred : RigidTy → Option TypeLayout → LayoutIdx → Value → Prop)
    (mem : Memory) :
    Nat → List RigidTy → List Value → Prop
  | _, _, .nil => True
  | pos, adtArgs, v :: restV =>
    let (fieldOk, nextAdtArgs) : Prop × List RigidTy :=
      match adtArgs with
      | argKind :: restArgs =>
        let nextArgs :=
          match restArgs with
          | .nil => argKind :: .nil
          | _ => restArgs
        let ok :=
          tyPred
            argKind
            (resolveChildLayout
              body parentLayout parentLayoutIdx (.some pos) argKind)
            parentLayoutIdx
            v
        (ok, nextArgs)
      | .nil =>
        let ok :=
          match sigGet? parentLayout.fieldLayouts pos with
          | .some fIdx =>
            valueMatchesLayoutOnly
              fuel' body (sigGet? body.layouts.entries fIdx) fIdx v mem
          | .none =>
            match parentLayout.variants, parentLayout.backendRepr with
            | .single _, .scalar sl =>
              match pos, restV with
              | 0, .nil => valueMatchesScalarLayout sl v
              | _, _ => valueMatchesUntypedField fuel' v
            | .single _, .scalarPair sl0 sl1 =>
              match pos with
              | 0 => valueMatchesScalarLayout sl0 v
              | 1 => valueMatchesScalarLayout sl1 v
              | _ => valueMatchesUntypedField fuel' v
            | _, _ => valueMatchesUntypedField fuel' v
        (ok, .nil)
    fieldOk ∧
      adtFieldsMatchWith
        fuel' body parentLayout parentLayoutIdx tyPred mem (pos + 1)
        nextAdtArgs restV

/--
Structurally validate a `Value` against a concrete `RigidTy` and `TypeLayout`
in `mem` with recursion depth bound `fuel`.

Rejects uninstantiated generic parameters (`RigidTy.param` and
`sigIsParamPlaceholder`), uninhabited types (`!` and empty enums),
invalid `bool` / `char` / discriminant bit patterns, misaligned or out-of-bounds
references `&T` / `&mut T`, and wide slices `&[T]` / `&mut [T]` / `&str` whose
byte length exceeds `isize::MAX` or the backing allocation in `mem`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value, even in private fields and locals. 'Producing' a
> value happens any time a value is assigned to or read from a place, passed to
> a function/primitive operation or returned from a function/primitive
> operation."
-/
@[reducible, simp]
def valueMatchesRigidTyAndLayout :
    Nat → CapturedMir → RigidTy → Option TypeLayout → LayoutIdx → Value →
      Memory → Prop
  | 0, _, _, _, _, _, _ => False
  | _ + 1, _, _, .none, _, _, _ => False
  | _ + 1, body, kind, .some layout, layoutIdx, .unit, _ =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      match kind with
      | .fnDef _ _ | .tuple .nil | .closure _ .nil =>
        layout.size.bytes = 0
      | .array elemKind 0 =>
        layout.size.bytes = 0 ∧
          match resolveChildLayout body layout layoutIdx (.some 0) elemKind with
          | .none => False
          | .some elemLayout =>
            elemLayout.isUninhabited = false ∧
              sigIsParamPlaceholder elemLayout = false
      | .adt _ _ =>
        match layout.variants, layout.fields with
        | .single expectedVar, .arbitrary .nil _ =>
          expectedVar = 0 ∧ layout.size.bytes = 0
        | .single expectedVar, .array _ count =>
          expectedVar = 0 ∧ count = 0 ∧ layout.size.bytes = 0
        | _, _ => False
      | _ => False
  | _ + 1, _, kind, .some layout, _, .scalar sv, _ =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      match kind with
      | .bool =>
        layout.size.bytes = 1 ∧
          sv.sizeBytes = 1 ∧
          (sv.bits = 0 ∨ sv.bits = 1) ∧
          scalarMatchesBackendRepr layout.backendRepr sv.bits
      | .char =>
        layout.size.bytes = 4 ∧
          isValidChar sv ∧
          scalarMatchesBackendRepr layout.backendRepr sv.bits
      | .int _ | .uint _ | .float _ =>
        sv.sizeBytes = layout.size.bytes ∧
          0 < sv.sizeBytes ∧
          sv.bits < 2 ^ (sv.sizeBytes * 8) ∧
          scalarMatchesBackendRepr layout.backendRepr sv.bits
      | .fnPtr _ _ _ _ =>
        sv.sizeBytes = layout.size.bytes ∧
          0 < sv.bits ∧
          sv.bits < 2 ^ (sv.sizeBytes * 8) ∧
          scalarMatchesBackendRepr layout.backendRepr sv.bits
      | .rawPtr _ pointee =>
        match pointee with
        | .slice _ | .str | .dynamic _ | .param _ _ | .alias _ _ => False
        | _ =>
          sv.sizeBytes = layout.size.bytes ∧
            0 < sv.sizeBytes ∧
            sv.bits < 2 ^ (sv.sizeBytes * 8)
      | .adt _ _ =>
        match layout.variants, layout.fields with
        | .single _, .union count =>
          0 < count ∧
            sv.sizeBytes = layout.size.bytes ∧
            0 < sv.sizeBytes ∧
            sv.bits < 2 ^ (sv.sizeBytes * 8)
        | _, _ => False
      | _ => False
  | fuel' + 1, body, kind, .some layout, layoutIdx, .ptr p ptrSz, mem =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      match kind with
      | .fnPtr _ _ _ _ =>
        ptrSz = layout.size.bytes ∧ 0 < ptrSz ∧ p.offsetBytes = 0
      | .rawPtr _ pointee =>
        match pointee with
        | .slice _ | .str | .dynamic _ | .param _ _ | .alias _ _ => False
        | _ => ptrSz = layout.size.bytes ∧ 0 < ptrSz
      | .ref refMut pointee =>
        match pointee with
        | .slice _ | .str | .dynamic _ | .foreign _ | .other _
        | .param _ _ | .alias _ _ | .never => False
        | _ =>
          ptrSz = layout.size.bytes ∧
            0 < ptrSz ∧
            match resolveChildLayout body layout layoutIdx .none pointee with
            | .none => False
            | .some pointeeLayout =>
              pointeeLayout.isUninhabited = false ∧
                sigIsParamPlaceholder pointeeLayout = false ∧
                0 < pointeeLayout.align.bytes ∧
                p.offsetBytes % pointeeLayout.align.bytes = 0 ∧
                match sigLookupGlobalAlloc mem.globals p.allocId with
                | .some alloc =>
                  p.offsetBytes + pointeeLayout.size.bytes ≤ alloc.bytes.length
                | .none =>
                  match sigLookupBorrow mem.borrows p.allocId with
                  | .some entry =>
                    borrowPermAllowsRef refMut entry.perm = true ∧
                      match
                        entry.targetProjection,
                        Nat.beq p.offsetBytes 0,
                        sigGet? mem.callerLocals entry.targetLocal
                      with
                      | .nil, true, .some (.init targetVal) =>
                        valueMatchesRigidTyAndLayout
                          fuel'
                          body
                          pointee
                          (.some pointeeLayout)
                          layoutIdx
                          targetVal
                          mem
                      | _, _, _ =>
                        0 < entry.rangeLen ∧
                          p.offsetBytes + pointeeLayout.size.bytes ≤
                            entry.rangeOffset + entry.rangeLen
                  | .none => False
      | _ => False
  | fuel' + 1,
    body,
    kind,
    .some layout,
    layoutIdx,
    .aggregate vIdx fields,
    mem =>
    layout.isUninhabited = false ∧
      sigIsParamPlaceholder layout = false ∧
      let recTyPred := fun childKind childOptLayout childIdx childVal =>
        valueMatchesRigidTyAndLayout
          fuel' body childKind childOptLayout childIdx childVal mem
      match kind with
      | .fnDef _ _ =>
        layout.size.bytes = 0 ∧ vIdx = 0 ∧ fields = .nil
      | .ref refMut pointee =>
        vIdx = 0 ∧
          match fields with
          | .cons (.ptr p ptrSz) (.cons (.scalar len_sv) .nil) =>
            match pointee with
            | .slice elemKind =>
              let maxBytes := maxIsizeBytes body.layouts.pointerBits
              0 < ptrSz ∧
                len_sv.sizeBytes = ptrSz ∧
                ptrSz * 2 = layout.size.bytes ∧
                match
                  resolveChildLayout body layout layoutIdx .none elemKind
                with
                | .none => False
                | .some elemLayout =>
                  let sliceBytes := len_sv.bits * elemLayout.size.bytes
                  elemLayout.isUninhabited = false ∧
                    sigIsParamPlaceholder elemLayout = false ∧
                    0 < elemLayout.align.bytes ∧
                    p.offsetBytes % elemLayout.align.bytes = 0 ∧
                    sliceBytes ≤ maxBytes ∧
                    match sigLookupGlobalAlloc mem.globals p.allocId with
                    | .some alloc =>
                      p.offsetBytes + sliceBytes ≤ alloc.bytes.length
                    | .none =>
                      match sigLookupBorrow mem.borrows p.allocId with
                      | .some entry =>
                        borrowPermAllowsRef refMut entry.perm = true ∧
                          match sigGet? mem.callerLocals entry.targetLocal with
                          | .some (.init (.aggregate aggVar elems)) =>
                            match Nat.beq aggVar 0 with
                            | true =>
                              len_sv.bits ≤ elems.length ∧
                                p.offsetBytes + sliceBytes ≤
                                  elems.length * elemLayout.size.bytes ∧
                                arrayElemsMatchWith
                                  (fun e =>
                                    recTyPred
                                      elemKind (.some elemLayout) layoutIdx e)
                                  elems
                            | false =>
                              0 < entry.rangeLen ∧
                                p.offsetBytes + sliceBytes ≤
                                  entry.rangeOffset + entry.rangeLen
                          | _ =>
                            0 < entry.rangeLen ∧
                              p.offsetBytes + sliceBytes ≤
                                entry.rangeOffset + entry.rangeLen
                      | .none => False
            | .str =>
              0 < ptrSz ∧
                len_sv.sizeBytes = ptrSz ∧
                ptrSz * 2 = layout.size.bytes ∧
                len_sv.bits ≤ maxIsizeBytes body.layouts.pointerBits ∧
                match sigLookupGlobalAlloc mem.globals p.allocId with
                | .some alloc =>
                  p.offsetBytes + len_sv.bits ≤ alloc.bytes.length
                | .none =>
                  match sigLookupBorrow mem.borrows p.allocId with
                  | .some entry =>
                    borrowPermAllowsRef refMut entry.perm = true ∧
                      0 < entry.rangeLen ∧
                      p.offsetBytes + len_sv.bits ≤
                        entry.rangeOffset + entry.rangeLen
                  | .none => False
            | _ => False
          | _ => False
      | .rawPtr _ pointee =>
        vIdx = 0 ∧
          match pointee, fields with
          | .slice _, .cons ptrVal (.cons (.scalar meta_sv) .nil)
          | .str, .cons ptrVal (.cons (.scalar meta_sv) .nil)
          | .dynamic _, .cons ptrVal (.cons (.scalar meta_sv) .nil) =>
            0 < meta_sv.sizeBytes ∧
              meta_sv.sizeBytes * 2 = layout.size.bytes ∧
              meta_sv.bits < 2 ^ (meta_sv.sizeBytes * 8) ∧
              match ptrVal with
              | .ptr _ ptrSz => ptrSz = meta_sv.sizeBytes
              | .scalar addr_sv =>
                addr_sv.sizeBytes = meta_sv.sizeBytes ∧
                  addr_sv.bits < 2 ^ (addr_sv.sizeBytes * 8)
              | _ => False
          | _, _ => False
      | .array elemKind len =>
        vIdx = 0 ∧
          match
            resolveChildLayout body layout layoutIdx (.some 0) elemKind
          with
          | .none => False
          | .some elemLayout =>
            elemLayout.isUninhabited = false ∧
              sigIsParamPlaceholder elemLayout = false ∧
              match Nat.beq len 0 with
              | true => layout.size.bytes = 0 ∧ fields = .nil
              | false =>
                fields.length = len ∧
                  arrayElemsMatchWith
                    (fun e =>
                      recTyPred elemKind (.some elemLayout) layoutIdx e)
                    fields
      | .tuple fieldKinds =>
        vIdx = 0 ∧
          match fieldKinds with
          | .nil => layout.size.bytes = 0 ∧ fields = .nil
          | _ :: _ =>
            fields.length = fieldKinds.length ∧
              tupleFieldsMatchWith
                body layout layoutIdx recTyPred 0 fieldKinds fields
      | .closure _ upvarKinds =>
        vIdx = 0 ∧
          match upvarKinds with
          | .nil => layout.size.bytes = 0 ∧ fields = .nil
          | _ :: _ =>
            fields.length = upvarKinds.length ∧
              tupleFieldsMatchWith
                body layout layoutIdx recTyPred 0 upvarKinds fields
      | .adt _ adtArgs =>
        match layout.variants with
        | .empty => False
        | .single expectedVar =>
          match layout.fields with
          | .primitive => False
          | .arbitrary offsets _ =>
            match offsets with
            | .nil =>
              layout.size.bytes = 0 ∧ vIdx = expectedVar ∧ fields = .nil
            | _ :: _ =>
              vIdx = expectedVar ∧
                fields.length = offsets.length ∧
                adtFieldsMatchWith
                  fuel' body layout layoutIdx recTyPred mem 0 adtArgs fields
          | .array stride count =>
            match Nat.beq count 0 with
            | true =>
              layout.size.bytes = 0 ∧ vIdx = expectedVar ∧ fields = .nil
            | false =>
              vIdx = expectedVar ∧
                fields.length = count ∧
                adtArrayElemsMatchWith
                  fuel' body layout layoutIdx stride.bytes adtArgs recTyPred
                  mem fields
          | .union count =>
            0 < count ∧
              match fields with
              | .cons fVal .nil =>
                vIdx = expectedVar ∧
                  adtFieldsMatchWith
                    fuel' body layout layoutIdx recTyPred mem 0 adtArgs
                    (.cons fVal .nil)
              | _ => False
        | .multiple tag _ variantShapes =>
          vIdx < variantShapes.length ∧
            tagMatchesScalarLayout tag vIdx ∧
            match sigGet? variantShapes vIdx with
            | .some (.arbitrary varOffsets _) =>
              fields.length = varOffsets.length ∧
                adtFieldsMatchWith
                  fuel'
                  body
                  layout
                  layoutIdx
                  recTyPred
                  mem
                  0
                  (selectVariantTypeArgs vIdx variantShapes adtArgs)
                  fields
            | .some .primitive => fields = .nil
            | _ => False
      | _ => False

/--
Structurally validate `val` against `ty : Ty` and its `layoutIdx` entry in
`body.layouts` and `mem`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is undefined behavior to produce an invalid value of any type."
-/
@[reducible, simp]
def valueMatchesTyAndLayout
    (fuel : Nat)
    (body : CapturedMir)
    (ty : Ty)
    (layoutIdx : LayoutIdx)
    (val : Value)
    (mem : Memory) : Prop :=
  valueMatchesRigidTyAndLayout
    fuel body ty.kind (sigGet? body.layouts.entries layoutIdx) layoutIdx val mem

/--
Default structural recursion depth for `argsMatchSignature` and
`retMatchesSignature`.
-/
@[reducible, simp]
def defaultSignatureFuel : Nat := 8

/--
Recursively validate that each argument in `args` matches its corresponding
parameter `LocalDecl` in `decls` (`_1..=argCount`).
-/
@[reducible, simp]
def argsMatchSignatureAux
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (decls : List LocalDecl)
    (mem : Memory) : Prop :=
  match args, decls with
  | .nil, _ => True
  | .cons a restA, .cons d restD =>
    valueMatchesTyAndLayout fuel body d.ty d.ty.layoutIdx a mem ∧
      argsMatchSignatureAux fuel body restA restD mem
  | .cons _ _, .nil => False

/--
Verify that `args` has length `body.argCount` and that each argument `args[i]`
structurally matches parameter local `_{i+1}` (`body.localDecls[i+1]`) and its
`TypeLayout` in `mem`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L223-L234>

> "The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments, followed by any user-declared
> variables and temporaries."
-/
@[reducible, simp]
def argsMatchSignature
    (body : CapturedMir) (args : List Value) (mem : Memory) : Prop :=
  args.length = body.argCount ∧
    match body.localDecls with
    | .nil => False
    | .cons _ argDecls =>
      argsMatchSignatureAux defaultSignatureFuel body args argDecls mem

/--
Verify that return value `ret` structurally matches return local `_0`
`body.localDecls[0]` and its `TypeLayout` in `mem`.

Reference (`compiler/rustc_middle/src/mir/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/mod.rs#L223-L227>

> "The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments"
-/
@[reducible, simp]
def retMatchesSignature
    (body : CapturedMir) (ret : Value) (mem : Memory) : Prop :=
  match body.localDecls with
  | .nil => False
  | .cons retDecl _ =>
    valueMatchesTyAndLayout
      defaultSignatureFuel body retDecl.ty retDecl.ty.layoutIdx ret mem

/--
When `body.typeParamCount = 0`, any `typeArgs : TypeSubst` with
`typeArgs.length = body.typeParamCount` is equal to `.nil`.
-/
theorem typeSubst_eq_nil_of_length_eq_zero :
    ∀ (typeArgs : TypeSubst),
      typeArgs.length = 0 → typeArgs = .nil
  | .nil, _ => rfl
  | _ :: _, h => by cases h

/--
For a monomorphic `body` (`body.typeParamCount = 0`), instantiating `body` with
any `typeArgs` of length `body.typeParamCount` leaves `body` unchanged.
-/
@[simp]
theorem instantiate_eq_self_of_typeParamCount_zero
    (body : CapturedMir)
    (typeArgs : TypeSubst)
    (hZero : body.typeParamCount = 0)
    (hLen : typeArgs.length = body.typeParamCount) :
    body.instantiate typeArgs = body := by
  have hNil : typeArgs = .nil :=
    typeSubst_eq_nil_of_length_eq_zero typeArgs (Eq.trans hLen hZero)
  subst hNil
  exact CapturedMir.instantiate_nil body

/-- Fundamental coinductive interaction tree of `body` from `(args, mem)`. -/
def mirStatefulTree
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineStateWithMemory body args mem)

/-! ## 1. Stateless Partial-Correctness Claims (`Claim`, `VerificationResult`) -/

/--
Smyth `Partial` behavior of `body` on `args`, projected from `mirCallTree`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def MirExecPartial (body : CapturedMir) (args : List Value) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  (mirCallTree body args).toPartial

/--
Stateless partial contract separating `safetyPre` (`.defined`) from `pre` and
`post` (`.val`).
-/
def MirContractSpec
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop)
    (args : List Value) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) where
  defined := safetyPre args
  val _ outPair :=
    pre args →
      ∀ retVal mem', outPair.2 = .normal (retVal, mem') → post args retVal

/-- Pointwise Smyth refinement claim with separate `safetyPre` and `pre`. -/
def MirContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirExecPartial body ≤ MirContractSpec safetyPre pre post

/-- Pointwise Smyth refinement claim (`safetyPre := pre`). -/
def MirContractHolds
    (body : CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithSafety body pre pre post

/--
Companion boolean contract helper predicate: on `args`, `specBody` is `TreeSafe`
and every normal return yields `true` (`.scalar ⟨1, 1⟩`).

Reference (The Rust Reference, "Boolean type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>

> "The value false has the bit pattern 0x00 and the value true has the bit
> pattern 0x01. It is undefined behavior for an object with the boolean type to
> have any other bit pattern."
-/
def MirBoolPredicateHolds (specBody : CapturedMir) (args : List Value) : Prop :=
  MirContractHolds
    specBody
    (· = args)
    (fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 })

/-- Stateless verification claim for a captured Rust item. -/
structure Claim : Type 1 where
  body : CapturedMir
  pre : List Value → Prop
  post : List Value → Value → Prop

/-- Proposition denoted by `c : Claim`. -/
def Claim.holds (c : Claim) : Prop :=
  MirContractHolds c.body c.pre c.post

/-- Audited kernel verification certificate for `c : Claim`. -/
structure VerificationResult (c : Claim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its stateless contract. -/
class ItemSpec (defId : String) : Type 1 where
  pre : List Value → Prop := fun _ => True
  post : List Value → Value → Prop := fun _ _ => True

/-- Typeclass packaging a kernel-checked `VerificationResult c` for `defId`. -/
class ItemProof (defId : String) (c : Claim) : Prop where
  verified : VerificationResult c

/-! ## 2. Stateful Partial-Correctness Claims (`StatefulClaim`, `StatefulVerificationResult`) -/

/-- Smyth `Partial` stateful behavior projected from `mirStatefulTree`. -/
def MirStatefulExecPartial
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  (mirStatefulTree body args mem).toPartial

/-- Stateful partial contract separating `safetyPre` from `pre` and `post`. -/
def MirStatefulContractSpec
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) where
  defined := safetyPre args mem
  val _ outPair :=
    pre args mem →
      ∀ retVal mem',
        outPair.2 = .normal (retVal, mem') → post args mem retVal mem'

/-- Pointwise stateful Smyth refinement with separate `safetyPre` and `pre`. -/
def MirStatefulContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulExecPartial body ≤ MirStatefulContractSpec safetyPre pre post

/-- Pointwise stateful Smyth refinement (`safetyPre := pre`). -/
def MirStatefulContractHolds
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulContractHoldsWithSafety body pre pre post

/-- Stateful verification claim over `(args, mem)`. -/
structure StatefulClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop

/-- Proposition denoted by `c : StatefulClaim`. -/
def StatefulClaim.holds (c : StatefulClaim) : Prop :=
  MirStatefulContractHolds c.body c.pre c.post

/-- Audited kernel verification certificate for `c : StatefulClaim`. -/
structure StatefulVerificationResult (c : StatefulClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its stateful contract. -/
class StatefulItemSpec (defId : String) : Type 1 where
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `StatefulVerificationResult c` for `defId`. -/
class StatefulItemProof (defId : String) (c : StatefulClaim) : Prop where
  verified : StatefulVerificationResult c

/-! ## 3. Modular Rely–Guarantee Claims (`ModularClaim`, `ModularVerificationResult`) -/

/-- Closed MIR effect remaining once `MirCallE` is handled. -/
abbrev MirClosedEffect : Effect.{0} := SumE MirFailE MirObsE

/-- Handler interpreting external `MirCallReq` calls into `MirClosedEffect`. -/
abbrev ExternalCallHandler : Type :=
  MirCallReq → ITree MirClosedEffect MirCallAns

/-- Lift an `ExternalCallHandler` across `MirEffect`. -/
def handleMirExternalCalls (h : ExternalCallHandler) :
    (i : MirEffect.I) → ITree MirClosedEffect (MirEffect.O i)
  | .inl (.fail fk) => ITree.fail (E := MirClosedEffect) fk
  | .inr (.inl (.emit obs)) => ITree.emit (E := MirClosedEffect) obs
  | .inr (.inr (.call req)) => h req

/-- Interpret external calls in `mirStatefulTree body args mem` with `h`. -/
def mirHandledTree
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (h : ExternalCallHandler) :
    ITree MirClosedEffect MirOutcome :=
  ITree.interp (handleMirExternalCalls h) (mirStatefulTree body args mem)

/-- Contract specification over `MirClosedEffect`. -/
def MirClosedStatefulContractSpec
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirClosedEffect) × MirOutcome)) where
  defined := safetyPre args mem
  val _ outPair :=
    pre args mem →
      ∀ retVal mem',
        outPair.2 = .normal (retVal, mem') → post args mem retVal mem'

/-- Rely–guarantee call contract over `MirCallReq` and `MirCallAns`. -/
structure MirCallContract : Type where
  pre : MirCallReq → Prop := fun _ => True
  post : MirCallReq → MirCallAns → Prop := fun _ _ => True

/--
Semantic rely predicate stating that an `ExternalCallHandler` `h` implements
`C : MirCallContract` over `MirClosedEffect`: for every request satisfying
`C.pre req`, `h req` is `TreeSafe` and every normal return satisfies
`C.post req ans`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
def MirCallContract.holdsOn
    (C : MirCallContract) (h : ExternalCallHandler) : Prop :=
  ∀ req : MirCallReq,
    C.pre req →
    TreeSafe (h req) ∧
    ∀ tr ans, ReachesRet (h req) tr ans → C.post req ans

/-- Modular claim parameterized by an explicit rely predicate `envAssumed`. -/
structure ModularClaim : Type 1 where
  body : CapturedMir
  envAssumed : ExternalCallHandler → Prop
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop

/-- Proposition denoted by `c : ModularClaim`. -/
def ModularClaim.holds (c : ModularClaim) : Prop :=
  ∀ h : ExternalCallHandler,
    c.envAssumed h →
      (fun args mem => (mirHandledTree c.body args mem h).toPartial) ≤
        MirClosedStatefulContractSpec c.pre c.pre c.post

/-- Audited kernel verification certificate for `c : ModularClaim`. -/
structure ModularVerificationResult (c : ModularClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its modular contract. -/
class ModularItemSpec (defId : String) : Type 1 where
  envAssumed : ExternalCallHandler → Prop := fun _ => True
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `ModularVerificationResult c` for `defId`. -/
class ModularItemProof (defId : String) (c : ModularClaim) : Prop where
  verified : ModularVerificationResult c

/-! ## 4. Trace-Aware Claims (`TraceClaim`, `TraceVerificationResult`) -/

/-- Trace-aware contract predicating on completed `List (Event MirEffect)`. -/
def MirTraceContractSpec
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → List (Event MirEffect) → MirOutcome → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List (Event MirEffect) × MirOutcome)) where
  defined := pre args mem
  val _ outPair := post args mem outPair.1 outPair.2

/-- Trace-aware verification claim. -/
structure TraceClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → List (Event MirEffect) → MirOutcome → Prop

/-- Proposition denoted by `c : TraceClaim`. -/
def TraceClaim.holds (c : TraceClaim) : Prop :=
  MirStatefulExecPartial c.body ≤ MirTraceContractSpec c.pre c.post

/-- Audited kernel verification certificate for `c : TraceClaim`. -/
structure TraceVerificationResult (c : TraceClaim) : Prop where
  proof : c.holds

/-! ## 5. Total-Correctness Claims (`TotalClaim`, `TotalVerificationResult`) -/

/--
Total-correctness claim requiring UB-freedom (`TreeSafe`), reactive productivity
(`Productive`), absence of silent divergence (`¬ MayDiverge`), absence of
panics or aborts, and postcondition satisfaction on all returns.
-/
structure TotalClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop

/-- Proposition denoted by `c : TotalClaim`. -/
def TotalClaim.holds (c : TotalClaim) : Prop :=
  ∀ args mem,
    c.pre args mem →
      let t := mirStatefulTree c.body args mem
      TreeSafe t ∧
      Productive t ∧
      ¬ MayDiverge t ∧
      ∀ tr out,
        ReachesRet t tr out →
          ∃ retVal mem',
            out = .normal (retVal, mem') ∧ c.post args mem retVal mem'

/-- Audited kernel verification certificate for `c : TotalClaim`. -/
structure TotalVerificationResult (c : TotalClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its total-correctness contract. -/
class TotalItemSpec (defId : String) : Type 1 where
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `TotalVerificationResult c` for `defId`. -/
class TotalItemProof (defId : String) (c : TotalClaim) : Prop where
  verified : TotalVerificationResult c

/-! ## 6. Program-to-Program Behavioral Refinement Claims (`StatefulEquivClaim`, `StatefulEquivVerificationResult`) -/

/--
Effect handler silencing internal `MirObsE` (`switchInt` branch-tag step
observations) into `.ret PUnit.unit` while preserving all `MirFailE` faults
(undefined behavior, panics, and aborts) and unresolved external `MirCallE`
calls.

Silencing `MirObsE` compares programs by their external call/return behavior,
heap mutations, and UB/panic safety rather than internal CFG branching
structure (`switchInt`), matching Rust's observable-behavior equivalence model.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
def silenceMirObs : (i : MirEffect.I) → ITree MirEffect (MirEffect.O i)
  | .inl (.fail fk) => ITree.fail (E := MirEffect) fk
  | .inr (.inl _) => .ret PUnit.unit
  | .inr (.inr (.call req)) =>
    ITree.trigger (E := MirEffect) (.inr (.inr (.call req)))

/--
Branch-observation-erased stateful interaction tree of `body` from `(args, mem)`,
enabling Smyth `Partial` behavioral comparison across optimizations that alter
internal CFG branching structure (such as loop unrolling or word-lane
vectorization) while preserving external `MirCallE` events, memory outcomes, and
UB/panic faults.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1185-L1190>

> "Block ends with testing the value of an operand and jumping depending on its
> value."
-/
def mirObsErasedStatefulTree
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    ITree MirEffect MirOutcome :=
  ITree.interp silenceMirObs (mirStatefulTree body args mem)

/--
Pointwise Smyth behavioral refinement from candidate implementation `implBody`
to reference specification implementation `specBody` under `pre` over
branch-observation-erased execution (`mirObsErasedStatefulTree`): whenever
`pre args mem` holds and `specBody` is UB-free on `(args, mem)`, `implBody`
is also UB-free (`TreeSafe`) and every completed external-call trace and outcome
of `implBody` is permitted by `specBody`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
def RefinesStatefulMir
    (implBody specBody : CapturedMir)
    (pre : List Value → Memory → Prop) : Prop :=
  ∀ args mem,
    pre args mem →
      (mirObsErasedStatefulTree implBody args mem).toPartial ≤
        (mirObsErasedStatefulTree specBody args mem).toPartial

/--
Program-to-program total behavioral equivalence and refinement claim pairing a
candidate `implBody` (such as an `unsafe` optimization) against a frozen
reference `specBody` (such as an existing safe Rust implementation): under
`pre`, `implBody` satisfies total correctness (`TotalClaim.holds`: UB-free,
productive, non-divergent, non-panicking, and satisfying `post`) and refines
`specBody` in the Smyth `Partial` order (`RefinesStatefulMir`).
-/
structure StatefulEquivClaim : Type 1 where
  implBody : CapturedMir
  specBody : CapturedMir
  pre : List Value → Memory → Prop
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Proposition denoted by `c : StatefulEquivClaim`. -/
def StatefulEquivClaim.holds (c : StatefulEquivClaim) : Prop :=
  RefinesStatefulMir c.implBody c.specBody c.pre ∧
  ({ body := c.implBody, pre := c.pre, post := c.post } : TotalClaim).holds

/-- Audited kernel verification certificate for `c : StatefulEquivClaim`. -/
structure StatefulEquivVerificationResult (c : StatefulEquivClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its reference `specBody` and contract. -/
class StatefulEquivItemSpec (defId : String) : Type 1 where
  specBody : CapturedMir
  pre : List Value → Memory → Prop := fun _ _ => True
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `StatefulEquivVerificationResult c` for `defId`. -/
class StatefulEquivItemProof (defId : String) (c : StatefulEquivClaim) : Prop where
  verified : StatefulEquivVerificationResult c

/-! ## 7. Scoped UB-Exception Claims (`UbExceptionClaim`, `UbExceptionVerificationResult`) -/

/--
Scoped verification-exception claim for a captured Rust item that is known to
potentially exhibit undefined behavior outside a restricted subdomain
`strictSafetyPre` (for example, an intentional zero-copy `&[u8]` borrow over a
concurrently mutable hardware or pager VMO where `strictSafetyPre` requires the
VMO to be exclusively owned/trusted, while callers invoke it across a broader
precondition `pre`).

Unlike an unconstrained `axiom` asserting `StatefulVerificationResult` (which
would assert `TreeSafe` on inputs where `mirStatefulTree` deterministically
steps to `.fail .ub`, introducing `False` into the Lean kernel),
`UbExceptionClaim` is proved **constructively with zero axioms** by
establishing two obligations:
1. **Strict Safety on `pre ∧ strictSafetyPre`**: Under the restricted
   subdomain `c.pre args mem ∧ c.strictSafetyPre args mem`, `c.body` is
   completely UB-free (`TreeSafe`) and every normal return satisfies `c.post`
   (`MirStatefulContractHoldsWithSafety`).
2. **Normal-Return Postcondition Across All `pre`**: Across the full caller
   precondition `c.pre args mem` (even when `¬ c.strictSafetyPre args mem`
   and a UB fault may occur), every non-faulting normal return
   `ReachesRet (mirStatefulTree c.body args mem) tr (.normal (retVal, mem'))`
   still satisfies `c.post args mem retVal mem'` (and no `.fail .unsupported`
   is reached under `mirUbWaivedWP`).

`TrustedBoundary.lean` treats `UbExceptionVerificationResult` as an explicit
conditional verification exception (gated behind `--allow-assumptions` /
`--allow-ub-exceptions` and surfaced in the audit summary). Callers isolate
themselves from the exempted callee's potential `.fail .ub` by verifying
against `c.callContract.holdsOn` via `ModularVerificationResult` and linking
via `linkUbExceptionCallee`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "It is the programmer’s responsibility when writing unsafe code to ensure that
> any safe code interacting with the unsafe code cannot trigger these
> behaviors. unsafe code that satisfies this property for any safe client is
> called sound; if unsafe code can be misused by safe code to exhibit
> undefined behavior, it is unsound."
-/
structure UbExceptionClaim : Type 1 where
  body : CapturedMir
  pre : List Value → Memory → Prop
  strictSafetyPre : List Value → Memory → Prop := fun _ _ => False
  post : List Value → Memory → Value → Memory → Prop

/-- Proposition denoted by `c : UbExceptionClaim`. -/
def UbExceptionClaim.holds (c : UbExceptionClaim) : Prop :=
  MirStatefulContractHoldsWithSafety
    c.body
    (fun args mem => c.pre args mem ∧ c.strictSafetyPre args mem)
    c.pre
    c.post ∧
  ∀ args mem,
    c.pre args mem →
    ∀ tr retVal mem',
      ReachesRet (mirStatefulTree c.body args mem) tr (.normal (retVal, mem')) →
      c.post args mem retVal mem'

/--
Modular call contract exported by `c : UbExceptionClaim` to callers: callers
must establish `c.pre req.args req.memory` at the call site and may rely on
`c.post req.args req.memory retVal mem'` upon normal return.
-/
def UbExceptionClaim.callContract (c : UbExceptionClaim) : MirCallContract where
  pre req := req.defPath = c.body.defPath ∧ c.pre req.args req.memory
  post req ans :=
    ∃ retVal mem',
      ans = .returned retVal mem' ∧
      c.post req.args req.memory retVal mem'

/-- Audited kernel verification certificate for `c : UbExceptionClaim`. -/
structure UbExceptionVerificationResult (c : UbExceptionClaim) : Prop where
  proof : c.holds

/-- Typeclass associating Rust item `defId` with its scoped UB-exception contract. -/
class UbExceptionItemSpec (defId : String) : Type 1 where
  pre : List Value → Memory → Prop := fun _ _ => True
  strictSafetyPre : List Value → Memory → Prop := fun _ _ => False
  post : List Value → Memory → Value → Memory → Prop := fun _ _ _ _ => True

/-- Typeclass packaging a `UbExceptionVerificationResult c` for `defId`. -/
class UbExceptionItemProof (defId : String) (c : UbExceptionClaim) : Prop where
  verified : UbExceptionVerificationResult c

/-! ## 8. Specification Non-Vacuity Obligations (`NonVacuousPre`, `NonVacuousStatefulPre`) -/

/-- Witness obligation asserting that a stateless precondition `pre` is satisfiable. -/
def NonVacuousPre (pre : List Value → Prop) : Prop :=
  ∃ args, pre args

/-- Witness obligation asserting that a stateful precondition `pre` is satisfiable. -/
def NonVacuousStatefulPre (pre : List Value → Memory → Prop) : Prop :=
  ∃ args mem, pre args mem

/-! ## 9. Whole-Crate Verification Rollup (`CrateItemEntry`, `CrateClaim`, `CrateVerificationResult`) -/

/-- Per-item entry in a whole-crate verification rollup manifest. -/
structure CrateItemEntry : Type 1 where
  /-- Cryptographic and toolchain identity of the captured Rust item. -/
  identity : ArtifactIdentity
  /-- Kernel-checked per-item verification certificate proposition (`Verify.<Item>.verified`'s type). -/
  certificate : Prop

/-- Whole-crate claim bundling every captured Rust item in a compilation unit. -/
structure CrateClaim : Type 1 where
  /-- Crate name recorded by `rustc-capture` in `CaptureManifest.json`. -/
  crateName : String
  /-- Recorded MIR dialect tag (e.g., `"V2026_06_01"`). -/
  mirDialect : String
  /-- Exhaustive list of captured Rust items and their verification certificates. -/
  items : List CrateItemEntry

/-- Conjunction asserting that every `CrateItemEntry` certificate in `items` holds. -/
def AllCrateItemsHold : List CrateItemEntry → Prop
  | [] => True
  | item :: rest => item.certificate ∧ AllCrateItemsHold rest

/-- Proposition denoted by `c : CrateClaim`: the crate has at least one
verified item and every captured item's kernel certificate holds. -/
def CrateClaim.holds (c : CrateClaim) : Prop :=
  c.items ≠ [] ∧ AllCrateItemsHold c.items

/-- Audited whole-crate verification certificate checked by `TrustedBoundary.lean`. -/
structure CrateVerificationResult (c : CrateClaim) : Prop where
  proof : c.holds

/--
Package a universally quantified polymorphic item proof `h : P` into an
audited `CrateVerificationResult` certificate for `Verify.<Item>.verified`.
-/
theorem mkPolyVerificationResult
    (id : ArtifactIdentity)
    {P : Prop}
    (h : P) :
    CrateVerificationResult
      { crateName := id.defPath
        mirDialect := id.mirDialect
        items := [{ identity := id, certificate := P }] } :=
  { proof := And.intro (by intro hc; nomatch hc) (And.intro h True.intro) }

end Trusted.VerificationResult
