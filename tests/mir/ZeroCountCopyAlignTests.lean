/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted

/-!
# Zero-byte `copy_nonoverlapping` alignment, validity, and overflow guard

Kernel-checked (`rfl`) regression tests for the hardened
`evalCopyNonOverlappingWithCount` (statement form `NonDivergingIntrinsic.copyNonOverlapping`
and, through `Terminators.evalCopyNonOverlappingCall`, the call form
`copy_nonoverlapping::<T>`) in **both** `Trusted.Rustc.V2026_06_01` and
`Trusted.Rustc.V2026_08_01`. Every fixture below is elaborated once per snapshot (§1
`V2026_06_01`, §2 `V2026_08_01`) from the same source text.

Ground truth (`library/core/src/ptr/mod.rs` at `rust-lang/rust`
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`): `src`/`dst` must be valid for
`count * size_of::<T>()` bytes "or that number must be 0", and "even if the effectively
copied size (`count * size_of::<T>()`) is `0`, the pointers must be properly aligned".
So on the zero-byte fragment aligned null and aligned dangling pointers are accepted
(no access), misaligned or malformed pointer values are undefined behavior, and an
undetermined alignment fails closed (`.unsupported`).

Covered cases (per snapshot): live aligned `count = 0`; `NonNull::dangling()`
`count = 0`; aligned null `count = 0` and ZST `count > 0`; non-zero null `.ub`;
misaligned live (`offset = 1`, including the `copyMisalignedZeroBody` statement shape)
and misaligned dangling (`addr = 9`) `.ub`; `Value.uninit` (`V2026_06_01` only),
wrong-width scalar/pointer, `.unit`, `.aggregate`, statically non-pointer operand,
out-of-range `count` bits `.ub`; aligned/misaligned ZST `[u64; 0]` with `count = 5`;
`count * size_of::<T>() > isize::MAX` overflow (including the wide pointer
`*const (u8, [u8])`); unresolved/opaque ADT `.unsupported` and Kleene
`.unsupported ∧₃ .ub = .ub`; packed-field misalignment `.ub`, packed-field plus offset
aligned pass, unlaid-out `(u128, u128)` / 32-bit `(u32, u32)` tuples (no false `.ub`),
`10^10` offsets; pre-monomorphization placeholder layouts (`Wrapper<T>`, `[T; 4]`,
depth-9 nesting, depth-16 truncation) `.unsupported` while monomorphized
`Wrapper<u64>` resolves; dead stack borrow with `align > 1` `.unsupported`; and the
terminator path `Terminators.evalCopyNonOverlappingCall` in both snapshots. §3 audits
the axioms of every test.
-/

/-! ## §1. `V2026_06_01` -/

namespace Anneal.Tests.ZeroCountCopyAlign.V06

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### Universal characterizations -/

/-- Every zero-byte copy (`count * size_of::<T>() = 0`, here a zero-sized `T` with any `count`)
whose pointers pass the zero-byte precondition is a pure no-op. -/
theorem zst_any_count_noop_univ (s : MachineState) (src dst : Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (sv dv : Value) (count : Nat) (l3 : List LocalSlot) (al : Nat)
    (hElem : resolveCopyElemLayout ld ly src dst = .ok 0 al)
    (hPre : zeroByteCopyPrecheck s l3 ld ly al sv dv = .ok)
    (hCnt : count < scalarModulus (layoutPointerBytes ly)) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv count l3 =
      MirStepNode.step (advanceStmt s l3) := by
  have h0 : Nat.mul count 0 = 0 := Nat.mul_zero count
  have hRange : Bool.or (Nat.beq count 0)
      (Nat.blt count (scalarModulus (layoutPointerBytes ly))) = true := by
    simp [Nat.blt_eq.mpr hCnt]
  unfold evalCopyNonOverlappingWithCount
  simp only [hRange, hElem, h0, hPre]
  all_goals rfl

/-- A definitely violated zero-byte precondition on either pointer is `.ub` for `count = 0`,
whatever the other pointer is (Kleene strong conjunction). -/
theorem zero_count_src_violation_ub_univ (s : MachineState) (src dst : Operand)
    (ld : List LocalDecl) (ly : LayoutTable) (sv dv : Value) (l3 : List LocalSlot) (sz al : Nat)
    (hElem : resolveCopyElemLayout ld ly src dst = .ok sz al)
    (hSrc : checkZeroCountCopyPtr s l3 ld ly al sv = .ub) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv 0 l3 = MirStepNode.fail .ub := by
  have h0 : Nat.mul 0 sz = 0 := Nat.zero_mul sz
  unfold evalCopyNonOverlappingWithCount
  simp only [hElem, h0, zeroByteCopyPrecheck, hSrc, ZeroCheck.both]
  all_goals rfl

theorem zero_count_dst_violation_ub_univ (s : MachineState) (src dst : Operand)
    (ld : List LocalDecl) (ly : LayoutTable) (sv dv : Value) (l3 : List LocalSlot) (sz al : Nat)
    (hElem : resolveCopyElemLayout ld ly src dst = .ok sz al)
    (hDst : checkZeroCountCopyPtr s l3 ld ly al dv = .ub) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv 0 l3 = MirStepNode.fail .ub := by
  have h0 : Nat.mul 0 sz = 0 := Nat.zero_mul sz
  unfold evalCopyNonOverlappingWithCount
  simp only [hElem, h0, zeroByteCopyPrecheck, hDst]
  cases checkZeroCountCopyPtr s l3 ld ly al sv <;> rfl

/-- A non-thin-pointer argument value is `.ub` at every count and every element layout. -/
theorem malformed_src_ub_univ (s : MachineState) (src dst : Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (dv : Value) (count : Nat) (l3 : List LocalSlot) :
    evalCopyNonOverlappingWithCount s src dst ld ly .unit dv count l3 = MirStepNode.fail .ub := by
  unfold evalCopyNonOverlappingWithCount
  repeat' (first | rfl | (dsimp only) | split)

/-- An unresolved element layout with `count ≠ 0` and two thin pointer values delegates to the
unchanged non-zero-byte implementation. -/
theorem unresolved_nonzero_delegates_univ (s : MachineState) (src dst : Operand)
    (ld : List LocalDecl) (ly : LayoutTable) (sp dp : ProvenancePtr) (count : Nat)
    (l3 : List LocalSlot) (hElem : resolveCopyElemLayout ld ly src dst = .unsupported)
    (hC : Nat.beq count 0 = false) (hCnt : count < scalarModulus (layoutPointerBytes ly)) :
    evalCopyNonOverlappingWithCount s src dst ld ly (.ptr sp (layoutPointerBytes ly))
        (.ptr dp (layoutPointerBytes ly)) count l3 =
      evalCopyNonOverlappingWithCountNonZero s src dst ld ly (.ptr sp (layoutPointerBytes ly))
        (.ptr dp (layoutPointerBytes ly)) count l3 := by
  unfold evalCopyNonOverlappingWithCount
  simp [hElem, hC, isThinPtrValue, Nat.blt_eq.mpr hCnt]

/-- A `count` whose bits are not a `usize` bit pattern is `.ub` at every element layout
(even for a zero-sized `T`, where `count * size_of::<T>() = 0`). -/
theorem out_of_range_count_ub_univ (s : MachineState) (src dst : Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (sv dv : Value) (count : Nat) (l3 : List LocalSlot)
    (hCnt : scalarModulus (layoutPointerBytes ly) ≤ count) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv count l3 = MirStepNode.fail .ub := by
  have hPos : 0 < scalarModulus (layoutPointerBytes ly) := by
    generalize layoutPointerBytes ly = k
    induction k with
    | zero => exact Nat.one_pos
    | succ k ih => exact Nat.mul_pos (by decide) ih
  have hRange : Bool.or (Nat.beq count 0)
      (Nat.blt count (scalarModulus (layoutPointerBytes ly))) = false := by
    have h1 : count ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le hPos hCnt)
    have h2 : ¬ count < scalarModulus (layoutPointerBytes ly) := Nat.not_lt.mpr hCnt
    have e1 : Nat.beq count 0 = false :=
      Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
    have e2 : Nat.blt count (scalarModulus (layoutPointerBytes ly)) = false :=
      Bool.eq_false_iff.mpr (fun h => h2 (Nat.blt_eq.mp h))
    rw [e1, e2]
    rfl
  unfold evalCopyNonOverlappingWithCount
  simp only [hRange]

/-! ### Fixtures -/

/-- A type with layout index `i`. -/
def ty (k : RigidTy) (i : Nat := 0) : Ty := { kind := k, layoutIdx := i }
/-- A mutable local declaration. -/
def decl (k : RigidTy) (i : Nat := 0) : LocalDecl :=
  { mutability := .mut, ty := ty k i, debugName := none }
/-- `*mut T`. -/
def ptrK (k : RigidTy) : RigidTy := .rawPtr .mut k
/-- A local place. -/
def loc (i : Nat) (proj : List ProjectionElem := []) : Place := { local_ := i, projection := proj }
/-- `copy _i`. -/
def cp (i : Nat) : Operand := .copy (loc i)
/-- A `usize` constant (`sizeBytes` overridable for malformed counts). -/
def usz (n : Nat) (w : Nat := 8) : Operand :=
  .constant { ty := ty (.uint .usize), val := .scalar (.int ⟨n, w⟩) }

/-- A plain memory-backed layout. -/
def lay (sz al : Nat) (f : FieldsShape) (fl : List Nat := []) : TypeLayout :=
  { size := ⟨sz⟩, align := ⟨al⟩, backendRepr := .memory, fields := f, variants := .single 0,
    isUninhabited := false, fieldLayouts := fl }
/-- A thin pointer layout whose single `fieldLayouts` entry names the pointee layout. -/
def ptrLay (w pointee : Nat) : TypeLayout :=
  { size := ⟨w⟩, align := ⟨w⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 2 ^ (8 * w) - 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false,
    fieldLayouts := [pointee] }

/-- `T` (generic parameter). -/
def paramT : RigidTy := .param 0 "T"
/-- `[u64; 0]`. -/
def arrU64x0 : RigidTy := .array (.uint .u64) 0
/-- Opaque ADT without a layout. -/
def opaqueK : RigidTy := .adt "zc::Opaque" []
/-- `Wrapper<T>`. -/
def wrapT : RigidTy := .adt "zc::Wrapper" [paramT]
/-- `[T; 4]`. -/
def arrT4 : RigidTy := .array paramT 4
/-- A generic struct nested `≥ 16` deep (truncated template). -/
def truncK : RigidTy := .adt "zc::Deep" [paramT]
/-- `Wrapper<u64>`. -/
def wrapU64 : RigidTy := .adt "zc::Wrapper" [.uint .u64]
/-- `#[repr(packed)] struct Packed { a: u8, b: u64 }`. -/
def packedK : RigidTy := .adt "zc::Packed" []
/-- `#[repr(C)] struct Outer { p: Packed }` (align 8). -/
def outerK : RigidTy := .adt "zc::Outer" []
/-- `(u128, u128)`. -/
def u128Pair : RigidTy := .tuple [.uint .u128, .uint .u128]
/-- `*const (u8, [u8])` (a wide pointer). -/
def widePtrK : RigidTy := .rawPtr .not (.tuple [.uint .u8, .slice (.uint .u8)])
/-- `[[…[T; 1]…; 1]; 1]` nested `n` deep. -/
def nestT : Nat → RigidTy
  | 0 => paramT
  | n + 1 => .array (nestT n) 1

/-- Placeholder-chain layouts for `nestT`: entry `base + k` is `[nestT k; 1]`. -/
def nestLays (base : Nat) : Nat → List TypeLayout
  | 0 => []
  | n + 1 => nestLays base n ++ [lay 0 1 (.array ⟨0⟩ 1) [if n = 0 then 2 else base + n - 1]]

/-- The 64-bit layout table (entry `0` is the unit layout, as in `rustc-capture`). -/
def L64 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])                         -- 0: ()
      , lay 8 8 .primitive                                -- 1: u64
      , lay 0 1 .primitive                                -- 2: placeholder `T`
      , lay 0 1 (.arbitrary [⟨0⟩] [0]) [2]                -- 3: Wrapper<T> template
      , lay 0 1 (.array ⟨0⟩ 4) [2]                        -- 4: [T; 4] template
      , lay 0 1 (.arbitrary [⟨0⟩] [0])                    -- 5: truncated depth-16 template
      , lay 8 8 (.arbitrary [⟨0⟩] [0]) [1]                -- 6: Wrapper<u64>
      , ptrLay 8 3                                        -- 7: *mut Wrapper<T>
      , ptrLay 8 4                                        -- 8: *mut [T; 4]
      , ptrLay 8 5                                        -- 9: *mut Deep<T>
      , ptrLay 8 6                                        -- 10: *mut Wrapper<u64>
      , lay 9 1 (.arbitrary [⟨0⟩, ⟨1⟩] [0, 1]) [12, 1]   -- 11: Packed
      , lay 1 1 .primitive                                -- 12: u8
      , lay 16 8 (.arbitrary [⟨0⟩] [0]) [11]              -- 13: Outer
      , lay 16 16 .primitive                              -- 14: u128 (x86_64)
      , ptrLay 8 14                                       -- 15: *mut u128
      , ptrLay 8 24 ] ++                                  -- 16: *mut nestT 9
      nestLays 17 9 }                                    -- 17..25: nestT 1 ..= nestT 9

/-- Local declarations of the 64-bit fixture body. -/
def D64 : List LocalDecl :=
  [ decl (.tuple []) 0                 -- _0
  , decl (.uint .u64) 1                -- _1 : u64
  , decl (ptrK (.uint .u64))           -- _2 : *mut u64
  , decl (ptrK (.uint .u64))           -- _3 : *mut u64
  , decl (ptrK arrU64x0)               -- _4 : *mut [u64; 0]
  , decl (ptrK opaqueK)                -- _5 : *mut Opaque
  , decl (ptrK wrapT) 7                -- _6 : *mut Wrapper<T>
  , decl (ptrK arrT4) 8                -- _7 : *mut [T; 4]
  , decl (ptrK truncK) 9               -- _8 : *mut Deep<T>
  , decl (ptrK wrapU64) 10             -- _9 : *mut Wrapper<u64>
  , decl outerK 13                     -- _10 : Outer
  , decl u128Pair 99                   -- _11 : (u128, u128) (no layout entry)
  , decl (ptrK (.uint .u128)) 15       -- _12 : *mut u128
  , decl (ptrK widePtrK)               -- _13 : *mut *const (u8, [u8])
  , decl (.uint .u32)                  -- _14 : u32
  , decl (ptrK (nestT 9)) 16           -- _15 : *mut nestT 9
  , decl packedK 11                    -- _16 : Packed
  ]

/-- Frame locals (every local live). -/
def locals64 : List LocalSlot :=
  [ .uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit
  , .uninit, .uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 8⟩]])
  , .init (.aggregate 0 [.scalar ⟨1, 16⟩, .scalar ⟨2, 16⟩]), .uninit, .uninit, .uninit, .uninit
  , .init (.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 8⟩]) ]

/-- A borrow entry with tag `t` on local `l` at projection `proj`. -/
def bor (t l : Nat) (proj : List ProjectionElem := []) (dead : Bool := false)
    (perm : TreeBorrowPerm := .unique) : BorrowEntry :=
  { tag := t, targetLocal := l, targetProjection := proj, perm := perm,
    targetFrameDepth := 0, allocDead := dead }

/-- Borrow table: `1 ↦ _1`, `2 ↦ dead _1`, `3 ↦ _10.p.b`, `4 ↦ _11.0`, `5 ↦ _16.b`,
`6 ↦ _1` (`.disabled` but live). -/
def B64 : List BorrowEntry :=
  [ bor 1 1
  , bor 2 1 [] true .disabled
  , bor 3 10 [.field 0 (ty packedK 11), .field 1 (ty (.uint .u64) 1)]
  , bor 4 11 [.field 0 (ty (.uint .u128) 14)]
  , bor 5 16 [.field 1 (ty (.uint .u64) 1)]
  , bor 6 1 [] false .disabled ]

/-- The 64-bit fixture machine state. -/
def S64 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals64 },
    memory := { emptyMemory with borrows := B64, nextTag := 7 } }

/-- Pointer value with provenance tag `t` at byte offset `off`. -/
def pv (t off : Nat) (w : Nat := 8) : Value := .ptr ⟨t, off⟩ w
/-- Integer address `a` (`NonNull::dangling()`, null, or misaligned). -/
def av (a : Nat) (w : Nat := 8) : Value := .scalar ⟨a, w⟩

/-- `copy_nonoverlapping` statement-level evaluation with pre-resolved count bits. -/
def run (src dst : Nat) (sv dv : Value) (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCount S64 (cp src) (cp dst) D64 L64 sv dv count locals64

/-- Success: the zero-byte copy is a pure no-op. -/
def noop : MirStepNode := MirStepNode.step (advanceStmt S64 locals64)

/-! ### Live aligned, dangling, and null pointers on the zero-byte fragment -/

theorem live_aligned_count0_noop : run 2 3 (pv 1 0) (pv 1 0) 0 = noop := rfl
theorem live_disabled_tag_count0_noop : run 2 3 (pv 6 0) (pv 1 0) 0 = noop := rfl
theorem dangling_count0_noop : run 2 3 (av 8) (av 8) 0 = noop := rfl
theorem dangling_large_count0_noop : run 2 3 (av 0x7ff8) (av 4096) 0 = noop := rfl
theorem null_count0_noop : run 2 3 (av 0) (av 0) 0 = noop := rfl
theorem null_unbacked_ptr_count0_noop : run 2 3 (pv 0 0) (av 0) 0 = noop := rfl
theorem null_zst_count5_noop : run 4 4 (av 0) (av 0) 5 = noop := rfl
theorem nonzero_null_u64_ub : run 2 3 (av 0) (av 0) 1 = MirStepNode.fail .ub := rfl
theorem nonzero_null_dst_ub : run 2 3 (pv 1 0) (av 0) 1 = MirStepNode.fail .ub := rfl

/-! ### Misalignment -/

theorem misaligned_live_offset1_ub : run 2 3 (pv 1 1) (pv 1 0) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_live_dst_offset1_ub : run 2 3 (pv 1 0) (pv 1 1) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_dangling_9_ub : run 2 3 (av 9) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_unbacked_ptr_ub : run 2 3 (pv 0 9) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_fnptr_like_ub : run 2 3 (pv 77 3) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem unbacked_aligned_unsupported : run 2 3 (pv 77 8) (av 8) 0 = MirStepNode.unsupported := rfl

/-- `copyMisalignedZeroBody` shape: `_2 = &raw mut _1; _2 = (_2 as *mut u8).offset(1) as
*mut u64; copy_nonoverlapping(copy _2, copy _2, 0)`, executed through the statement-level
`evalStmt` (count operand evaluated and range-checked). -/
def misalignedS : MachineState :=
  { S64 with frame := { S64.frame with locals := locals64.set 2 (.init (pv 1 1)) } }

theorem copyMisalignedZeroBody_shape_ub :
    evalStmt misalignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz 0)), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.fail .ub := rfl

/-- The aligned counterpart of `copyMisalignedZeroBody` steps. -/
def alignedS : MachineState :=
  { S64 with frame := { S64.frame with locals := locals64.set 2 (.init (pv 1 0)) } }

theorem copyAlignedZeroBody_shape_noop :
    evalStmt alignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz 0)), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.step (advanceStmt alignedS alignedS.frame.locals) := rfl

/-! ### Malformed pointer values and ill-typed operands -/

theorem uninit_value_ub : run 2 3 .uninit (av 8) 0 = MirStepNode.fail .ub := rfl
theorem uninit_dst_value_ub : run 2 3 (av 8) .uninit 0 = MirStepNode.fail .ub := rfl

theorem wrong_width_scalar_ub : run 2 3 (av 8 4) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem out_of_range_scalar_ub : run 2 3 (av (2 ^ 64)) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem wrong_width_ptr_ub : run 2 3 (pv 1 0 4) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem wrong_width_ptr_nonzero_ub : run 2 3 (pv 1 0 4) (pv 1 0) 1 = MirStepNode.fail .ub := rfl
theorem unit_value_ub : run 2 3 .unit (av 8) 0 = MirStepNode.fail .ub := rfl
theorem aggregate_value_ub : run 2 3 (av 8) (.aggregate 0 []) 0 = MirStepNode.fail .ub := rfl
theorem nonptr_operand_ub : run 14 3 (av 8) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem nonptr_operand_nonzero_ub : run 2 14 (pv 1 0) (pv 1 0) 3 = MirStepNode.fail .ub := rfl
theorem out_of_range_count_bits_ub :
    evalStmt alignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz (2 ^ 64))), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.fail .ub := rfl
theorem wrong_width_count_ub :
    evalStmt alignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz 0 4)), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.fail .ub := rfl

/-! ### Zero-sized element types -/

theorem resolve_arrU64x0 : resolveCopyElemLayout D64 L64 (cp 4) (cp 4) = .ok 0 8 := rfl
theorem zst_aligned_count5_noop : run 4 4 (av 16) (av 8) 5 = noop := rfl
theorem zst_misaligned_count5_ub : run 4 4 (av 16) (av 4) 5 = MirStepNode.fail .ub := rfl
theorem zst_dead_borrow_count5_unsupported : run 4 4 (pv 2 0) (av 8) 5 = MirStepNode.unsupported := rfl
theorem zst_out_of_range_count_ub : run 4 4 (av 8) (av 8) (2 ^ 64) = MirStepNode.fail .ub := rfl
/-- The call form only checks the `count` scalar's width; the out-of-range bits of a
zero-sized-`T` call are still `.ub` (`evalCopyNonOverlappingWithCount` step 0). -/
theorem call_zst_out_of_range_count_ub :
    evalCopyNonOverlappingCall S64 D64 L64 [cp 4, cp 4, usz 0] [av 8, av 8, .scalar ⟨2 ^ 64, 8⟩]
      locals64 (loc 0) 1 = MirStepNode.fail .ub := rfl

/-! ### `count * size_of::<T>() ≤ isize::MAX` -/

theorem overflow_u64_ub : run 2 3 (pv 1 0) (pv 1 0) (2 ^ 60) = MirStepNode.fail .ub := rfl
theorem overflow_u64_null_ub : run 2 3 (av 0) (av 0) (2 ^ 62) = MirStepNode.fail .ub := rfl
theorem resolve_widePtr : resolveCopyElemLayout D64 L64 (cp 13) (cp 13) = .ok 16 8 := rfl
theorem overflow_widePtr_ub : run 13 13 (av 8) (av 8) (2 ^ 59) = MirStepNode.fail .ub := rfl
theorem widePtr_count0_noop : run 13 13 (av 8) (av 8) 0 = noop := rfl

/-! ### Undetermined layouts and Kleene conjunction -/

theorem opaque_unresolved : resolveCopyElemLayout D64 L64 (cp 5) (cp 5) = .unsupported := rfl
theorem opaque_count0_unsupported : run 5 5 (av 9) (av 0) 0 = MirStepNode.unsupported := rfl
theorem opaque_count0_malformed_ub : run 5 5 (av 8) .unit 0 = MirStepNode.fail .ub := rfl
theorem kleene_unsupported_and_ub : ZeroCheck.both .unsupported .ub = .ub := rfl
theorem kleene_ub_and_unsupported : ZeroCheck.both .ub .unsupported = .ub := rfl
theorem kleene_unsupported_and_ok : ZeroCheck.both .unsupported .ok = .unsupported := rfl
theorem kleene_dead_src_misaligned_dst_ub : run 2 3 (pv 2 0) (av 9) 0 = MirStepNode.fail .ub := rfl
theorem kleene_misaligned_src_dead_dst_ub : run 2 3 (av 9) (pv 2 0) 0 = MirStepNode.fail .ub := rfl
theorem dead_borrow_align8_unsupported : run 2 3 (pv 2 0) (av 8) 0 = MirStepNode.unsupported := rfl

/-! ### Place-alignment bounds (packed fields, unlaid-out tuples, large offsets) -/

theorem packed_field_misaligned_ub : run 2 3 (pv 5 0) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem packed_field_plus7_in_outer_noop : run 2 3 (pv 3 7) (av 8) 0 = noop := rfl
theorem packed_field_in_outer_misaligned_ub : run 2 3 (pv 3 0) (av 8) 0 = MirStepNode.fail .ub := rfl
/-- `(u128, u128)` without a layout entry is `.atLeast 8` on 64-bit, so `&raw mut x.0` at
offset `0` is undetermined (never a false `.ub`) while odd offset `+3` (`3 % 8 ≠ 0`) is `.ub`. -/
theorem u128_tuple_field_no_false_ub : run 12 12 (pv 4 0) (av 16) 0 = MirStepNode.unsupported := rfl
theorem u128_tuple_field_odd_offset_ub :
    run 12 12 (pv 4 3) (av 16) 0 = MirStepNode.fail .ub := rfl
theorem large_offset_aligned_noop : run 2 3 (pv 1 (10 ^ 10)) (av 8) 0 = noop := rfl
theorem large_offset_misaligned_ub : run 2 3 (pv 1 (10 ^ 10 + 3)) (av 8) 0 = MirStepNode.fail .ub := rfl

/-! ### Pre-monomorphization placeholder layouts -/

theorem placeholder_wrapper_unresolved :
    resolveCopyElemLayout D64 L64 (cp 6) (cp 6) = .unsupported := rfl
theorem placeholder_wrapper_count0_unsupported :
    run 6 6 (pv 1 0) (pv 1 0) 0 = MirStepNode.unsupported := rfl
theorem placeholder_wrapper_count5_not_noop :
    run 6 6 (av 1) (av 1) 5 = MirStepNode.fail .ub := rfl
theorem placeholder_array_unresolved :
    resolveCopyElemLayout D64 L64 (cp 7) (cp 7) = .unsupported := rfl
theorem placeholder_truncated_unresolved :
    resolveCopyElemLayout D64 L64 (cp 8) (cp 8) = .unsupported := rfl
theorem placeholder_nested9_unresolved :
    resolveCopyElemLayout D64 L64 (cp 15) (cp 15) = .unsupported := rfl
theorem monomorphized_wrapper_resolves :
    resolveCopyElemLayout D64 L64 (cp 9) (cp 9) = .ok 8 8 := rfl
theorem monomorphized_wrapper_misaligned_ub : run 9 9 (av 4) (av 8) 0 = MirStepNode.fail .ub := rfl

/-! ### 32-bit target -/

/-- 32-bit table: `0 ↦ ()`, `1 ↦ u32`, `2 ↦ *mut u32` (pointee `1`). -/
def L32 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true,
    entries := [lay 0 1 (.arbitrary [] []), lay 4 4 .primitive, ptrLay 4 1] }

/-- `_0 : ()`, `_1 : (u32, u32)` (no layout), `_2 : *mut u32`, `_3 : u32`. -/
def D32 : List LocalDecl :=
  [decl (.tuple []) 0, decl (.tuple [.uint .u32, .uint .u32]) 99, decl (ptrK (.uint .u32)) 2,
   decl (.uint .u32) 1]

/-- 32-bit frame locals. -/
def locals32 : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]), .uninit, .init (.scalar ⟨3, 4⟩)]

/-- 32-bit state: borrows `1 ↦ _1.0`, `2 ↦ _3`. -/
def S32 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals32 },
    memory := { emptyMemory with
      borrows := [bor 1 1 [.field 0 (ty (.uint .u32) 1)], bor 2 3], nextTag := 3 } }

theorem target32_resolve_u32 : resolveCopyElemLayout D32 L32 (cp 2) (cp 2) = .ok 4 4 := rfl
/-- The unlaid-out `(u32, u32)` root is `.atLeast 4` (its fields' declared `u32` layout), so
`&raw mut x.0` is aligned in every execution (no false `.ub`) ... -/
theorem target32_u32_tuple_field_aligned_noop :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 1 0 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.step (advanceStmt S32 S32.frame.locals) := rfl
/-- ... and `(&raw mut x.0).byte_add(1)` is misaligned in every execution. -/
theorem target32_u32_tuple_field_odd_offset_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 1 1 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl
theorem target32_decl_u32_aligned_noop :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 2 0 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.step (advanceStmt S32 S32.frame.locals) := rfl
theorem target32_decl_u32_misaligned_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 2 2 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl
theorem target32_8byte_ptr_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (av 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl
theorem target32_overflow_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (av 4 4) (av 4 4) (2 ^ 29)
      S32.frame.locals = MirStepNode.fail .ub := rfl

/-! ### Terminator path (`copy_nonoverlapping::<T>` call) -/

/-- The call form at `count = n` with argument values `sv`, `dv`. -/
def runCall (sv dv : Value) (n : Nat) : MirStepNode :=
  evalCopyNonOverlappingCall S64 D64 L64 [cp 2, cp 3, usz n] [sv, dv, .scalar ⟨n, 8⟩] locals64
    (loc 0) 1

theorem call_misaligned_count0_ub : runCall (pv 1 1) (pv 1 0) 0 = MirStepNode.fail .ub := rfl
theorem call_misaligned_dangling_count0_ub : runCall (av 9) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem call_malformed_count0_ub : runCall .unit (av 8) 0 = MirStepNode.fail .ub := rfl
theorem call_aligned_null_count0_steps :
    runCall (av 0) (av 8) 0 = finishMemIntrinsicCall S64 noop (loc 0) 1 := rfl
theorem call_live_aligned_count0_steps :
    runCall (pv 1 0) (pv 1 0) 0 = finishMemIntrinsicCall S64 noop (loc 0) 1 := rfl

/-- **The terminator path inherits the guard (universal)**: every well-formed-width
`copy_nonoverlapping::<T>(src, dst, count)` call is exactly `finishMemIntrinsicCall` of the
hardened statement-level `evalCopyNonOverlappingWithCount` on the same operands and values. -/
theorem call_inherits_withCount_univ (s : MachineState) (ld : List LocalDecl) (ly : LayoutTable)
    (srcOp dstOp cntOp : Operand) (sv dv : Value) (countSc : ScalarInt) (l' : List LocalSlot)
    (dest : Place) (bb : BasicBlockIdx)
    (hW : Nat.beq countSc.sizeBytes (layoutPointerBytes ly) = true) :
    evalCopyNonOverlappingCall s ld ly [srcOp, dstOp, cntOp] [sv, dv, .scalar countSc] l' dest bb =
      finishMemIntrinsicCall s
        (evalCopyNonOverlappingWithCount s srcOp dstOp ld ly sv dv countSc.bits l') dest bb := by
  unfold evalCopyNonOverlappingCall
  simp only [hW]

/-- ... so a definitely misaligned zero-byte call faults for every state, layout table, and
destination (lifting `zero_count_src_violation_ub_univ`). -/
theorem call_zero_count_src_violation_ub_univ (s : MachineState) (ld : List LocalDecl)
    (ly : LayoutTable) (srcOp dstOp cntOp : Operand) (sv dv : Value) (l' : List LocalSlot)
    (dest : Place) (bb : BasicBlockIdx) (sz al : Nat)
    (hElem : resolveCopyElemLayout ld ly srcOp dstOp = .ok sz al)
    (hSrc : checkZeroCountCopyPtr s l' ld ly al sv = .ub) :
    evalCopyNonOverlappingCall s ld ly [srcOp, dstOp, cntOp]
        [sv, dv, .scalar ⟨0, layoutPointerBytes ly⟩] l' dest bb = MirStepNode.fail .ub := by
  rw [call_inherits_withCount_univ s ld ly srcOp dstOp cntOp sv dv _ l' dest bb (Nat.beq_refl _),
    zero_count_src_violation_ub_univ s srcOp dstOp ld ly sv dv l' sz al hElem hSrc]
  rfl

/-! ### B1 soundness regressions & full-branch coverage -/

/-- `[u8; 8]` at `entries[0]` must NOT hijack `*mut u64` (`layoutIdx = 0`) to align 1. -/
def L64_u8arr8 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 8 1 (.array ⟨1⟩ 8)] }

def D64_ptrPtr : List LocalDecl :=
  [decl (.array (.uint .u8) 8) 0, decl (ptrK (ptrK (.uint .u64))) 0, decl (ptrK (.uint .u64)) 0]

theorem non_ptr_u8arr8_cannot_hijack_ptr_resolve :
    resolveCopyElemLayout D64_ptrPtr L64_u8arr8 (cp 1) (cp 1) = .ok 8 8 := rfl
theorem non_ptr_u8arr8_cannot_hijack_ptr_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_ptrPtr L64_u8arr8 (av 1) (av 1) 0
      locals64 = MirStepNode.fail .ub := rfl

/-- `#[repr(packed)] struct P8 { a: u64 }` at `entries[0]` must NOT hijack `*mut u64` to align 1. -/
def L64_packed8 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 8 1 (.arbitrary [⟨0⟩] [0]) [1], lay 8 8 .primitive] }

theorem non_ptr_packed8_cannot_hijack_ptr_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_ptrPtr L64_packed8 (av 1) (av 1) 0
      locals64 = MirStepNode.fail .ub := rfl

/-- Projected operand `_1[0] : *mut Align8` must NOT alias `entries[0] = *mut Packed` via
synthesized `layoutIdx = 0` (`operandTyResolved` preserves unresolved indices). -/
def align8K : RigidTy := .adt "zc::Align8" []
def L64_projHijack : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [ptrLay 8 1, lay 9 1 (.arbitrary [⟨0⟩, ⟨1⟩] [0, 1]) [2, 3],
                lay 1 1 .primitive, lay 8 8 .primitive] }
def D64_projHijack : List LocalDecl :=
  [decl (ptrK packedK) 0, decl (.array (ptrK align8K) 2) 99]
def opProjAlign8 : Operand := .copy (loc 1 [.constantIndex 0 2 false])

theorem projected_ptr_cannot_hijack_entry0_packed :
    resolveCopyElemLayout D64_projHijack L64_projHijack opProjAlign8 opProjAlign8 =
      .unsupported := rfl

/-- Depth-16 truncated `[T; 0]` (`align = 1, size = 0, fieldLayouts = []`) must NOT resolve as
`.ok 0 1` align-1 ZST; concrete `[u64; 0]` with a corrupt align-1 un-interned layout falls back
to exact `.ok 0 8`. -/
def L64_truncArr0 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 0 1 (.arbitrary [] []), lay 0 1 (.array ⟨0⟩ 0), ptrLay 8 1] }
def D64_truncArr0 : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.array paramT 0)) 2, decl (ptrK arrU64x0) 2]

theorem truncated_arr0_param_unresolved :
    resolveCopyElemLayout D64_truncArr0 L64_truncArr0 (cp 1) (cp 1) = .unsupported := rfl
theorem truncated_arr0_param_count5_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_truncArr0 L64_truncArr0 (av 1) (av 1) 5
      locals64 = MirStepNode.fail .ub := rfl
theorem corrupt_arr0_u64_recovers_align8 :
    resolveCopyElemLayout D64_truncArr0 L64_truncArr0 (cp 2) (cp 2) = .ok 0 8 := rfl

/-- Over-aligned uninhabited layout (`size = 0, align = 16, isUninhabited = true`) is rejected
for `!`, so `!` falls back to `(0, 1)` with no false `.ub` on `addr = 1`. -/
def L64_neverBad : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ { size := ⟨0⟩, align := ⟨16⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .empty, isUninhabited := true, fieldLayouts := [] }
      , ptrLay 8 0 ] }
def D64_neverBad : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK .never) 1]

theorem never_rejects_overaligned_layout :
    resolveCopyElemLayout D64_neverBad L64_neverBad (cp 1) (cp 1) = .ok 0 1 := rfl
theorem never_count0_aligned1_noop :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_neverBad L64_neverBad (av 1) (av 1) 0
      locals64 = noop := rfl

/-- Direct exercise of the `.atLeast` branch in `stackBorrowAlignKnown` on 32-bit with NO `u32`
local declaration: unlaid-out `(u32, u32)` has `rootBound = .atLeast 2`, while `elemAlign = 4`:
offset `0` (`0 % 2 = 0`) is `.unsupported` (no false `.ub`), and offset `1` (`1 % 2 ≠ 0`) is `.ub`. -/
def D32_noDecl : List LocalDecl :=
  [decl (.tuple []) 0, decl (.tuple [.uint .u32, .uint .u32]) 99, decl (ptrK (.uint .u32)) 2]

theorem target32_u32_tuple_atLeast2_off0_unsupported :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32_noDecl L32 (pv 1 0 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.unsupported := rfl
theorem target32_u32_tuple_atLeast2_off1_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32_noDecl L32 (pv 1 1 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl

/-- `globalAllocAlignKnown` coverage: align 8 off 0 noop, align 8 off 1 ub, align 4 off 1 ub,
align 4 off 0 unsupported, non-power-of-two align 3 unsupported. -/
def gAlloc (id al : Nat) : CapturedAllocation :=
  { allocId := id, bytes := [], relocations := [], align := ⟨al⟩, mutability := .not }
def S64_globals : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals64 },
    memory := { emptyMemory with
      globals := [gAlloc 10 8, gAlloc 11 4, gAlloc 12 3], nextTag := 1 } }

theorem global_align8_off0_noop :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 10 0) (av 8) 0 locals64 =
      MirStepNode.step (advanceStmt S64_globals locals64) := rfl
theorem global_align8_off1_ub :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 10 1) (av 8) 0 locals64 = MirStepNode.fail .ub := rfl
theorem global_align4_off1_u64_ub :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 11 1) (av 8) 0 locals64 = MirStepNode.fail .ub := rfl
theorem global_align4_off0_u64_unsupported :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 11 0) (av 8) 0 locals64 = MirStepNode.unsupported := rfl
theorem global_nonpow2_align3_unsupported :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 12 0) (av 8) 0 locals64 = MirStepNode.unsupported := rfl

/-- Recursive concrete `struct Node { next: *mut Node }`: `copyLayoutHasPlaceholder` stops at
pointer `backendRepr` and never cycles; also checks `ptLayoutIdx = 0` preserved with no `Node`
local declaration. -/
def nodeK : RigidTy := .adt "zc::Node" []
def L64_node : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 8 8 (.arbitrary [⟨0⟩] [0]) [1], ptrLay 8 0] }
def D64_node : List LocalDecl := [decl (ptrK nodeK) 1]

theorem recursive_node_ptLayoutIdx0_resolves :
    resolveCopyElemLayout D64_node L64_node (cp 0) (cp 0) = .ok 8 8 := rfl
theorem recursive_node_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 0) (cp 0) D64_node L64_node (av 4) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl

/-- Truncated generic multi-variant enum (`size = 1, align = 1, fieldLayouts = []`) is rejected. -/
def L64_truncEnum : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
          fields := .arbitrary [⟨0⟩] [0],
          variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
            [.arbitrary [] [], .arbitrary [⟨0⟩] [0]],
          isUninhabited := false, fieldLayouts := [] }
      , ptrLay 8 1 ] }
def D64_truncEnum : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.adt "zc::EnumT" [paramT])) 2]

theorem placeholder_truncated_enum_unresolved :
    resolveCopyElemLayout D64_truncEnum L64_truncEnum (cp 1) (cp 1) = .unsupported := rfl

/-- Unsized pointees (`*mut [u8]`, `*mut str`, `*mut (u8, [u8])`) fault `.ub` for all counts;
non-pointer-classified `.alias`/`.param`/ADT operands are `.unknown` (never spurious `.ub`);
opaque ADT pointer `*const Opaque` fails closed `.unsupported`; mismatched pointees (`*mut u32`
vs `*mut u8`) are `.unsupported` at `count = 0` and delegate at `count = 1`. -/
def D64_misc : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.slice (.uint .u8))) 0
  , decl (ptrK .str) 0
  , decl (ptrK (.tuple [.uint .u8, .slice (.uint .u8)])) 0
  , decl (.alias "zc::Alias" []) 0
  , decl paramT 0
  , decl opaqueK 0
  , decl (ptrK (ptrK opaqueK)) 0
  , decl (ptrK (.uint .u32)) 0
  , decl (ptrK (.uint .u8)) 0 ]

theorem unsized_slice_count0_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl
theorem unsized_str_count0_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl
theorem unsized_tuple_count1_ub :
    evalCopyNonOverlappingWithCount S64 (cp 3) (cp 3) D64_misc L64 (av 8) (av 8) 1 locals64 =
      MirStepNode.fail .ub := rfl
theorem alias_operand_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 4) (cp 4) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem param_operand_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 5) (cp 5) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem nonbox_adt_operand_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 6) (cp 6) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem opaque_adt_ptr_unresolved :
    resolveCopyElemLayout D64_misc L64 (cp 7) (cp 7) = .unsupported := rfl
theorem mismatched_pointees_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 8) (cp 9) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem mismatched_pointees_count1_delegates_ub :
    evalCopyNonOverlappingWithCount S64 (cp 8) (cp 9) D64_misc L64 (av 8) (av 8) 1 locals64 =
      MirStepNode.fail .ub := rfl

/-- Corrupted `[u8; 0]` with nonzero size `8` and corrupted wide pointer `*const [u8]` with
`align = 16` are rejected by `copyLayoutMatchesRigidTy` and fall back cleanly. -/
def L64_corrupt : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 8 8 (.array ⟨0⟩ 0) [4]
      , { size := ⟨16⟩, align := ⟨16⟩,
          backendRepr := .scalarPair
            (.initialized (.pointer 0) ⟨0, 2 ^ 64 - 1⟩)
            (.initialized (.int 64 false) ⟨0, 2 ^ 64 - 1⟩),
          fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1], variants := .single 0,
          isUninhabited := false, fieldLayouts := [] }
      , ptrLay 8 1
      , lay 1 1 .primitive
      , ptrLay 8 2 ] }
def D64_corrupt : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.array (.uint .u8) 0)) 3
  , decl (ptrK (.rawPtr .not (.slice (.uint .u8)))) 5 ]

theorem corrupt_array0_nonzero_size_rejected :
    resolveCopyElemLayout D64_corrupt L64_corrupt (cp 1) (cp 1) = .ok 0 1 := rfl
theorem corrupt_wide_ptr_align16_rejected :
    resolveCopyElemLayout D64_corrupt L64_corrupt (cp 2) (cp 2) = .ok 16 8 := rfl

/-- Cross-frame `callStack` borrow (`targetFrameDepth = 0` while active frame is at depth `1`):
`frameLocalDeclsAndLayoutsAtDepth` reads the saved caller's `localDecls`/`layouts`. -/
def callerBody64 : CapturedMir :=
  { defPath := "zc::caller", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [decl (.tuple []) 0, decl (.uint .u64) 1], basicBlocks := [],
    fnAbi :=
      { args := [], ret := { layout := lay 0 1 (.arbitrary [] []), mode := .ignore },
        conv := .rust, canUnwind := false },
    layouts := L64, allocations := [] }
def savedCaller64 : SavedCallerFrame :=
  { callerBody := callerBody64,
    frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨7, 8⟩)] },
    destination := loc 0 }
def S64_crossFrame : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals64 },
    memory := { emptyMemory with
      callStack := [savedCaller64],
      borrows := [bor 1 1],
      nextTag := 2 } }

theorem cross_frame_borrow_aligned_noop :
    evalCopyNonOverlappingWithCount S64_crossFrame (cp 2) (cp 3) D64 L64 (pv 1 0) (av 8) 0
      locals64 = MirStepNode.step (advanceStmt S64_crossFrame locals64) := rfl
theorem cross_frame_borrow_misaligned_ub :
    evalCopyNonOverlappingWithCount S64_crossFrame (cp 2) (cp 3) D64 L64 (pv 1 1) (av 8) 0
      locals64 = MirStepNode.fail .ub := rfl

/-! ### B2 soundness regressions (layout-index & compound field-layout validation) -/

/-- `entries[0] = ()` must NOT hijack an unresolved `_1 : Opaque` (`layoutIdx = 0`) into a ZST
`(0, 1)` layout (which would turn `count = 5` on misaligned pointers into a no-op). -/
def D64_unresAdt : List LocalDecl :=
  [decl (.tuple []) 0, decl opaqueK 0, decl (ptrK opaqueK) 0]

theorem unit0_cannot_hijack_unresolved_adt_decl :
    resolveCopyElemLayout D64_unresAdt L64 (cp 2) (cp 2) = .unsupported := rfl
theorem unit0_unresolved_adt_count5_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_unresAdt L64 (av 1) (av 1) 5
      locals64 = MirStepNode.fail .ub := rfl

/-- `entries[0] = *mut Packed` must NOT hijack an unresolved `_1 : *mut Align8` (`layoutIdx = 0`)
into `Packed`'s align-1 layout. -/
def D64_unresPtr : List LocalDecl :=
  [decl (ptrK packedK) 0, decl (ptrK align8K) 0]

theorem entry0_packed_ptr_cannot_hijack_unresolved_ptr_decl :
    resolveCopyElemLayout D64_unresPtr L64_projHijack (cp 1) (cp 1) = .unsupported := rfl

/-- `[u8; 4]` layout (`stride = 1, align = 1, fieldLayouts = [u8]`) must NOT validate as the
layout of `[u64; 4]`; `[u64; 4]` falls back to exact `.ok 32 8`, rejecting misaligned `av 1`
and `2^58 * 32 > isize::MAX` overflow. -/
def L64_arrHijack : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 1 1 .primitive
      , lay 4 1 (.array ⟨1⟩ 4) [1]
      , ptrLay 8 2 ] }
def D64_arrHijack : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.array (.uint .u64) 4)) 3]

theorem u8_arr4_cannot_hijack_u64_arr4_resolve :
    resolveCopyElemLayout D64_arrHijack L64_arrHijack (cp 1) (cp 1) = .ok 32 8 := rfl
theorem u8_arr4_cannot_hijack_u64_arr4_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_arrHijack L64_arrHijack (av 1) (av 1) 0
      locals64 = MirStepNode.fail .ub := rfl
theorem u8_arr4_cannot_hijack_u64_arr4_overflow_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_arrHijack L64_arrHijack (av 8) (av 8)
      (2 ^ 58) locals64 = MirStepNode.fail .ub := rfl

/-- `(u8, u8)` layout (`size = 2, align = 1, fieldLayouts = [u8, u8]`) must NOT validate as the
layout of `(u64, u64)`; a valid `(u64, u8)` layout (`size = 16, align = 8`) resolves cleanly. -/
def L64_tupHijack : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 1 1 .primitive
      , lay 8 8 .primitive
      , lay 2 1 (.arbitrary [⟨0⟩, ⟨1⟩] [0, 1]) [1, 1]
      , ptrLay 8 3
      , lay 16 8 (.arbitrary [⟨0⟩, ⟨8⟩] [0, 1]) [2, 1]
      , ptrLay 8 5 ] }
def D64_tupHijack : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u64])) 4
  , decl (ptrK (.tuple [.uint .u64, .uint .u8])) 6 ]

theorem u8_tuple_cannot_hijack_u64_tuple_unresolved :
    resolveCopyElemLayout D64_tupHijack L64_tupHijack (cp 1) (cp 1) = .unsupported := rfl
theorem valid_u64_u8_tuple_resolves :
    resolveCopyElemLayout D64_tupHijack L64_tupHijack (cp 2) (cp 2) = .ok 16 8 := rfl

/-! ### A2 soundness regressions (field offsets and array strides) -/

/-- A `(u64, u8)` layout placing the `u64` field at the misaligned offset `1` ("The fields are
properly aligned") and a `[Foo; 2]` layout whose stride `12` is not a multiple of its
alignment `8` are both rejected (fail closed), instead of resolving `(16, 8)` / `(24, 8)`. -/
def L64_a2 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 8 8 .primitive
      , lay 1 1 .primitive
      , lay 16 8 (.arbitrary [⟨1⟩, ⟨0⟩] [1, 0]) [1, 2]
      , ptrLay 8 3
      , lay 24 8 (.array ⟨12⟩ 2)
      , ptrLay 8 5 ] }
def D64_a2 : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u8])) 4
  , decl (ptrK (.array (.adt "zc::Foo" []) 2)) 6 ]

theorem misaligned_tuple_field_offset_rejected :
    resolveCopyElemLayout D64_a2 L64_a2 (cp 1) (cp 1) = .unsupported := rfl
theorem array_stride_not_multiple_of_align_rejected :
    resolveCopyElemLayout D64_a2 L64_a2 (cp 2) (cp 2) = .unsupported := rfl

/-! ### B3 soundness regressions (nested depth-16 truncation, overlapping tuple fields, multivariant tuples) -/

/-- Real `rustc-capture` depth-16 truncation occurs *nested* inside `fieldLayouts` (`Outer<Deep16<T>>`):
`Outer` has non-empty `fieldLayouts = [deep16Idx]` while `Deep16<T>` has empty `fieldLayouts = []`.
`copyLayoutHasPlaceholder` must reject truncated templates transitively, not only at the root. -/
def L64_nestedTrunc : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 0 1 (.arbitrary [⟨0⟩] [0])         -- 1: depth-16 truncated Deep16<T> (fieldLayouts = [])
      , lay 0 1 (.arbitrary [⟨0⟩] [0]) [1]     -- 2: Outer<Deep16<T>> (non-empty fieldLayouts!)
      , ptrLay 8 2 ] }
def D64_nestedTrunc : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.adt "zc::OuterDeep" [paramT])) 3]

theorem nested_truncated_param_wrapper_unresolved :
    resolveCopyElemLayout D64_nestedTrunc L64_nestedTrunc (cp 1) (cp 1) = .unsupported := rfl
theorem nested_truncated_param_wrapper_count5_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_nestedTrunc L64_nestedTrunc (av 1)
      (av 1) 5 locals64 = MirStepNode.fail .ub := rfl

/-- Overlapping tuple fields (`(u64, u64)` with `size = 8`, both at offset `0`) must be rejected,
while valid ZST sharing (`(u64, ())` with `size = 8`, both at offset `0`) remains accepted; a
multi-variant enum layout (`.multiple`) must be rejected for a tuple. -/
def L64_b3Tup : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])                                  -- 0: ()
      , lay 8 8 .primitive                                          -- 1: u64
      , lay 8 8 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1]) [1, 1]              -- 2: corrupt overlapping (u64, u64)
      , ptrLay 8 2                                                  -- 3: *mut (u64, u64)
      , lay 8 8 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1]) [1, 0]              -- 4: valid (u64, ())
      , ptrLay 8 4                                                  -- 5: *mut (u64, ())
      , { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
          fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1],
          variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
            [.arbitrary [] [], .arbitrary [⟨1⟩] [0]],
          isUninhabited := false, fieldLayouts := [7, 7] }          -- 6: multivariant enum
      , lay 1 1 .primitive                                          -- 7: u8
      , ptrLay 8 6 ] }                                              -- 8: *mut (u8, u8)
def D64_b3Tup : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u64])) 3
  , decl (ptrK (.tuple [.uint .u64, .tuple []])) 5
  , decl (ptrK (.tuple [.uint .u8, .uint .u8])) 8 ]

theorem overlapping_tuple_fields_size8_rejected :
    resolveCopyElemLayout D64_b3Tup L64_b3Tup (cp 1) (cp 1) = .unsupported := rfl
theorem valid_tuple_with_zst_shared_offset0_resolves :
    resolveCopyElemLayout D64_b3Tup L64_b3Tup (cp 2) (cp 2) = .ok 8 8 := rfl
theorem multivariant_tuple_rejected :
    resolveCopyElemLayout D64_b3Tup L64_b3Tup (cp 3) (cp 3) = .unsupported := rfl

/-! ### B4 soundness regressions (absent-`fieldLayouts` ZST/pointer/param arrays and tuples) -/

/-- When `fieldLayouts = []`, corrupted layouts for `[(); 0]` (align 8), `[*mut u64; 4]` (stride 1),
`[*const (u8, [u8]); 4]` (thin stride 8), `[T; 4]`, `(*mut u64, *mut u64)` (size 4), and `(T, u64)`
(size 8) must all be rejected rather than accepted as authoritative. -/
def L64_b4 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])                           -- 0: ()
      , lay 0 8 (.array ⟨8⟩ 0)                               -- 1: corrupt [(); 0] align 8
      , ptrLay 8 1                                           -- 2: *mut [(); 0]
      , lay 4 1 (.array ⟨1⟩ 4)                               -- 3: corrupt [*mut u64; 4] stride 1
      , ptrLay 8 3                                           -- 4: *mut [*mut u64; 4]
      , lay 32 8 (.array ⟨8⟩ 4)                              -- 5: corrupt wide-ptr / [T; 4] array
      , ptrLay 8 5                                           -- 6: *mut [widePtr; 4] / *mut [T; 4]
      , lay 4 1 (.arbitrary [⟨0⟩, ⟨2⟩] [0, 1])              -- 7: corrupt (*mut u64, *mut u64) sz 4
      , ptrLay 8 7                                           -- 8: *mut (*mut u64, *mut u64)
      , lay 8 8 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1])              -- 9: corrupt (T, u64) sz 8
      , ptrLay 8 9 ] }                                       -- 10: *mut (T, u64)
def D64_b4 : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.array (.tuple []) 0)) 2
  , decl (ptrK (.array (ptrK (.uint .u64)) 4)) 4
  , decl (ptrK (.array widePtrK 4)) 6
  , decl (ptrK arrT4) 6
  , decl (ptrK (.tuple [ptrK (.uint .u64), ptrK (.uint .u64)])) 8
  , decl (ptrK (.tuple [paramT, .uint .u64])) 10 ]

theorem corrupt_unit_arr0_align8_no_false_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_b4 L64_b4 (av 1) (av 1) 5 locals64 =
      noop := rfl
theorem corrupt_ptr_arr4_stride1_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_b4 L64_b4 (av 1) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl
theorem corrupt_wide_ptr_arr4_stride8_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 3) (cp 3) = .ok 64 8 := rfl
theorem corrupt_param_arr4_nil_fl_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 4) (cp 4) = .unsupported := rfl
theorem corrupt_ptr_tuple_small_size_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 5) (cp 5) = .unsupported := rfl
theorem corrupt_param_tuple_nil_fl_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 6) (cp 6) = .unsupported := rfl

/-! ### A4 regressions: arrays / non-empty tuples without `fieldLayouts` fail closed -/

/-- `rustc-capture` interns element / field layouts for every array and non-empty tuple above
its depth-16 limit, so an absent `fieldLayouts` list never determines a layout: a `(u64, u8)`
layout with `size = 9, align = 1` (whose primitive sizes sum to `9`) and a `[u64; 2]` layout
with `align = 1` are rejected; the tuple is then `.unsupported` and the array falls back to the
exact structural `(16, 8)`, so a 4-aligned dangling pointer is `.ub`. -/
def L64_a4 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 9 1 (.arbitrary [⟨0⟩, ⟨8⟩] [0, 1])
      , ptrLay 8 1
      , lay 16 1 (.array ⟨8⟩ 2)
      , ptrLay 8 3 ] }
def D64_a4 : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u8])) 2
  , decl (ptrK (.array (.uint .u64) 2)) 4 ]

theorem nil_fl_tuple_size9_align1_rejected :
    resolveCopyElemLayout D64_a4 L64_a4 (cp 1) (cp 1) = .unsupported := rfl
theorem nil_fl_u64_array_align1_falls_back_exact :
    resolveCopyElemLayout D64_a4 L64_a4 (cp 2) (cp 2) = .ok 16 8 := rfl
theorem nil_fl_u64_array_align1_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_a4 L64_a4 (av 4) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl

end Anneal.Tests.ZeroCountCopyAlign.V06

/-! ## §2. `V2026_08_01` (same fixtures; `Value` has no `uninit`) -/

namespace Anneal.Tests.ZeroCountCopyAlign.V08

open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! ### Universal characterizations -/

/-- Every zero-byte copy (`count * size_of::<T>() = 0`, here a zero-sized `T` with any `count`)
whose pointers pass the zero-byte precondition is a pure no-op. -/
theorem zst_any_count_noop_univ (s : MachineState) (src dst : Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (sv dv : Value) (count : Nat) (l3 : List LocalSlot) (al : Nat)
    (hElem : resolveCopyElemLayout ld ly src dst = .ok 0 al)
    (hPre : zeroByteCopyPrecheck s l3 ld ly al sv dv = .ok)
    (hCnt : count < scalarModulus (layoutPointerBytes ly)) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv count l3 =
      MirStepNode.step (advanceStmt s l3) := by
  have h0 : Nat.mul count 0 = 0 := Nat.mul_zero count
  have hRange : Bool.or (Nat.beq count 0)
      (Nat.blt count (scalarModulus (layoutPointerBytes ly))) = true := by
    simp [Nat.blt_eq.mpr hCnt]
  unfold evalCopyNonOverlappingWithCount
  simp only [hRange, hElem, h0, hPre]
  all_goals rfl

/-- A definitely violated zero-byte precondition on either pointer is `.ub` for `count = 0`,
whatever the other pointer is (Kleene strong conjunction). -/
theorem zero_count_src_violation_ub_univ (s : MachineState) (src dst : Operand)
    (ld : List LocalDecl) (ly : LayoutTable) (sv dv : Value) (l3 : List LocalSlot) (sz al : Nat)
    (hElem : resolveCopyElemLayout ld ly src dst = .ok sz al)
    (hSrc : checkZeroCountCopyPtr s l3 ld ly al sv = .ub) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv 0 l3 = MirStepNode.fail .ub := by
  have h0 : Nat.mul 0 sz = 0 := Nat.zero_mul sz
  unfold evalCopyNonOverlappingWithCount
  simp only [hElem, h0, zeroByteCopyPrecheck, hSrc, ZeroCheck.both]
  all_goals rfl

theorem zero_count_dst_violation_ub_univ (s : MachineState) (src dst : Operand)
    (ld : List LocalDecl) (ly : LayoutTable) (sv dv : Value) (l3 : List LocalSlot) (sz al : Nat)
    (hElem : resolveCopyElemLayout ld ly src dst = .ok sz al)
    (hDst : checkZeroCountCopyPtr s l3 ld ly al dv = .ub) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv 0 l3 = MirStepNode.fail .ub := by
  have h0 : Nat.mul 0 sz = 0 := Nat.zero_mul sz
  unfold evalCopyNonOverlappingWithCount
  simp only [hElem, h0, zeroByteCopyPrecheck, hDst]
  cases checkZeroCountCopyPtr s l3 ld ly al sv <;> rfl

/-- A non-thin-pointer argument value is `.ub` at every count and every element layout. -/
theorem malformed_src_ub_univ (s : MachineState) (src dst : Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (dv : Value) (count : Nat) (l3 : List LocalSlot) :
    evalCopyNonOverlappingWithCount s src dst ld ly .unit dv count l3 = MirStepNode.fail .ub := by
  unfold evalCopyNonOverlappingWithCount
  repeat' (first | rfl | (dsimp only) | split)

/-- An unresolved element layout with `count ≠ 0` and two thin pointer values delegates to the
unchanged non-zero-byte implementation. -/
theorem unresolved_nonzero_delegates_univ (s : MachineState) (src dst : Operand)
    (ld : List LocalDecl) (ly : LayoutTable) (sp dp : ProvenancePtr) (count : Nat)
    (l3 : List LocalSlot) (hElem : resolveCopyElemLayout ld ly src dst = .unsupported)
    (hC : Nat.beq count 0 = false) (hCnt : count < scalarModulus (layoutPointerBytes ly)) :
    evalCopyNonOverlappingWithCount s src dst ld ly (.ptr sp (layoutPointerBytes ly))
        (.ptr dp (layoutPointerBytes ly)) count l3 =
      evalCopyNonOverlappingWithCountNonZero s src dst ld ly (.ptr sp (layoutPointerBytes ly))
        (.ptr dp (layoutPointerBytes ly)) count l3 := by
  unfold evalCopyNonOverlappingWithCount
  simp [hElem, hC, isThinPtrValue, Nat.blt_eq.mpr hCnt]

/-- A `count` whose bits are not a `usize` bit pattern is `.ub` at every element layout
(even for a zero-sized `T`, where `count * size_of::<T>() = 0`). -/
theorem out_of_range_count_ub_univ (s : MachineState) (src dst : Operand) (ld : List LocalDecl)
    (ly : LayoutTable) (sv dv : Value) (count : Nat) (l3 : List LocalSlot)
    (hCnt : scalarModulus (layoutPointerBytes ly) ≤ count) :
    evalCopyNonOverlappingWithCount s src dst ld ly sv dv count l3 = MirStepNode.fail .ub := by
  have hPos : 0 < scalarModulus (layoutPointerBytes ly) := by
    generalize layoutPointerBytes ly = k
    induction k with
    | zero => exact Nat.one_pos
    | succ k ih => exact Nat.mul_pos (by decide) ih
  have hRange : Bool.or (Nat.beq count 0)
      (Nat.blt count (scalarModulus (layoutPointerBytes ly))) = false := by
    have h1 : count ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le hPos hCnt)
    have h2 : ¬ count < scalarModulus (layoutPointerBytes ly) := Nat.not_lt.mpr hCnt
    have e1 : Nat.beq count 0 = false :=
      Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
    have e2 : Nat.blt count (scalarModulus (layoutPointerBytes ly)) = false :=
      Bool.eq_false_iff.mpr (fun h => h2 (Nat.blt_eq.mp h))
    rw [e1, e2]
    rfl
  unfold evalCopyNonOverlappingWithCount
  simp only [hRange]

/-! ### Fixtures -/

/-- A type with layout index `i`. -/
def ty (k : RigidTy) (i : Nat := 0) : Ty := { kind := k, layoutIdx := i }
/-- A mutable local declaration. -/
def decl (k : RigidTy) (i : Nat := 0) : LocalDecl :=
  { mutability := .mut, ty := ty k i, debugName := none }
/-- `*mut T`. -/
def ptrK (k : RigidTy) : RigidTy := .rawPtr .mut k
/-- A local place. -/
def loc (i : Nat) (proj : List ProjectionElem := []) : Place := { local_ := i, projection := proj }
/-- `copy _i`. -/
def cp (i : Nat) : Operand := .copy (loc i)
/-- A `usize` constant (`sizeBytes` overridable for malformed counts). -/
def usz (n : Nat) (w : Nat := 8) : Operand :=
  .constant { ty := ty (.uint .usize), val := .scalar (.int ⟨n, w⟩) }

/-- A plain memory-backed layout. -/
def lay (sz al : Nat) (f : FieldsShape) (fl : List Nat := []) : TypeLayout :=
  { size := ⟨sz⟩, align := ⟨al⟩, backendRepr := .memory, fields := f, variants := .single 0,
    isUninhabited := false, fieldLayouts := fl }
/-- A thin pointer layout whose single `fieldLayouts` entry names the pointee layout. -/
def ptrLay (w pointee : Nat) : TypeLayout :=
  { size := ⟨w⟩, align := ⟨w⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 2 ^ (8 * w) - 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false,
    fieldLayouts := [pointee] }

/-- `T` (generic parameter). -/
def paramT : RigidTy := .param 0 "T"
/-- `[u64; 0]`. -/
def arrU64x0 : RigidTy := .array (.uint .u64) 0
/-- Opaque ADT without a layout. -/
def opaqueK : RigidTy := .adt "zc::Opaque" []
/-- `Wrapper<T>`. -/
def wrapT : RigidTy := .adt "zc::Wrapper" [paramT]
/-- `[T; 4]`. -/
def arrT4 : RigidTy := .array paramT 4
/-- A generic struct nested `≥ 16` deep (truncated template). -/
def truncK : RigidTy := .adt "zc::Deep" [paramT]
/-- `Wrapper<u64>`. -/
def wrapU64 : RigidTy := .adt "zc::Wrapper" [.uint .u64]
/-- `#[repr(packed)] struct Packed { a: u8, b: u64 }`. -/
def packedK : RigidTy := .adt "zc::Packed" []
/-- `#[repr(C)] struct Outer { p: Packed }` (align 8). -/
def outerK : RigidTy := .adt "zc::Outer" []
/-- `(u128, u128)`. -/
def u128Pair : RigidTy := .tuple [.uint .u128, .uint .u128]
/-- `*const (u8, [u8])` (a wide pointer). -/
def widePtrK : RigidTy := .rawPtr .not (.tuple [.uint .u8, .slice (.uint .u8)])
/-- `[[…[T; 1]…; 1]; 1]` nested `n` deep. -/
def nestT : Nat → RigidTy
  | 0 => paramT
  | n + 1 => .array (nestT n) 1

/-- Placeholder-chain layouts for `nestT`: entry `base + k` is `[nestT k; 1]`. -/
def nestLays (base : Nat) : Nat → List TypeLayout
  | 0 => []
  | n + 1 => nestLays base n ++ [lay 0 1 (.array ⟨0⟩ 1) [if n = 0 then 2 else base + n - 1]]

/-- The 64-bit layout table (entry `0` is the unit layout, as in `rustc-capture`). -/
def L64 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])                         -- 0: ()
      , lay 8 8 .primitive                                -- 1: u64
      , lay 0 1 .primitive                                -- 2: placeholder `T`
      , lay 0 1 (.arbitrary [⟨0⟩] [0]) [2]                -- 3: Wrapper<T> template
      , lay 0 1 (.array ⟨0⟩ 4) [2]                        -- 4: [T; 4] template
      , lay 0 1 (.arbitrary [⟨0⟩] [0])                    -- 5: truncated depth-16 template
      , lay 8 8 (.arbitrary [⟨0⟩] [0]) [1]                -- 6: Wrapper<u64>
      , ptrLay 8 3                                        -- 7: *mut Wrapper<T>
      , ptrLay 8 4                                        -- 8: *mut [T; 4]
      , ptrLay 8 5                                        -- 9: *mut Deep<T>
      , ptrLay 8 6                                        -- 10: *mut Wrapper<u64>
      , lay 9 1 (.arbitrary [⟨0⟩, ⟨1⟩] [0, 1]) [12, 1]   -- 11: Packed
      , lay 1 1 .primitive                                -- 12: u8
      , lay 16 8 (.arbitrary [⟨0⟩] [0]) [11]              -- 13: Outer
      , lay 16 16 .primitive                              -- 14: u128 (x86_64)
      , ptrLay 8 14                                       -- 15: *mut u128
      , ptrLay 8 24 ] ++                                  -- 16: *mut nestT 9
      nestLays 17 9 }                                    -- 17..25: nestT 1 ..= nestT 9

/-- Local declarations of the 64-bit fixture body. -/
def D64 : List LocalDecl :=
  [ decl (.tuple []) 0                 -- _0
  , decl (.uint .u64) 1                -- _1 : u64
  , decl (ptrK (.uint .u64))           -- _2 : *mut u64
  , decl (ptrK (.uint .u64))           -- _3 : *mut u64
  , decl (ptrK arrU64x0)               -- _4 : *mut [u64; 0]
  , decl (ptrK opaqueK)                -- _5 : *mut Opaque
  , decl (ptrK wrapT) 7                -- _6 : *mut Wrapper<T>
  , decl (ptrK arrT4) 8                -- _7 : *mut [T; 4]
  , decl (ptrK truncK) 9               -- _8 : *mut Deep<T>
  , decl (ptrK wrapU64) 10             -- _9 : *mut Wrapper<u64>
  , decl outerK 13                     -- _10 : Outer
  , decl u128Pair 99                   -- _11 : (u128, u128) (no layout entry)
  , decl (ptrK (.uint .u128)) 15       -- _12 : *mut u128
  , decl (ptrK widePtrK)               -- _13 : *mut *const (u8, [u8])
  , decl (.uint .u32)                  -- _14 : u32
  , decl (ptrK (nestT 9)) 16           -- _15 : *mut nestT 9
  , decl packedK 11                    -- _16 : Packed
  ]

/-- Frame locals (every local live). -/
def locals64 : List LocalSlot :=
  [ .uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit, .uninit, .uninit, .uninit, .uninit
  , .uninit, .uninit, .init (.aggregate 0 [.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 8⟩]])
  , .init (.aggregate 0 [.scalar ⟨1, 16⟩, .scalar ⟨2, 16⟩]), .uninit, .uninit, .uninit, .uninit
  , .init (.aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 8⟩]) ]

/-- A borrow entry with tag `t` on local `l` at projection `proj`. -/
def bor (t l : Nat) (proj : List ProjectionElem := []) (dead : Bool := false)
    (perm : TreeBorrowPerm := .unique) : BorrowEntry :=
  { tag := t, targetLocal := l, targetProjection := proj, perm := perm,
    targetFrameDepth := 0, allocDead := dead }

/-- Borrow table: `1 ↦ _1`, `2 ↦ dead _1`, `3 ↦ _10.p.b`, `4 ↦ _11.0`, `5 ↦ _16.b`,
`6 ↦ _1` (`.disabled` but live). -/
def B64 : List BorrowEntry :=
  [ bor 1 1
  , bor 2 1 [] true .disabled
  , bor 3 10 [.field 0 (ty packedK 11), .field 1 (ty (.uint .u64) 1)]
  , bor 4 11 [.field 0 (ty (.uint .u128) 14)]
  , bor 5 16 [.field 1 (ty (.uint .u64) 1)]
  , bor 6 1 [] false .disabled ]

/-- The 64-bit fixture machine state. -/
def S64 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals64 },
    memory := { emptyMemory with borrows := B64, nextTag := 7 } }

/-- Pointer value with provenance tag `t` at byte offset `off`. -/
def pv (t off : Nat) (w : Nat := 8) : Value := .ptr ⟨t, off⟩ w
/-- Integer address `a` (`NonNull::dangling()`, null, or misaligned). -/
def av (a : Nat) (w : Nat := 8) : Value := .scalar ⟨a, w⟩

/-- `copy_nonoverlapping` statement-level evaluation with pre-resolved count bits. -/
def run (src dst : Nat) (sv dv : Value) (count : Nat) : MirStepNode :=
  evalCopyNonOverlappingWithCount S64 (cp src) (cp dst) D64 L64 sv dv count locals64

/-- Success: the zero-byte copy is a pure no-op. -/
def noop : MirStepNode := MirStepNode.step (advanceStmt S64 locals64)

/-! ### Live aligned, dangling, and null pointers on the zero-byte fragment -/

theorem live_aligned_count0_noop : run 2 3 (pv 1 0) (pv 1 0) 0 = noop := rfl
theorem live_disabled_tag_count0_noop : run 2 3 (pv 6 0) (pv 1 0) 0 = noop := rfl
theorem dangling_count0_noop : run 2 3 (av 8) (av 8) 0 = noop := rfl
theorem dangling_large_count0_noop : run 2 3 (av 0x7ff8) (av 4096) 0 = noop := rfl
theorem null_count0_noop : run 2 3 (av 0) (av 0) 0 = noop := rfl
theorem null_unbacked_ptr_count0_noop : run 2 3 (pv 0 0) (av 0) 0 = noop := rfl
theorem null_zst_count5_noop : run 4 4 (av 0) (av 0) 5 = noop := rfl
theorem nonzero_null_u64_ub : run 2 3 (av 0) (av 0) 1 = MirStepNode.fail .ub := rfl
theorem nonzero_null_dst_ub : run 2 3 (pv 1 0) (av 0) 1 = MirStepNode.fail .ub := rfl

/-! ### Misalignment -/

theorem misaligned_live_offset1_ub : run 2 3 (pv 1 1) (pv 1 0) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_live_dst_offset1_ub : run 2 3 (pv 1 0) (pv 1 1) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_dangling_9_ub : run 2 3 (av 9) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_unbacked_ptr_ub : run 2 3 (pv 0 9) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem misaligned_fnptr_like_ub : run 2 3 (pv 77 3) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem unbacked_aligned_unsupported : run 2 3 (pv 77 8) (av 8) 0 = MirStepNode.unsupported := rfl

/-- `copyMisalignedZeroBody` shape: `_2 = &raw mut _1; _2 = (_2 as *mut u8).offset(1) as
*mut u64; copy_nonoverlapping(copy _2, copy _2, 0)`, executed through the statement-level
`evalStmt` (count operand evaluated and range-checked). -/
def misalignedS : MachineState :=
  { S64 with frame := { S64.frame with locals := locals64.set 2 (.init (pv 1 1)) } }

theorem copyMisalignedZeroBody_shape_ub :
    evalStmt misalignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz 0)), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.fail .ub := rfl

/-- The aligned counterpart of `copyMisalignedZeroBody` steps. -/
def alignedS : MachineState :=
  { S64 with frame := { S64.frame with locals := locals64.set 2 (.init (pv 1 0)) } }

theorem copyAlignedZeroBody_shape_noop :
    evalStmt alignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz 0)), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.step (advanceStmt alignedS alignedS.frame.locals) := rfl

/-! ### Malformed pointer values and ill-typed operands -/

theorem wrong_width_scalar_ub : run 2 3 (av 8 4) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem out_of_range_scalar_ub : run 2 3 (av (2 ^ 64)) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem wrong_width_ptr_ub : run 2 3 (pv 1 0 4) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem wrong_width_ptr_nonzero_ub : run 2 3 (pv 1 0 4) (pv 1 0) 1 = MirStepNode.fail .ub := rfl
theorem unit_value_ub : run 2 3 .unit (av 8) 0 = MirStepNode.fail .ub := rfl
theorem aggregate_value_ub : run 2 3 (av 8) (.aggregate 0 []) 0 = MirStepNode.fail .ub := rfl
theorem nonptr_operand_ub : run 14 3 (av 8) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem nonptr_operand_nonzero_ub : run 2 14 (pv 1 0) (pv 1 0) 3 = MirStepNode.fail .ub := rfl
theorem out_of_range_count_bits_ub :
    evalStmt alignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz (2 ^ 64))), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.fail .ub := rfl
theorem wrong_width_count_ub :
    evalStmt alignedS ⟨.intrinsic (.copyNonOverlapping (cp 2) (cp 2) (usz 0 4)), "zc.rs:1:1"⟩
      D64 L64 = MirStepNode.fail .ub := rfl

/-! ### Zero-sized element types -/

theorem resolve_arrU64x0 : resolveCopyElemLayout D64 L64 (cp 4) (cp 4) = .ok 0 8 := rfl
theorem zst_aligned_count5_noop : run 4 4 (av 16) (av 8) 5 = noop := rfl
theorem zst_misaligned_count5_ub : run 4 4 (av 16) (av 4) 5 = MirStepNode.fail .ub := rfl
theorem zst_dead_borrow_count5_unsupported : run 4 4 (pv 2 0) (av 8) 5 = MirStepNode.unsupported := rfl
theorem zst_out_of_range_count_ub : run 4 4 (av 8) (av 8) (2 ^ 64) = MirStepNode.fail .ub := rfl
/-- The call form only checks the `count` scalar's width; the out-of-range bits of a
zero-sized-`T` call are still `.ub` (`evalCopyNonOverlappingWithCount` step 0). -/
theorem call_zst_out_of_range_count_ub :
    evalCopyNonOverlappingCall S64 D64 L64 [cp 4, cp 4, usz 0] [av 8, av 8, .scalar ⟨2 ^ 64, 8⟩]
      locals64 (loc 0) 1 = MirStepNode.fail .ub := rfl

/-! ### `count * size_of::<T>() ≤ isize::MAX` -/

theorem overflow_u64_ub : run 2 3 (pv 1 0) (pv 1 0) (2 ^ 60) = MirStepNode.fail .ub := rfl
theorem overflow_u64_null_ub : run 2 3 (av 0) (av 0) (2 ^ 62) = MirStepNode.fail .ub := rfl
theorem resolve_widePtr : resolveCopyElemLayout D64 L64 (cp 13) (cp 13) = .ok 16 8 := rfl
theorem overflow_widePtr_ub : run 13 13 (av 8) (av 8) (2 ^ 59) = MirStepNode.fail .ub := rfl
theorem widePtr_count0_noop : run 13 13 (av 8) (av 8) 0 = noop := rfl

/-! ### Undetermined layouts and Kleene conjunction -/

theorem opaque_unresolved : resolveCopyElemLayout D64 L64 (cp 5) (cp 5) = .unsupported := rfl
theorem opaque_count0_unsupported : run 5 5 (av 9) (av 0) 0 = MirStepNode.unsupported := rfl
theorem opaque_count0_malformed_ub : run 5 5 (av 8) .unit 0 = MirStepNode.fail .ub := rfl
theorem kleene_unsupported_and_ub : ZeroCheck.both .unsupported .ub = .ub := rfl
theorem kleene_ub_and_unsupported : ZeroCheck.both .ub .unsupported = .ub := rfl
theorem kleene_unsupported_and_ok : ZeroCheck.both .unsupported .ok = .unsupported := rfl
theorem kleene_dead_src_misaligned_dst_ub : run 2 3 (pv 2 0) (av 9) 0 = MirStepNode.fail .ub := rfl
theorem kleene_misaligned_src_dead_dst_ub : run 2 3 (av 9) (pv 2 0) 0 = MirStepNode.fail .ub := rfl
theorem dead_borrow_align8_unsupported : run 2 3 (pv 2 0) (av 8) 0 = MirStepNode.unsupported := rfl

/-! ### Place-alignment bounds (packed fields, unlaid-out tuples, large offsets) -/

theorem packed_field_misaligned_ub : run 2 3 (pv 5 0) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem packed_field_plus7_in_outer_noop : run 2 3 (pv 3 7) (av 8) 0 = noop := rfl
theorem packed_field_in_outer_misaligned_ub : run 2 3 (pv 3 0) (av 8) 0 = MirStepNode.fail .ub := rfl
/-- `(u128, u128)` without a layout entry is `.atLeast 8` on 64-bit, so `&raw mut x.0` at
offset `0` is undetermined (never a false `.ub`) while odd offset `+3` (`3 % 8 ≠ 0`) is `.ub`. -/
theorem u128_tuple_field_no_false_ub : run 12 12 (pv 4 0) (av 16) 0 = MirStepNode.unsupported := rfl
theorem u128_tuple_field_odd_offset_ub :
    run 12 12 (pv 4 3) (av 16) 0 = MirStepNode.fail .ub := rfl
theorem large_offset_aligned_noop : run 2 3 (pv 1 (10 ^ 10)) (av 8) 0 = noop := rfl
theorem large_offset_misaligned_ub : run 2 3 (pv 1 (10 ^ 10 + 3)) (av 8) 0 = MirStepNode.fail .ub := rfl

/-! ### Pre-monomorphization placeholder layouts -/

theorem placeholder_wrapper_unresolved :
    resolveCopyElemLayout D64 L64 (cp 6) (cp 6) = .unsupported := rfl
theorem placeholder_wrapper_count0_unsupported :
    run 6 6 (pv 1 0) (pv 1 0) 0 = MirStepNode.unsupported := rfl
theorem placeholder_wrapper_count5_not_noop :
    run 6 6 (av 1) (av 1) 5 = MirStepNode.fail .ub := rfl
theorem placeholder_array_unresolved :
    resolveCopyElemLayout D64 L64 (cp 7) (cp 7) = .unsupported := rfl
theorem placeholder_truncated_unresolved :
    resolveCopyElemLayout D64 L64 (cp 8) (cp 8) = .unsupported := rfl
theorem placeholder_nested9_unresolved :
    resolveCopyElemLayout D64 L64 (cp 15) (cp 15) = .unsupported := rfl
theorem monomorphized_wrapper_resolves :
    resolveCopyElemLayout D64 L64 (cp 9) (cp 9) = .ok 8 8 := rfl
theorem monomorphized_wrapper_misaligned_ub : run 9 9 (av 4) (av 8) 0 = MirStepNode.fail .ub := rfl

/-! ### 32-bit target -/

/-- 32-bit table: `0 ↦ ()`, `1 ↦ u32`, `2 ↦ *mut u32` (pointee `1`). -/
def L32 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true,
    entries := [lay 0 1 (.arbitrary [] []), lay 4 4 .primitive, ptrLay 4 1] }

/-- `_0 : ()`, `_1 : (u32, u32)` (no layout), `_2 : *mut u32`, `_3 : u32`. -/
def D32 : List LocalDecl :=
  [decl (.tuple []) 0, decl (.tuple [.uint .u32, .uint .u32]) 99, decl (ptrK (.uint .u32)) 2,
   decl (.uint .u32) 1]

/-- 32-bit frame locals. -/
def locals32 : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]), .uninit, .init (.scalar ⟨3, 4⟩)]

/-- 32-bit state: borrows `1 ↦ _1.0`, `2 ↦ _3`. -/
def S32 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals32 },
    memory := { emptyMemory with
      borrows := [bor 1 1 [.field 0 (ty (.uint .u32) 1)], bor 2 3], nextTag := 3 } }

theorem target32_resolve_u32 : resolveCopyElemLayout D32 L32 (cp 2) (cp 2) = .ok 4 4 := rfl
/-- The unlaid-out `(u32, u32)` root is `.atLeast 4` (its fields' declared `u32` layout), so
`&raw mut x.0` is aligned in every execution (no false `.ub`) ... -/
theorem target32_u32_tuple_field_aligned_noop :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 1 0 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.step (advanceStmt S32 S32.frame.locals) := rfl
/-- ... and `(&raw mut x.0).byte_add(1)` is misaligned in every execution. -/
theorem target32_u32_tuple_field_odd_offset_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 1 1 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl
theorem target32_decl_u32_aligned_noop :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 2 0 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.step (advanceStmt S32 S32.frame.locals) := rfl
theorem target32_decl_u32_misaligned_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (pv 2 2 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl
theorem target32_8byte_ptr_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (av 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl
theorem target32_overflow_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32 L32 (av 4 4) (av 4 4) (2 ^ 29)
      S32.frame.locals = MirStepNode.fail .ub := rfl

/-! ### Terminator path (`copy_nonoverlapping::<T>` call) -/

/-- The call form at `count = n` with argument values `sv`, `dv`. -/
def runCall (sv dv : Value) (n : Nat) : MirStepNode :=
  evalCopyNonOverlappingCall S64 D64 L64 [cp 2, cp 3, usz n] [sv, dv, .scalar ⟨n, 8⟩] locals64
    (loc 0) 1

theorem call_misaligned_count0_ub : runCall (pv 1 1) (pv 1 0) 0 = MirStepNode.fail .ub := rfl
theorem call_misaligned_dangling_count0_ub : runCall (av 9) (av 8) 0 = MirStepNode.fail .ub := rfl
theorem call_malformed_count0_ub : runCall .unit (av 8) 0 = MirStepNode.fail .ub := rfl
theorem call_aligned_null_count0_steps :
    runCall (av 0) (av 8) 0 = finishMemIntrinsicCall S64 noop (loc 0) 1 := rfl
theorem call_live_aligned_count0_steps :
    runCall (pv 1 0) (pv 1 0) 0 = finishMemIntrinsicCall S64 noop (loc 0) 1 := rfl

/-- **The terminator path inherits the guard (universal)**: every well-formed-width
`copy_nonoverlapping::<T>(src, dst, count)` call is exactly `finishMemIntrinsicCall` of the
hardened statement-level `evalCopyNonOverlappingWithCount` on the same operands and values. -/
theorem call_inherits_withCount_univ (s : MachineState) (ld : List LocalDecl) (ly : LayoutTable)
    (srcOp dstOp cntOp : Operand) (sv dv : Value) (countSc : ScalarInt) (l' : List LocalSlot)
    (dest : Place) (bb : BasicBlockIdx)
    (hW : Nat.beq countSc.sizeBytes (layoutPointerBytes ly) = true) :
    evalCopyNonOverlappingCall s ld ly [srcOp, dstOp, cntOp] [sv, dv, .scalar countSc] l' dest bb =
      finishMemIntrinsicCall s
        (evalCopyNonOverlappingWithCount s srcOp dstOp ld ly sv dv countSc.bits l') dest bb := by
  unfold evalCopyNonOverlappingCall
  simp only [hW]

/-- ... so a definitely misaligned zero-byte call faults for every state, layout table, and
destination (lifting `zero_count_src_violation_ub_univ`). -/
theorem call_zero_count_src_violation_ub_univ (s : MachineState) (ld : List LocalDecl)
    (ly : LayoutTable) (srcOp dstOp cntOp : Operand) (sv dv : Value) (l' : List LocalSlot)
    (dest : Place) (bb : BasicBlockIdx) (sz al : Nat)
    (hElem : resolveCopyElemLayout ld ly srcOp dstOp = .ok sz al)
    (hSrc : checkZeroCountCopyPtr s l' ld ly al sv = .ub) :
    evalCopyNonOverlappingCall s ld ly [srcOp, dstOp, cntOp]
        [sv, dv, .scalar ⟨0, layoutPointerBytes ly⟩] l' dest bb = MirStepNode.fail .ub := by
  rw [call_inherits_withCount_univ s ld ly srcOp dstOp cntOp sv dv _ l' dest bb (Nat.beq_refl _),
    zero_count_src_violation_ub_univ s srcOp dstOp ld ly sv dv l' sz al hElem hSrc]
  rfl

/-! ### B1 soundness regressions & full-branch coverage -/

/-- `[u8; 8]` at `entries[0]` must NOT hijack `*mut u64` (`layoutIdx = 0`) to align 1. -/
def L64_u8arr8 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 8 1 (.array ⟨1⟩ 8)] }

def D64_ptrPtr : List LocalDecl :=
  [decl (.array (.uint .u8) 8) 0, decl (ptrK (ptrK (.uint .u64))) 0, decl (ptrK (.uint .u64)) 0]

theorem non_ptr_u8arr8_cannot_hijack_ptr_resolve :
    resolveCopyElemLayout D64_ptrPtr L64_u8arr8 (cp 1) (cp 1) = .ok 8 8 := rfl
theorem non_ptr_u8arr8_cannot_hijack_ptr_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_ptrPtr L64_u8arr8 (av 1) (av 1) 0
      locals64 = MirStepNode.fail .ub := rfl

/-- `#[repr(packed)] struct P8 { a: u64 }` at `entries[0]` must NOT hijack `*mut u64` to align 1. -/
def L64_packed8 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 8 1 (.arbitrary [⟨0⟩] [0]) [1], lay 8 8 .primitive] }

theorem non_ptr_packed8_cannot_hijack_ptr_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_ptrPtr L64_packed8 (av 1) (av 1) 0
      locals64 = MirStepNode.fail .ub := rfl

/-- Projected operand `_1[0] : *mut Align8` must NOT alias `entries[0] = *mut Packed` via
synthesized `layoutIdx = 0` (`operandTyResolved` preserves unresolved indices). -/
def align8K : RigidTy := .adt "zc::Align8" []
def L64_projHijack : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [ptrLay 8 1, lay 9 1 (.arbitrary [⟨0⟩, ⟨1⟩] [0, 1]) [2, 3],
                lay 1 1 .primitive, lay 8 8 .primitive] }
def D64_projHijack : List LocalDecl :=
  [decl (ptrK packedK) 0, decl (.array (ptrK align8K) 2) 99]
def opProjAlign8 : Operand := .copy (loc 1 [.constantIndex 0 2 false])

theorem projected_ptr_cannot_hijack_entry0_packed :
    resolveCopyElemLayout D64_projHijack L64_projHijack opProjAlign8 opProjAlign8 =
      .unsupported := rfl

/-- Depth-16 truncated `[T; 0]` (`align = 1, size = 0, fieldLayouts = []`) must NOT resolve as
`.ok 0 1` align-1 ZST; concrete `[u64; 0]` with a corrupt align-1 un-interned layout falls back
to exact `.ok 0 8`. -/
def L64_truncArr0 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 0 1 (.arbitrary [] []), lay 0 1 (.array ⟨0⟩ 0), ptrLay 8 1] }
def D64_truncArr0 : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.array paramT 0)) 2, decl (ptrK arrU64x0) 2]

theorem truncated_arr0_param_unresolved :
    resolveCopyElemLayout D64_truncArr0 L64_truncArr0 (cp 1) (cp 1) = .unsupported := rfl
theorem truncated_arr0_param_count5_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_truncArr0 L64_truncArr0 (av 1) (av 1) 5
      locals64 = MirStepNode.fail .ub := rfl
theorem corrupt_arr0_u64_recovers_align8 :
    resolveCopyElemLayout D64_truncArr0 L64_truncArr0 (cp 2) (cp 2) = .ok 0 8 := rfl

/-- Over-aligned uninhabited layout (`size = 0, align = 16, isUninhabited = true`) is rejected
for `!`, so `!` falls back to `(0, 1)` with no false `.ub` on `addr = 1`. -/
def L64_neverBad : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ { size := ⟨0⟩, align := ⟨16⟩, backendRepr := .memory, fields := .arbitrary [] [],
          variants := .empty, isUninhabited := true, fieldLayouts := [] }
      , ptrLay 8 0 ] }
def D64_neverBad : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK .never) 1]

theorem never_rejects_overaligned_layout :
    resolveCopyElemLayout D64_neverBad L64_neverBad (cp 1) (cp 1) = .ok 0 1 := rfl
theorem never_count0_aligned1_noop :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_neverBad L64_neverBad (av 1) (av 1) 0
      locals64 = noop := rfl

/-- Direct exercise of the `.atLeast` branch in `stackBorrowAlignKnown` on 32-bit with NO `u32`
local declaration: unlaid-out `(u32, u32)` has `rootBound = .atLeast 2`, while `elemAlign = 4`:
offset `0` (`0 % 2 = 0`) is `.unsupported` (no false `.ub`), and offset `1` (`1 % 2 ≠ 0`) is `.ub`. -/
def D32_noDecl : List LocalDecl :=
  [decl (.tuple []) 0, decl (.tuple [.uint .u32, .uint .u32]) 99, decl (ptrK (.uint .u32)) 2]

theorem target32_u32_tuple_atLeast2_off0_unsupported :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32_noDecl L32 (pv 1 0 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.unsupported := rfl
theorem target32_u32_tuple_atLeast2_off1_ub :
    evalCopyNonOverlappingWithCount S32 (cp 2) (cp 2) D32_noDecl L32 (pv 1 1 4) (av 4 4) 0
      S32.frame.locals = MirStepNode.fail .ub := rfl

/-- `globalAllocAlignKnown` coverage: align 8 off 0 noop, align 8 off 1 ub, align 4 off 1 ub,
align 4 off 0 unsupported, non-power-of-two align 3 unsupported. -/
def gAlloc (id al : Nat) : CapturedAllocation :=
  { allocId := id, bytes := [], relocations := [], align := ⟨al⟩, mutability := .not }
def S64_globals : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals64 },
    memory := { emptyMemory with
      globals := [gAlloc 10 8, gAlloc 11 4, gAlloc 12 3], nextTag := 1 } }

theorem global_align8_off0_noop :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 10 0) (av 8) 0 locals64 =
      MirStepNode.step (advanceStmt S64_globals locals64) := rfl
theorem global_align8_off1_ub :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 10 1) (av 8) 0 locals64 = MirStepNode.fail .ub := rfl
theorem global_align4_off1_u64_ub :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 11 1) (av 8) 0 locals64 = MirStepNode.fail .ub := rfl
theorem global_align4_off0_u64_unsupported :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 11 0) (av 8) 0 locals64 = MirStepNode.unsupported := rfl
theorem global_nonpow2_align3_unsupported :
    evalCopyNonOverlappingWithCount S64_globals (cp 2) (cp 3) D64 L64
      (pv 12 0) (av 8) 0 locals64 = MirStepNode.unsupported := rfl

/-- Recursive concrete `struct Node { next: *mut Node }`: `copyLayoutHasPlaceholder` stops at
pointer `backendRepr` and never cycles; also checks `ptLayoutIdx = 0` preserved with no `Node`
local declaration. -/
def nodeK : RigidTy := .adt "zc::Node" []
def L64_node : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lay 8 8 (.arbitrary [⟨0⟩] [0]) [1], ptrLay 8 0] }
def D64_node : List LocalDecl := [decl (ptrK nodeK) 1]

theorem recursive_node_ptLayoutIdx0_resolves :
    resolveCopyElemLayout D64_node L64_node (cp 0) (cp 0) = .ok 8 8 := rfl
theorem recursive_node_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 0) (cp 0) D64_node L64_node (av 4) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl

/-- Truncated generic multi-variant enum (`size = 1, align = 1, fieldLayouts = []`) is rejected. -/
def L64_truncEnum : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
          fields := .arbitrary [⟨0⟩] [0],
          variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
            [.arbitrary [] [], .arbitrary [⟨0⟩] [0]],
          isUninhabited := false, fieldLayouts := [] }
      , ptrLay 8 1 ] }
def D64_truncEnum : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.adt "zc::EnumT" [paramT])) 2]

theorem placeholder_truncated_enum_unresolved :
    resolveCopyElemLayout D64_truncEnum L64_truncEnum (cp 1) (cp 1) = .unsupported := rfl

/-- Unsized pointees (`*mut [u8]`, `*mut str`, `*mut (u8, [u8])`) fault `.ub` for all counts;
non-pointer-classified `.alias`/`.param`/ADT operands are `.unknown` (never spurious `.ub`);
opaque ADT pointer `*const Opaque` fails closed `.unsupported`; mismatched pointees (`*mut u32`
vs `*mut u8`) are `.unsupported` at `count = 0` and delegate at `count = 1`. -/
def D64_misc : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.slice (.uint .u8))) 0
  , decl (ptrK .str) 0
  , decl (ptrK (.tuple [.uint .u8, .slice (.uint .u8)])) 0
  , decl (.alias "zc::Alias" []) 0
  , decl paramT 0
  , decl opaqueK 0
  , decl (ptrK (ptrK opaqueK)) 0
  , decl (ptrK (.uint .u32)) 0
  , decl (ptrK (.uint .u8)) 0 ]

theorem unsized_slice_count0_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl
theorem unsized_str_count0_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl
theorem unsized_tuple_count1_ub :
    evalCopyNonOverlappingWithCount S64 (cp 3) (cp 3) D64_misc L64 (av 8) (av 8) 1 locals64 =
      MirStepNode.fail .ub := rfl
theorem alias_operand_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 4) (cp 4) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem param_operand_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 5) (cp 5) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem nonbox_adt_operand_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 6) (cp 6) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem opaque_adt_ptr_unresolved :
    resolveCopyElemLayout D64_misc L64 (cp 7) (cp 7) = .unsupported := rfl
theorem mismatched_pointees_count0_unsupported :
    evalCopyNonOverlappingWithCount S64 (cp 8) (cp 9) D64_misc L64 (av 8) (av 8) 0 locals64 =
      MirStepNode.unsupported := rfl
theorem mismatched_pointees_count1_delegates_ub :
    evalCopyNonOverlappingWithCount S64 (cp 8) (cp 9) D64_misc L64 (av 8) (av 8) 1 locals64 =
      MirStepNode.fail .ub := rfl

/-- Corrupted `[u8; 0]` with nonzero size `8` and corrupted wide pointer `*const [u8]` with
`align = 16` are rejected by `copyLayoutMatchesRigidTy` and fall back cleanly. -/
def L64_corrupt : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 8 8 (.array ⟨0⟩ 0) [4]
      , { size := ⟨16⟩, align := ⟨16⟩,
          backendRepr := .scalarPair
            (.initialized (.pointer 0) ⟨0, 2 ^ 64 - 1⟩)
            (.initialized (.int 64 false) ⟨0, 2 ^ 64 - 1⟩),
          fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1], variants := .single 0,
          isUninhabited := false, fieldLayouts := [] }
      , ptrLay 8 1
      , lay 1 1 .primitive
      , ptrLay 8 2 ] }
def D64_corrupt : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.array (.uint .u8) 0)) 3
  , decl (ptrK (.rawPtr .not (.slice (.uint .u8)))) 5 ]

theorem corrupt_array0_nonzero_size_rejected :
    resolveCopyElemLayout D64_corrupt L64_corrupt (cp 1) (cp 1) = .ok 0 1 := rfl
theorem corrupt_wide_ptr_align16_rejected :
    resolveCopyElemLayout D64_corrupt L64_corrupt (cp 2) (cp 2) = .ok 16 8 := rfl

/-- Cross-frame `callStack` borrow (`targetFrameDepth = 0` while active frame is at depth `1`):
`frameLocalDeclsAndLayoutsAtDepth` reads the saved caller's `localDecls`/`layouts`. -/
def callerBody64 : CapturedMir :=
  { defPath := "zc::caller", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [decl (.tuple []) 0, decl (.uint .u64) 1], basicBlocks := [],
    fnAbi :=
      { args := [], ret := { layout := lay 0 1 (.arbitrary [] []), mode := .ignore },
        conv := .rust, canUnwind := false },
    layouts := L64, allocations := [] }
def savedCaller64 : SavedCallerFrame :=
  { callerBody := callerBody64,
    frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨7, 8⟩)] },
    destination := loc 0 }
def S64_crossFrame : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals64 },
    memory := { emptyMemory with
      callStack := [savedCaller64],
      borrows := [bor 1 1],
      nextTag := 2 } }

theorem cross_frame_borrow_aligned_noop :
    evalCopyNonOverlappingWithCount S64_crossFrame (cp 2) (cp 3) D64 L64 (pv 1 0) (av 8) 0
      locals64 = MirStepNode.step (advanceStmt S64_crossFrame locals64) := rfl
theorem cross_frame_borrow_misaligned_ub :
    evalCopyNonOverlappingWithCount S64_crossFrame (cp 2) (cp 3) D64 L64 (pv 1 1) (av 8) 0
      locals64 = MirStepNode.fail .ub := rfl

/-! ### B2 soundness regressions (layout-index & compound field-layout validation) -/

/-- `entries[0] = ()` must NOT hijack an unresolved `_1 : Opaque` (`layoutIdx = 0`) into a ZST
`(0, 1)` layout (which would turn `count = 5` on misaligned pointers into a no-op). -/
def D64_unresAdt : List LocalDecl :=
  [decl (.tuple []) 0, decl opaqueK 0, decl (ptrK opaqueK) 0]

theorem unit0_cannot_hijack_unresolved_adt_decl :
    resolveCopyElemLayout D64_unresAdt L64 (cp 2) (cp 2) = .unsupported := rfl
theorem unit0_unresolved_adt_count5_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_unresAdt L64 (av 1) (av 1) 5
      locals64 = MirStepNode.fail .ub := rfl

/-- `entries[0] = *mut Packed` must NOT hijack an unresolved `_1 : *mut Align8` (`layoutIdx = 0`)
into `Packed`'s align-1 layout. -/
def D64_unresPtr : List LocalDecl :=
  [decl (ptrK packedK) 0, decl (ptrK align8K) 0]

theorem entry0_packed_ptr_cannot_hijack_unresolved_ptr_decl :
    resolveCopyElemLayout D64_unresPtr L64_projHijack (cp 1) (cp 1) = .unsupported := rfl

/-- `[u8; 4]` layout (`stride = 1, align = 1, fieldLayouts = [u8]`) must NOT validate as the
layout of `[u64; 4]`; `[u64; 4]` falls back to exact `.ok 32 8`, rejecting misaligned `av 1`
and `2^58 * 32 > isize::MAX` overflow. -/
def L64_arrHijack : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 1 1 .primitive
      , lay 4 1 (.array ⟨1⟩ 4) [1]
      , ptrLay 8 2 ] }
def D64_arrHijack : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.array (.uint .u64) 4)) 3]

theorem u8_arr4_cannot_hijack_u64_arr4_resolve :
    resolveCopyElemLayout D64_arrHijack L64_arrHijack (cp 1) (cp 1) = .ok 32 8 := rfl
theorem u8_arr4_cannot_hijack_u64_arr4_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_arrHijack L64_arrHijack (av 1) (av 1) 0
      locals64 = MirStepNode.fail .ub := rfl
theorem u8_arr4_cannot_hijack_u64_arr4_overflow_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_arrHijack L64_arrHijack (av 8) (av 8)
      (2 ^ 58) locals64 = MirStepNode.fail .ub := rfl

/-- `(u8, u8)` layout (`size = 2, align = 1, fieldLayouts = [u8, u8]`) must NOT validate as the
layout of `(u64, u64)`; a valid `(u64, u8)` layout (`size = 16, align = 8`) resolves cleanly. -/
def L64_tupHijack : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 1 1 .primitive
      , lay 8 8 .primitive
      , lay 2 1 (.arbitrary [⟨0⟩, ⟨1⟩] [0, 1]) [1, 1]
      , ptrLay 8 3
      , lay 16 8 (.arbitrary [⟨0⟩, ⟨8⟩] [0, 1]) [2, 1]
      , ptrLay 8 5 ] }
def D64_tupHijack : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u64])) 4
  , decl (ptrK (.tuple [.uint .u64, .uint .u8])) 6 ]

theorem u8_tuple_cannot_hijack_u64_tuple_unresolved :
    resolveCopyElemLayout D64_tupHijack L64_tupHijack (cp 1) (cp 1) = .unsupported := rfl
theorem valid_u64_u8_tuple_resolves :
    resolveCopyElemLayout D64_tupHijack L64_tupHijack (cp 2) (cp 2) = .ok 16 8 := rfl

/-! ### A2 soundness regressions (field offsets and array strides) -/

/-- A `(u64, u8)` layout placing the `u64` field at the misaligned offset `1` ("The fields are
properly aligned") and a `[Foo; 2]` layout whose stride `12` is not a multiple of its
alignment `8` are both rejected (fail closed), instead of resolving `(16, 8)` / `(24, 8)`. -/
def L64_a2 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 8 8 .primitive
      , lay 1 1 .primitive
      , lay 16 8 (.arbitrary [⟨1⟩, ⟨0⟩] [1, 0]) [1, 2]
      , ptrLay 8 3
      , lay 24 8 (.array ⟨12⟩ 2)
      , ptrLay 8 5 ] }
def D64_a2 : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u8])) 4
  , decl (ptrK (.array (.adt "zc::Foo" []) 2)) 6 ]

theorem misaligned_tuple_field_offset_rejected :
    resolveCopyElemLayout D64_a2 L64_a2 (cp 1) (cp 1) = .unsupported := rfl
theorem array_stride_not_multiple_of_align_rejected :
    resolveCopyElemLayout D64_a2 L64_a2 (cp 2) (cp 2) = .unsupported := rfl

/-! ### B3 soundness regressions (nested depth-16 truncation, overlapping tuple fields, multivariant tuples) -/

/-- Real `rustc-capture` depth-16 truncation occurs *nested* inside `fieldLayouts` (`Outer<Deep16<T>>`):
`Outer` has non-empty `fieldLayouts = [deep16Idx]` while `Deep16<T>` has empty `fieldLayouts = []`.
`copyLayoutHasPlaceholder` must reject truncated templates transitively, not only at the root. -/
def L64_nestedTrunc : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 0 1 (.arbitrary [⟨0⟩] [0])         -- 1: depth-16 truncated Deep16<T> (fieldLayouts = [])
      , lay 0 1 (.arbitrary [⟨0⟩] [0]) [1]     -- 2: Outer<Deep16<T>> (non-empty fieldLayouts!)
      , ptrLay 8 2 ] }
def D64_nestedTrunc : List LocalDecl :=
  [decl (.tuple []) 0, decl (ptrK (.adt "zc::OuterDeep" [paramT])) 3]

theorem nested_truncated_param_wrapper_unresolved :
    resolveCopyElemLayout D64_nestedTrunc L64_nestedTrunc (cp 1) (cp 1) = .unsupported := rfl
theorem nested_truncated_param_wrapper_count5_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_nestedTrunc L64_nestedTrunc (av 1)
      (av 1) 5 locals64 = MirStepNode.fail .ub := rfl

/-- Overlapping tuple fields (`(u64, u64)` with `size = 8`, both at offset `0`) must be rejected,
while valid ZST sharing (`(u64, ())` with `size = 8`, both at offset `0`) remains accepted; a
multi-variant enum layout (`.multiple`) must be rejected for a tuple. -/
def L64_b3Tup : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])                                  -- 0: ()
      , lay 8 8 .primitive                                          -- 1: u64
      , lay 8 8 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1]) [1, 1]              -- 2: corrupt overlapping (u64, u64)
      , ptrLay 8 2                                                  -- 3: *mut (u64, u64)
      , lay 8 8 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1]) [1, 0]              -- 4: valid (u64, ())
      , ptrLay 8 4                                                  -- 5: *mut (u64, ())
      , { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
          fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1],
          variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
            [.arbitrary [] [], .arbitrary [⟨1⟩] [0]],
          isUninhabited := false, fieldLayouts := [7, 7] }          -- 6: multivariant enum
      , lay 1 1 .primitive                                          -- 7: u8
      , ptrLay 8 6 ] }                                              -- 8: *mut (u8, u8)
def D64_b3Tup : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u64])) 3
  , decl (ptrK (.tuple [.uint .u64, .tuple []])) 5
  , decl (ptrK (.tuple [.uint .u8, .uint .u8])) 8 ]

theorem overlapping_tuple_fields_size8_rejected :
    resolveCopyElemLayout D64_b3Tup L64_b3Tup (cp 1) (cp 1) = .unsupported := rfl
theorem valid_tuple_with_zst_shared_offset0_resolves :
    resolveCopyElemLayout D64_b3Tup L64_b3Tup (cp 2) (cp 2) = .ok 8 8 := rfl
theorem multivariant_tuple_rejected :
    resolveCopyElemLayout D64_b3Tup L64_b3Tup (cp 3) (cp 3) = .unsupported := rfl

/-! ### B4 soundness regressions (absent-`fieldLayouts` ZST/pointer/param arrays and tuples) -/

/-- When `fieldLayouts = []`, corrupted layouts for `[(); 0]` (align 8), `[*mut u64; 4]` (stride 1),
`[*const (u8, [u8]); 4]` (thin stride 8), `[T; 4]`, `(*mut u64, *mut u64)` (size 4), and `(T, u64)`
(size 8) must all be rejected rather than accepted as authoritative. -/
def L64_b4 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])                           -- 0: ()
      , lay 0 8 (.array ⟨8⟩ 0)                               -- 1: corrupt [(); 0] align 8
      , ptrLay 8 1                                           -- 2: *mut [(); 0]
      , lay 4 1 (.array ⟨1⟩ 4)                               -- 3: corrupt [*mut u64; 4] stride 1
      , ptrLay 8 3                                           -- 4: *mut [*mut u64; 4]
      , lay 32 8 (.array ⟨8⟩ 4)                              -- 5: corrupt wide-ptr / [T; 4] array
      , ptrLay 8 5                                           -- 6: *mut [widePtr; 4] / *mut [T; 4]
      , lay 4 1 (.arbitrary [⟨0⟩, ⟨2⟩] [0, 1])              -- 7: corrupt (*mut u64, *mut u64) sz 4
      , ptrLay 8 7                                           -- 8: *mut (*mut u64, *mut u64)
      , lay 8 8 (.arbitrary [⟨0⟩, ⟨0⟩] [0, 1])              -- 9: corrupt (T, u64) sz 8
      , ptrLay 8 9 ] }                                       -- 10: *mut (T, u64)
def D64_b4 : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.array (.tuple []) 0)) 2
  , decl (ptrK (.array (ptrK (.uint .u64)) 4)) 4
  , decl (ptrK (.array widePtrK 4)) 6
  , decl (ptrK arrT4) 6
  , decl (ptrK (.tuple [ptrK (.uint .u64), ptrK (.uint .u64)])) 8
  , decl (ptrK (.tuple [paramT, .uint .u64])) 10 ]

theorem corrupt_unit_arr0_align8_no_false_ub :
    evalCopyNonOverlappingWithCount S64 (cp 1) (cp 1) D64_b4 L64_b4 (av 1) (av 1) 5 locals64 =
      noop := rfl
theorem corrupt_ptr_arr4_stride1_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_b4 L64_b4 (av 1) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl
theorem corrupt_wide_ptr_arr4_stride8_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 3) (cp 3) = .ok 64 8 := rfl
theorem corrupt_param_arr4_nil_fl_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 4) (cp 4) = .unsupported := rfl
theorem corrupt_ptr_tuple_small_size_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 5) (cp 5) = .unsupported := rfl
theorem corrupt_param_tuple_nil_fl_rejected :
    resolveCopyElemLayout D64_b4 L64_b4 (cp 6) (cp 6) = .unsupported := rfl

/-! ### A4 regressions: arrays / non-empty tuples without `fieldLayouts` fail closed -/

/-- `rustc-capture` interns element / field layouts for every array and non-empty tuple above
its depth-16 limit, so an absent `fieldLayouts` list never determines a layout: a `(u64, u8)`
layout with `size = 9, align = 1` (whose primitive sizes sum to `9`) and a `[u64; 2]` layout
with `align = 1` are rejected; the tuple is then `.unsupported` and the array falls back to the
exact structural `(16, 8)`, so a 4-aligned dangling pointer is `.ub`. -/
def L64_a4 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries :=
      [ lay 0 1 (.arbitrary [] [])
      , lay 9 1 (.arbitrary [⟨0⟩, ⟨8⟩] [0, 1])
      , ptrLay 8 1
      , lay 16 1 (.array ⟨8⟩ 2)
      , ptrLay 8 3 ] }
def D64_a4 : List LocalDecl :=
  [ decl (.tuple []) 0
  , decl (ptrK (.tuple [.uint .u64, .uint .u8])) 2
  , decl (ptrK (.array (.uint .u64) 2)) 4 ]

theorem nil_fl_tuple_size9_align1_rejected :
    resolveCopyElemLayout D64_a4 L64_a4 (cp 1) (cp 1) = .unsupported := rfl
theorem nil_fl_u64_array_align1_falls_back_exact :
    resolveCopyElemLayout D64_a4 L64_a4 (cp 2) (cp 2) = .ok 16 8 := rfl
theorem nil_fl_u64_array_align1_misaligned_ub :
    evalCopyNonOverlappingWithCount S64 (cp 2) (cp 2) D64_a4 L64_a4 (av 4) (av 8) 0 locals64 =
      MirStepNode.fail .ub := rfl

end Anneal.Tests.ZeroCountCopyAlign.V08

/-! ## §3. Axiom audit (standard axioms only: no `sorryAx`, no `Lean.ofReduceBool`) -/

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zst_any_count_noop_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zst_any_count_noop_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zero_count_src_violation_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zero_count_src_violation_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zero_count_dst_violation_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zero_count_dst_violation_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.malformed_src_ub_univ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.malformed_src_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unresolved_nonzero_delegates_univ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unresolved_nonzero_delegates_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.live_aligned_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.live_aligned_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.live_disabled_tag_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.live_disabled_tag_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.dangling_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.dangling_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.dangling_large_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.dangling_large_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.null_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.null_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.null_unbacked_ptr_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.null_unbacked_ptr_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.null_zst_count5_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.null_zst_count5_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nonzero_null_u64_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nonzero_null_u64_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nonzero_null_dst_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nonzero_null_dst_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_live_offset1_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_live_offset1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_live_dst_offset1_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_live_dst_offset1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_dangling_9_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_dangling_9_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_unbacked_ptr_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_unbacked_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_fnptr_like_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_fnptr_like_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unbacked_aligned_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unbacked_aligned_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.copyMisalignedZeroBody_shape_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.copyMisalignedZeroBody_shape_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.copyAlignedZeroBody_shape_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.copyAlignedZeroBody_shape_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_scalar_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_scalar_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.out_of_range_scalar_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.out_of_range_scalar_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_ptr_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_ptr_nonzero_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_ptr_nonzero_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unit_value_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unit_value_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.aggregate_value_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.aggregate_value_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nonptr_operand_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nonptr_operand_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nonptr_operand_nonzero_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nonptr_operand_nonzero_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.out_of_range_count_bits_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.out_of_range_count_bits_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_count_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.wrong_width_count_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.resolve_arrU64x0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.resolve_arrU64x0

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zst_aligned_count5_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zst_aligned_count5_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zst_misaligned_count5_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zst_misaligned_count5_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zst_dead_borrow_count5_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zst_dead_borrow_count5_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.zst_out_of_range_count_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.zst_out_of_range_count_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_zst_out_of_range_count_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_zst_out_of_range_count_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.out_of_range_count_ub_univ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.out_of_range_count_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.overflow_u64_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.overflow_u64_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.overflow_u64_null_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.overflow_u64_null_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.resolve_widePtr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.resolve_widePtr

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.overflow_widePtr_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.overflow_widePtr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.widePtr_count0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.widePtr_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.opaque_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.opaque_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.opaque_count0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.opaque_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.opaque_count0_malformed_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.opaque_count0_malformed_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.kleene_unsupported_and_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.kleene_unsupported_and_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.kleene_ub_and_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.kleene_ub_and_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.kleene_unsupported_and_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.kleene_unsupported_and_ok

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.kleene_dead_src_misaligned_dst_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.kleene_dead_src_misaligned_dst_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.kleene_misaligned_src_dead_dst_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.kleene_misaligned_src_dead_dst_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.dead_borrow_align8_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.dead_borrow_align8_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.packed_field_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.packed_field_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.packed_field_plus7_in_outer_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.packed_field_plus7_in_outer_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.packed_field_in_outer_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.packed_field_in_outer_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.u128_tuple_field_no_false_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.u128_tuple_field_no_false_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.u128_tuple_field_odd_offset_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.u128_tuple_field_odd_offset_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.large_offset_aligned_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.large_offset_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.large_offset_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.large_offset_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_wrapper_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_wrapper_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_wrapper_count5_not_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_wrapper_count5_not_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_array_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_array_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_truncated_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_truncated_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_nested9_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_nested9_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.monomorphized_wrapper_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.monomorphized_wrapper_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.monomorphized_wrapper_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.monomorphized_wrapper_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_resolve_u32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_resolve_u32

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_field_aligned_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_field_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_field_odd_offset_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_field_odd_offset_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_decl_u32_aligned_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_decl_u32_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_decl_u32_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_decl_u32_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_8byte_ptr_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_8byte_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_overflow_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_overflow_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_misaligned_count0_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_misaligned_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_misaligned_dangling_count0_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_misaligned_dangling_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_malformed_count0_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_malformed_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_aligned_null_count0_steps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_aligned_null_count0_steps

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_live_aligned_count0_steps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_live_aligned_count0_steps

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_inherits_withCount_univ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_inherits_withCount_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.call_zero_count_src_violation_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.call_zero_count_src_violation_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.uninit_value_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.uninit_value_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.uninit_dst_value_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.uninit_dst_value_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zst_any_count_noop_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zst_any_count_noop_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zero_count_src_violation_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zero_count_src_violation_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zero_count_dst_violation_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zero_count_dst_violation_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.malformed_src_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.malformed_src_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unresolved_nonzero_delegates_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unresolved_nonzero_delegates_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.live_aligned_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.live_aligned_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.live_disabled_tag_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.live_disabled_tag_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.dangling_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.dangling_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.dangling_large_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.dangling_large_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.null_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.null_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.null_unbacked_ptr_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.null_unbacked_ptr_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.null_zst_count5_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.null_zst_count5_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nonzero_null_u64_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nonzero_null_u64_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nonzero_null_dst_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nonzero_null_dst_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_live_offset1_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_live_offset1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_live_dst_offset1_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_live_dst_offset1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_dangling_9_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_dangling_9_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_unbacked_ptr_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_unbacked_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_fnptr_like_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_fnptr_like_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unbacked_aligned_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unbacked_aligned_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.copyMisalignedZeroBody_shape_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.copyMisalignedZeroBody_shape_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.copyAlignedZeroBody_shape_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.copyAlignedZeroBody_shape_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_scalar_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_scalar_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.out_of_range_scalar_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.out_of_range_scalar_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_ptr_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_ptr_nonzero_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_ptr_nonzero_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unit_value_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unit_value_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.aggregate_value_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.aggregate_value_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nonptr_operand_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nonptr_operand_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nonptr_operand_nonzero_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nonptr_operand_nonzero_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.out_of_range_count_bits_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.out_of_range_count_bits_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_count_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.wrong_width_count_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.resolve_arrU64x0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.resolve_arrU64x0

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zst_aligned_count5_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zst_aligned_count5_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zst_misaligned_count5_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zst_misaligned_count5_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zst_dead_borrow_count5_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zst_dead_borrow_count5_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.zst_out_of_range_count_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.zst_out_of_range_count_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_zst_out_of_range_count_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_zst_out_of_range_count_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.out_of_range_count_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.out_of_range_count_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.overflow_u64_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.overflow_u64_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.overflow_u64_null_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.overflow_u64_null_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.resolve_widePtr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.resolve_widePtr

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.overflow_widePtr_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.overflow_widePtr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.widePtr_count0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.widePtr_count0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.opaque_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.opaque_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.opaque_count0_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.opaque_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.opaque_count0_malformed_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.opaque_count0_malformed_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.kleene_unsupported_and_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.kleene_unsupported_and_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.kleene_ub_and_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.kleene_ub_and_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.kleene_unsupported_and_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.kleene_unsupported_and_ok

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.kleene_dead_src_misaligned_dst_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.kleene_dead_src_misaligned_dst_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.kleene_misaligned_src_dead_dst_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.kleene_misaligned_src_dead_dst_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.dead_borrow_align8_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.dead_borrow_align8_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.packed_field_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.packed_field_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.packed_field_plus7_in_outer_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.packed_field_plus7_in_outer_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.packed_field_in_outer_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.packed_field_in_outer_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.u128_tuple_field_no_false_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.u128_tuple_field_no_false_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.u128_tuple_field_odd_offset_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.u128_tuple_field_odd_offset_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.large_offset_aligned_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.large_offset_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.large_offset_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.large_offset_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_wrapper_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_wrapper_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_wrapper_count5_not_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_wrapper_count5_not_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_array_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_array_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_truncated_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_truncated_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_nested9_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_nested9_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.monomorphized_wrapper_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.monomorphized_wrapper_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.monomorphized_wrapper_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.monomorphized_wrapper_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_resolve_u32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_resolve_u32

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_field_aligned_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_field_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_field_odd_offset_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_field_odd_offset_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_decl_u32_aligned_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_decl_u32_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_decl_u32_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_decl_u32_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_8byte_ptr_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_8byte_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_overflow_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_overflow_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_misaligned_count0_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_misaligned_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_misaligned_dangling_count0_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_misaligned_dangling_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_malformed_count0_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_malformed_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_aligned_null_count0_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_aligned_null_count0_steps

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_live_aligned_count0_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_live_aligned_count0_steps

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_inherits_withCount_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_inherits_withCount_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.call_zero_count_src_violation_ub_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.call_zero_count_src_violation_ub_univ

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_wrapper_count0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_wrapper_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.non_ptr_u8arr8_cannot_hijack_ptr_resolve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.non_ptr_u8arr8_cannot_hijack_ptr_resolve

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.non_ptr_u8arr8_cannot_hijack_ptr_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.non_ptr_u8arr8_cannot_hijack_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.non_ptr_packed8_cannot_hijack_ptr_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.non_ptr_packed8_cannot_hijack_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.projected_ptr_cannot_hijack_entry0_packed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.projected_ptr_cannot_hijack_entry0_packed

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.truncated_arr0_param_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.truncated_arr0_param_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.truncated_arr0_param_count5_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.truncated_arr0_param_count5_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_arr0_u64_recovers_align8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_arr0_u64_recovers_align8

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.never_rejects_overaligned_layout' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.never_rejects_overaligned_layout

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.never_count0_aligned1_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.never_count0_aligned1_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_atLeast2_off0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_atLeast2_off0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_atLeast2_off1_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.target32_u32_tuple_atLeast2_off1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.global_align8_off0_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.global_align8_off0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.global_align8_off1_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.global_align8_off1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.global_align4_off1_u64_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.global_align4_off1_u64_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.global_align4_off0_u64_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.global_align4_off0_u64_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.global_nonpow2_align3_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.global_nonpow2_align3_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.recursive_node_ptLayoutIdx0_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.recursive_node_ptLayoutIdx0_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.recursive_node_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.recursive_node_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_truncated_enum_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.placeholder_truncated_enum_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unsized_slice_count0_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unsized_slice_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unsized_str_count0_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unsized_str_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unsized_tuple_count1_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unsized_tuple_count1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.alias_operand_count0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.alias_operand_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.param_operand_count0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.param_operand_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nonbox_adt_operand_count0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nonbox_adt_operand_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.opaque_adt_ptr_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.opaque_adt_ptr_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.mismatched_pointees_count0_unsupported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.mismatched_pointees_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.mismatched_pointees_count1_delegates_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.mismatched_pointees_count1_delegates_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_array0_nonzero_size_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_array0_nonzero_size_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_wide_ptr_align16_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_wide_ptr_align16_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.cross_frame_borrow_aligned_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.cross_frame_borrow_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.cross_frame_borrow_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.cross_frame_borrow_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_wrapper_count0_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_wrapper_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.non_ptr_u8arr8_cannot_hijack_ptr_resolve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.non_ptr_u8arr8_cannot_hijack_ptr_resolve

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.non_ptr_u8arr8_cannot_hijack_ptr_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.non_ptr_u8arr8_cannot_hijack_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.non_ptr_packed8_cannot_hijack_ptr_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.non_ptr_packed8_cannot_hijack_ptr_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.projected_ptr_cannot_hijack_entry0_packed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.projected_ptr_cannot_hijack_entry0_packed

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.truncated_arr0_param_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.truncated_arr0_param_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.truncated_arr0_param_count5_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.truncated_arr0_param_count5_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_arr0_u64_recovers_align8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_arr0_u64_recovers_align8

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.never_rejects_overaligned_layout' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.never_rejects_overaligned_layout

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.never_count0_aligned1_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.never_count0_aligned1_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_atLeast2_off0_unsupported' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_atLeast2_off0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_atLeast2_off1_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.target32_u32_tuple_atLeast2_off1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.global_align8_off0_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.global_align8_off0_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.global_align8_off1_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.global_align8_off1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.global_align4_off1_u64_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.global_align4_off1_u64_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.global_align4_off0_u64_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.global_align4_off0_u64_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.global_nonpow2_align3_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.global_nonpow2_align3_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.recursive_node_ptLayoutIdx0_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.recursive_node_ptLayoutIdx0_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.recursive_node_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.recursive_node_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_truncated_enum_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.placeholder_truncated_enum_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unsized_slice_count0_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unsized_slice_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unsized_str_count0_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unsized_str_count0_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unsized_tuple_count1_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unsized_tuple_count1_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.alias_operand_count0_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.alias_operand_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.param_operand_count0_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.param_operand_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nonbox_adt_operand_count0_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nonbox_adt_operand_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.opaque_adt_ptr_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.opaque_adt_ptr_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.mismatched_pointees_count0_unsupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.mismatched_pointees_count0_unsupported

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.mismatched_pointees_count1_delegates_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.mismatched_pointees_count1_delegates_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_array0_nonzero_size_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_array0_nonzero_size_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_wide_ptr_align16_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_wide_ptr_align16_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.cross_frame_borrow_aligned_noop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.cross_frame_borrow_aligned_noop

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.cross_frame_borrow_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.cross_frame_borrow_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unit0_cannot_hijack_unresolved_adt_decl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unit0_cannot_hijack_unresolved_adt_decl

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.unit0_unresolved_adt_count5_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.unit0_unresolved_adt_count5_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.entry0_packed_ptr_cannot_hijack_unresolved_ptr_decl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.entry0_packed_ptr_cannot_hijack_unresolved_ptr_decl

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.u8_arr4_cannot_hijack_u64_arr4_resolve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.u8_arr4_cannot_hijack_u64_arr4_resolve

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.u8_arr4_cannot_hijack_u64_arr4_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.u8_arr4_cannot_hijack_u64_arr4_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.u8_arr4_cannot_hijack_u64_arr4_overflow_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.u8_arr4_cannot_hijack_u64_arr4_overflow_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.u8_tuple_cannot_hijack_u64_tuple_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.u8_tuple_cannot_hijack_u64_tuple_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.valid_u64_u8_tuple_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.valid_u64_u8_tuple_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_tuple_field_offset_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.misaligned_tuple_field_offset_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.array_stride_not_multiple_of_align_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.array_stride_not_multiple_of_align_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unit0_cannot_hijack_unresolved_adt_decl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unit0_cannot_hijack_unresolved_adt_decl

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.unit0_unresolved_adt_count5_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.unit0_unresolved_adt_count5_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.entry0_packed_ptr_cannot_hijack_unresolved_ptr_decl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.entry0_packed_ptr_cannot_hijack_unresolved_ptr_decl

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.u8_arr4_cannot_hijack_u64_arr4_resolve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.u8_arr4_cannot_hijack_u64_arr4_resolve

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.u8_arr4_cannot_hijack_u64_arr4_misaligned_ub' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.u8_arr4_cannot_hijack_u64_arr4_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.u8_arr4_cannot_hijack_u64_arr4_overflow_ub' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.u8_arr4_cannot_hijack_u64_arr4_overflow_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.u8_tuple_cannot_hijack_u64_tuple_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.u8_tuple_cannot_hijack_u64_tuple_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.valid_u64_u8_tuple_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.valid_u64_u8_tuple_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_tuple_field_offset_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.misaligned_tuple_field_offset_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.array_stride_not_multiple_of_align_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.array_stride_not_multiple_of_align_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nested_truncated_param_wrapper_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nested_truncated_param_wrapper_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nested_truncated_param_wrapper_count5_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nested_truncated_param_wrapper_count5_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.overlapping_tuple_fields_size8_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.overlapping_tuple_fields_size8_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.valid_tuple_with_zst_shared_offset0_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.valid_tuple_with_zst_shared_offset0_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.multivariant_tuple_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.multivariant_tuple_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nested_truncated_param_wrapper_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nested_truncated_param_wrapper_unresolved

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nested_truncated_param_wrapper_count5_misaligned_ub' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nested_truncated_param_wrapper_count5_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.overlapping_tuple_fields_size8_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.overlapping_tuple_fields_size8_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.valid_tuple_with_zst_shared_offset0_resolves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.valid_tuple_with_zst_shared_offset0_resolves

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.multivariant_tuple_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.multivariant_tuple_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_unit_arr0_align8_no_false_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_unit_arr0_align8_no_false_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_ptr_arr4_stride1_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_ptr_arr4_stride1_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_wide_ptr_arr4_stride8_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_wide_ptr_arr4_stride8_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_param_arr4_nil_fl_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_param_arr4_nil_fl_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_ptr_tuple_small_size_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_ptr_tuple_small_size_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_param_tuple_nil_fl_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.corrupt_param_tuple_nil_fl_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nil_fl_tuple_size9_align1_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nil_fl_tuple_size9_align1_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nil_fl_u64_array_align1_falls_back_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nil_fl_u64_array_align1_falls_back_exact

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V06.nil_fl_u64_array_align1_misaligned_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V06.nil_fl_u64_array_align1_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_unit_arr0_align8_no_false_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_unit_arr0_align8_no_false_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_ptr_arr4_stride1_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_ptr_arr4_stride1_misaligned_ub

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_wide_ptr_arr4_stride8_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_wide_ptr_arr4_stride8_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_param_arr4_nil_fl_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_param_arr4_nil_fl_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_ptr_tuple_small_size_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_ptr_tuple_small_size_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_param_tuple_nil_fl_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.corrupt_param_tuple_nil_fl_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nil_fl_tuple_size9_align1_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nil_fl_tuple_size9_align1_rejected

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nil_fl_u64_array_align1_falls_back_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nil_fl_u64_array_align1_falls_back_exact

/-- info: 'Anneal.Tests.ZeroCountCopyAlign.V08.nil_fl_u64_array_align1_misaligned_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.Tests.ZeroCountCopyAlign.V08.nil_fl_u64_array_align1_misaligned_ub
