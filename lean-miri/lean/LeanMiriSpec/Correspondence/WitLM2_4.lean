/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM2_4
import LeanMiriSpec.Correspondence.WitLM2_1

/-!
# Non-Vacuity Witnesses for the `LM-2.4` Correspondence

The `LM-2.4` theorems would hold vacuously if their hypotheses could not be met
together. This module builds `union U { a: u8, b: u32 }` (four bytes, both
fields at offset `0`), a body that writes, copies, and reads it, and reuses the
`[u16; 3]` array of `WitLM2_1`, to prove that:

1. `_1 = U { a: 5 }; _2 = copy (_1.0: u8)` steps normally in both machines, to
   related states (`lm24_write_read_same_field_steps`);
2. `_1 = U { a: 5 }; _4 = copy _1; _2 = copy (_4.0: u8)` does too, and after the
   copy `_4`'s allocation initializes byte `0` but not the whole union
   (`lm24_copy_initMask_steps`). Each step after the first applies the next
   theorem to the facts that the previous step re-established
   (`lm24_agg_copy_chain`);
3. reading the larger field `_4.1: u32` of that copy is undefined behavior in
   both machines (`lm24_copy_larger_field_ub`);
4. `Subslice` projections of the array agree in bounds, counted from the start
   or from the end, and out of bounds (`lm24_subslice_witness`);
5. `_1 = U { a: 5 }; _1.0 = 7; _2 = copy (_1.0: u8)` steps normally in both
   machines, the field write updating the union's allocation in place
   (`lm24_field_write_read_steps`);
6. `_1.0 = 7` on the uninitialized `_1` steps normally in both machines,
   initializing `_1` via `uninitFieldWriteShell?` + `writeProjectedForLocal` in
   Anneal and writing byte `0` of a fresh allocation in `lean-miri`
   (`lm24_field_write_uninit_simulation`); likewise the nonzero-field write
   `_1.1 = 0x01020304_u32` on the uninitialized `_1` writes bytes `[0, 4)`
   (`lm24_field1_write_uninit_simulation`), and chained *narrower* projected
   field writes `_1.0 = 0x77_u8; _1.0 = 0x88_u8` onto `_1 = U { b: 0x01020304_u32 }`
   retain the high bytes `[0x03, 0x02, 0x01]` in both Anneal's raw-byte overlay
   and `lean-miri`'s allocation so `_3 = copy (_1.1: u32)` reads
   `0x01020388_u32` and `StorageDead(_1)` frees `_1`'s backing allocation with
   `StateRelLM2_4` preserved after every step
   (`lm24_narrower_field_write_retains_high_bytes_simulation`);
7. `_1 = U { a: 5 }; _4 = move _1; _2 = copy (_4.0: u8)` steps normally in both
   machines (`lm24_move_read_steps`);
8. the operands `copy _1[1..3]` and `move _1[2..len - 2]` on the array agree,
   the first in value and place and the second as undefined behavior, as does
   `copy _1[1..3]` on the uninitialized array
   (`lm24_subslice_operand_witness`);
9. `_1 = U { b: 0x01020304_u32 }; _2 = copy (_1.0: u8)` (`activeField = some 1`
   via `evalRvalue_union_aggregate_activeField_simulation`) steps both the
   aggregate and the type-punning read in lockstep, reading the low byte
   `0x04_u8` (`lm24_rvalue_union_aggregate_activeField_witness`,
   `lm24_type_punning_read_simulation`);
10. `_1 = U { a: 5 }; _1.1 = 0x01020304_u32` steps both the aggregate and the
    nonzero-field write in lockstep, updating `_1` to
    `[.unit, .scalar ⟨0x01020304, 4⟩]` in Anneal and overwriting bytes `[0, 4)`
    at offset `0` in `lean-miri` (`lm24_nonzero_field_write_simulation`);
11. `_2 = move _1[1..3]; _3 = copy _1[1..1]` steps both `[u16; 2]` and
    `[u16; 0]` subslice assignments in lockstep while keeping `_1` initialized,
    whereas out-of-bounds `_3 = copy _1[2..len - 2]` and uninitialized
    `_2 = move _1[1..3]` report undefined behavior in both
    (`lm24_subslice_assign_steps`, `lm24_subslice_assign_oob_and_uninit_ub`);
12. `copy _3[0..0]` on an uninitialized memory-backed `[u16; 0]` local reports
    undefined behavior in both machines when the allocation mask is
    `.Lazy false`, and succeeds in `lean-miri` (while Anneal reports `.ub`)
    when the allocation mask is `InitMask.new _ true`
    (`lm24_zero_uninit_indirect_subslice_witness`);
13. the 6-step lifecycle and in-place overwrite chain
    `_1 = U { a: 5 }; _4 = U { 0: 0x01020304_u32 }; _4 = copy _1;
     _1 = U { 0: 0x05060708_u32 }; StorageDead(_1); StorageLive(_1)`
    steps normally in both machines (narrowing `_4`'s `InitMask` from `4` bytes
    down to `1` byte via `step_union_whole_copy_or_move_overwrite_simulation`,
    widening `_1` from `1` byte to `4` bytes via
    `step_union_aggregate_overwrite_simulation`, freeing `_1`'s stack allocation
    on `StorageDead(_1)`, and re-activating `_1` on `StorageLive(_1)`), while
    writing to a `.dead` union local reports UB in both
    (`lm24_overwrite_and_lifecycle_steps`);
14. self-copy `_1 = copy _1` on `U { a: 5 }` steps normally in Anneal while
    `lean-miri` rejects the overlapping copy range as UB
    (`lm24_union_self_copy_overlap_divergence`);
15. whole-union `_4 = copy _1` on an uninitialized indirect union (`InitMask.new _ false`,
    `MaybeUninit::uninit()`) reports `.ub` in Anneal while `lean-miri` copies `4`
    uninitialized bytes (`lm24_union_copy_indirect_uninit_divergence`);
16. overwriting `_1 = U { 0: 0x01020304_u32 }` with narrower `_1 = U { a: 0x77_u8 }`
    replaces the whole union in Anneal, while `lean-miri` updates byte `0` to
    `0x77`, preserves `IsUnionPrefixMask 4 4`, and retains the trailing high
    bytes `#[0x03, 0x02, 0x01]` (`lm24_union_agg_smaller_overwrite_divergence`);
17. `_1 = U { a: 5 }; _3 = [copy (_1.0: u8); 3]` steps normally in both machines
    to `[5_u8, 5_u8, 5_u8]`, whereas repeating the wider uninitialized field
    `_3 = [copy (_1.1: u32); 3]` reports UB in both
    (`lm24_repeat_union_field_steps`);
18. nested `Subslice` projections (`_1[0..3][1..2]` and out-of-bounds
    `_1[0..3][2..len - 2]`), in-place subslice destination overwrites
    (`_2 = move _1[1..3]; _2 = copy _1[0..2]`), and projected subslice element
    writes (`_1[1..3][0 of 2] = 0x0099_u16`) all step in lockstep
    (`lm24_nested_subslice_witness`,
    `lm24_subslice_overwrite_and_elem_write_witness`).

Every Anneal step is computed exactly, by `rfl`.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. The Union `U { a: u8, b: u32 }` -/

def lm24U8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def lm24U32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `union U { a: u8, b: u32 }`: four bytes, both fields at offset `0`. -/
def lm24ULayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false, fieldLayouts := [0, 1] }

def lm24Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lm24U8Layout, lm24U32Layout, lm24ULayout] }

def lm24U8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def lm24U32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def lm24UTy : Ty := { kind := .adt "U" [], layoutIdx := 2 }

def lm24Decl (t : Ty) : LocalDecl := { mutability := .mut, ty := t, debugName := none }

def lm24ConstU8 (n : Nat) : ConstOperand := { ty := lm24U8Ty, val := .scalar (.int ⟨n, 1⟩) }
def lm24ConstU32 (n : Nat) : ConstOperand := { ty := lm24U32Ty, val := .scalar (.int ⟨n, 4⟩) }

/-- `_u = U { a: const n_u8 }`. -/
def lm24AggStmt (u n : Nat) : MirAst.Statement :=
  mkStmt (.assign (local_ u) (.aggregate (.adt "U" 0 (some 0)) [.constant (lm24ConstU8 n)]))

/-- `_u = U { b: const n_u32 }` (`activeField = some 1`). -/
def lm24AggU32Stmt (u n : Nat) : MirAst.Statement :=
  mkStmt (.assign (local_ u) (.aggregate (.adt "U" 0 (some 1)) [.constant (lm24ConstU32 n)]))

/-- `_u.0 = const n_u8`. -/
def lm24FieldWriteStmt (u n : Nat) : MirAst.Statement :=
  mkStmt (.assign ⟨u, [.field 0 lm24U8Ty]⟩ (.use (.constant (lm24ConstU8 n))))

/-- `_u.1 = const n_u32`. -/
def lm24Field1WriteU32Stmt (u n : Nat) : MirAst.Statement :=
  mkStmt (.assign ⟨u, [.field 1 lm24U32Ty]⟩ (.use (.constant (lm24ConstU32 n))))

theorem lm24_wt_U : WellTypedUnionTy lm24Layouts lm24UTy 4 :=
  WellTypedUnionTy.of_fullRangeScalarFields
    (Or.inr (Or.inr (Or.inl rfl)))
    ⟨2, rfl, by decide⟩
    rfl rfl (by decide)
    rfl (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by
      intro idx flIdx hget
      match idx with
      | 0 =>
        injection hget with h; subst h
        refine ⟨lm24U8Layout, rfl, rfl, Or.inl rfl, by decide, ?_⟩
        intro prim vr hrepr
        injection hrepr with hs; injection hs with _ hvr; subst hvr
        exact ⟨rfl, rfl⟩
      | 1 =>
        injection hget with h; subst h
        refine ⟨lm24U32Layout, rfl, rfl, Or.inr (Or.inr (Or.inl rfl)), by decide, ?_⟩
        intro prim vr hrepr
        injection hrepr with hs; injection hs with _ hvr; subst hvr
        exact ⟨rfl, rfl⟩
      | _ + 2 => simp [lm24ULayout, get?] at hget)

theorem lm24_isPrim_u8 : IsPrimScalarTy lm24U8Ty := Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))
theorem lm24_isPrim_u32 : IsPrimScalarTy lm24U32Ty := Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))

/-! ## 2. Body and Initial States -/

def lm24FnAbi : FnAbi :=
  { args := [], ret := { layout := lm24U32Layout, mode := .direct }, conv := .rust,
    canUnwind := false }

/-- Locals: `_0: u32`, `_1: U`, `_2: u8`, `_3: u32`, `_4: U`.
- `bb0`: `_1 = U { a: 5 }; _4 = copy _1; _2 = copy (_4.0: u8)`
- `bb1`: `_1 = U { a: 5 }; _2 = copy (_1.0: u8)`
- `bb2`: `_1 = U { a: 5 }; _4 = copy _1; _3 = copy (_4.1: u32)`
- `bb3`: `_1 = U { a: 5 }; _1.0 = 7; _2 = copy (_1.0: u8)`
- `bb4`: `_1.0 = 7` (on the uninitialized `_1`)
- `bb5`: `_1 = U { a: 5 }; _4 = move _1; _2 = copy (_4.0: u8)`
- `bb6`: `_1 = U { b: 0x01020304_u32 }; _2 = copy (_1.0: u8)`
- `bb7`: `_1 = U { a: 5 }; _1.1 = 0x01020304_u32`
- `bb8`: `_1.1 = 0x01020304_u32` (on the uninitialized `_1`)
- `bb9`: `_1 = U { b: 0x01020304_u32 }; _1.0 = 0x77_u8; _1.0 = 0x88_u8; _3 = copy (_1.1: u32); StorageDead(_1)` -/
def lm24Body : CapturedMir where
  defPath := "lm_2_4_witness::unions"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm24Decl lm24U32Ty, lm24Decl lm24UTy, lm24Decl lm24U8Ty, lm24Decl lm24U32Ty,
    lm24Decl lm24UTy]
  basicBlocks := [
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 2) (.use (unionFieldReadOperand false 4 0 lm24U8Ty)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 2) (.use (unionFieldReadOperand false 1 0 lm24U8Ty)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 3) (.use (unionFieldReadOperand false 4 1 lm24U32Ty)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        lm24FieldWriteStmt 1 7,
        mkStmt (.assign (local_ 2) (.use (unionFieldReadOperand false 1 0 lm24U8Ty)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [lm24FieldWriteStmt 1 7],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 4) (.use (.move (local_ 1)))),
        mkStmt (.assign (local_ 2) (.use (unionFieldReadOperand false 4 0 lm24U8Ty)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggU32Stmt 1 0x01020304,
        mkStmt (.assign (local_ 2) (.use (unionFieldReadOperand false 1 0 lm24U8Ty)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        lm24Field1WriteU32Stmt 1 0x01020304],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [lm24Field1WriteU32Stmt 1 0x01020304],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggU32Stmt 1 0x01020304,
        lm24FieldWriteStmt 1 0x77,
        lm24FieldWriteStmt 1 0x88,
        mkStmt (.assign (local_ 3) (.use (unionFieldReadOperand false 1 1 lm24U32Ty))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm24FnAbi
  layouts := lm24Layouts
  allocations := []

theorem lm24_phase : ∀ p, lm24Body.phase ≠ .other p := by
  intro p h; cases h

/-- The Anneal state at the start of block `b` with all five locals live and
uninitialized. -/
def lm24InitAnneal (b : Nat) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := 0,
               locals := [.uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm24Body []).memory }

def lm24InitMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm24Body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm24U32Ty lm24Layouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨b, 0⟩ }

def lm24InitMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24InitMiriFrame b]⟩, machine := AnnealMachine.empty }

theorem lm24_init_stateRel (b : Nat) :
    StateRel lm24Body (lm24InitAnneal b) (lm24InitMiri b) := by
  refine StateRel.mk (lm24InitMiriFrame b) rfl rfl ⟨translateTy lm24U32Ty lm24Layouts, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 => rintro ⟨⟩
      | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  have himm : ∀ d : LocalDecl, LocalRel AnnealMachine.empty d lm24Layouts .uninit
      { value := .live (.immediate .uninit), layout := none } :=
    fun _ => .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  match i with
  | 0 | 1 | 2 | 3 | 4 =>
    have hs : slot = .uninit := by simpa [lm24InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24InitMiriFrame] using hmls.symm
    subst hs hm
    exact himm decl
  | _ + 5 =>
    simp [lm24Body, get?] at hdecl

theorem lm24_init_imm (b j : Nat) : IsImmediateFrameLocal (lm24InitMiriFrame b) j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 | 3 | 4 => simp [lm24InitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 5 => simp [lm24InitMiriFrame] at hmls

theorem lm24_init_frame_imm (b j : Nat) :
    ∀ tf, (lm24InitMiri b).stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
  intro tf h
  have htf : lm24InitMiriFrame b = tf := by simpa [lm24InitMiri] using h
  subst htf
  exact lm24_init_imm b j

theorem lm24_nodup_empty : LiveAllocsNodup AnnealMachine.empty :=
  List.Pairwise.nil

theorem lm24_canReserve_empty : CanReserveAllocId AnnealMachine.empty.memory :=
  MemoryHighWater.empty.canReserveAllocId

theorem lm24_constU8_wt (n : Nat) (hn : n < 256)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand lm24Body tf (.constant (lm24ConstU8 n)) lm24U8Ty :=
  .constScalar (lm24ConstU8 n) ⟨n, 1⟩ rfl lm24_isPrim_u8 (Or.inl rfl) hn rfl
    (fun h => nomatch h) (fun h => nomatch h)

/-! ## 3. Writing and Reading the Same Field -/

/-- The Anneal states of block `1` after `_1 = U { a: 5 }` and after
`_2 = copy (_1.0: u8)`. -/
def lm24Bb1S1 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit]), .uninit, .uninit, .uninit] }
    memory := (initMachineState lm24Body []).memory }

def lm24Bb1S2 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit]), .init (.scalar ⟨5, 1⟩),
                 .uninit, .uninit] }
    memory := (initMachineState lm24Body []).memory }

theorem lm24_bb1_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 1) = .step lm24Bb1S1 := rfl
theorem lm24_bb1_anneal₂ : stepMirFn lm24Body lm24Bb1S1 = .step lm24Bb1S2 := rfl

private theorem lm24_decls_adt :
    ∀ l ∈ collectAdtLayoutsInDecls lm24Body.layouts "U" lm24Body.localDecls,
      lm24Body.layouts.entries[(lm24Decl lm24UTy).ty.layoutIdx]? = some l := by
  have hs : stringEq "U" "U" = true := by decide
  simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, hs, LayoutTable.lookup,
    lm24Body, lm24Layouts, lm24Decl, lm24UTy, lm24U8Ty, lm24U32Ty, get?, eq_comm]

/-- **Witness for `union_field_write_read_same_field_simulation`**: in `bb1`,
`_1 = U { a: 5 }` and `_2 = copy (_1.0: u8)` both step normally in Anneal and in
`lean-miri` (under `annealStepHooksLM2_4`), to related states, and `_2` ends up
holding `5_u8`. -/
theorem lm24_write_read_same_field_steps :
    ∃ m₁ m₂ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 1) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body lm24Bb1S1 m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body lm24Bb1S2 m₂ ∧
      get? lm24Bb1S2.frame.locals 2 = some (.init (.scalar ⟨5, 1⟩)) := by
  obtain ⟨hrel₁, hpost⟩ := union_field_write_read_same_field_simulation
    (lm24_init_stateRel 1).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24_phase (u := 1) (r := 2) (bb := _) rfl rfl rfl rfl
    rfl rfl lm24_wt_U rfl (by decide) rfl rfl rfl (lm24_init_frame_imm 1 1) (lm24_init_frame_imm 1 2)
    lm24_isPrim_u8 (fun tf _ => lm24_constU8_wt 5 (by decide) tf) (by decide)
    (hdecls_adt := lm24_decls_adt)
  obtain ⟨m₁, _, hstep₁, _, hrel₂, _⟩ := hpost lm24Bb1S1 lm24_bb1_anneal₁
  rw [lm24_bb1_anneal₁, hstep₁] at hrel₁
  rw [lm24_bb1_anneal₂] at hrel₂
  cases hrel₁ with
  | step _ _ hst₁ =>
    generalize hr : Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) () m₁ = r at hrel₂
    cases hrel₂ with
    | step _ m₂ hst₂ =>
      exact ⟨m₁, m₂, hstep₁, hst₁, hr, hst₂, rfl⟩

/-! ## 4. Whole-Union Copies -/

/-- The chain `_1 = U { a: 5 }; _4 = copy _1` at the start of a block `b` of
`lm24Body`, through `step_union_aggregate_simulation` and then
`union_whole_copy_initMask_preservation_simulation` applied to the facts that
the first step re-established. Afterwards `_4` is a memory-backed union holding
`5_u8` in its first byte, and `_2` and `_3` are still immediates. -/
theorem lm24_agg_copy_chain (b : Nat) {bb : BasicBlockData}
    (hbb : get? lm24Body.basicBlocks b = some bb)
    (h0 : get? bb.statements 0 = some (lm24AggStmt 1 5))
    (h1 : get? bb.statements 1 = some (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
    {S₁ S₂ : MachineState}
    (hs₁ : stepMirFn lm24Body (lm24InitAnneal b) = .step S₁)
    (hs₂ : stepMirFn lm24Body S₁ = .step S₂) :
    ∃ (m₁ m₂ : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri b) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body S₁ m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body S₂ m₂ ∧
      LiveAllocsNodup m₂.machine ∧
      get? S₂.frame.locals 4 = some (.init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit])) ∧
      S₂.frame.blockIdx = b ∧ S₂.frame.stmtIdx = 2 ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[4]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      UnionMemRel m₂.machine lm24UTy lm24Layouts 4 lm24U8Ty ⟨5, 1⟩ mp_w ∧
      IsImmediateFrameLocal tf₂ 2 ∧ IsImmediateFrameLocal tf₂ 3 := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24_init_stateRel b).toLM2_4
    lm24_nodup_empty
    lm24_canReserve_empty lm24_phase (u := 1) hbb h0 rfl lm24_wt_U rfl (by decide) rfl rfl rfl
    (lm24_init_frame_imm b 1) lm24_isPrim_u8 (fun tf _ => lm24_constU8_wt 5 (by decide) tf)
    (by decide) (hdecls_adt := lm24_decls_adt)
  obtain ⟨sc, mp, m₁, tf₁, hstep₁, hop₁, hst₁, hu_slot₁, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    himm₁, hpres₁, hblk₁, hidx₁, hhw₁⟩ := hpost₁ S₁ hs₁
  have hsc : sc = ⟨5, 1⟩ := by
    have h : evalOperand (lm24InitAnneal b).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24InitAnneal b).memory.globals lm24Body.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24InitAnneal b).frame.locals := rfl
    rw [h] at hop₁
    injection hop₁ with h1 _
    injection h1 with h1
    exact h1.symm
  subst hsc
  obtain ⟨hhw₁', _⟩ := hhw₁ rfl MemoryHighWater.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 64 by decide)
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact ⟨c₁, hmls₁⟩
  have himm₁' : ∀ j, j ≠ 1 → IsImmediateFrameLocal tf₁ j :=
    fun j hj => himm₁ (lm24InitMiriFrame b) rfl j hj (lm24_init_imm b j)
  have hw_imm₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 4 := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact himm₁' 4 (by decide)
  have hbb₁ : get? lm24Body.basicBlocks S₁.frame.blockIdx = some bb := by rw [hblk₁]; exact hbb
  have hstmt₁ : get? bb.statements S₁.frame.stmtIdx =
      some ⟨.assign ⟨4, .nil⟩ (.use (.copy ⟨1, .nil⟩)), "lm-1.1-witness"⟩ := by
    rw [hidx₁]; exact h1
  have hw_uninit₁ : get? S₁.frame.locals 4 = some .uninit := by
    rw [hpres₁ 4 (by decide)]; rfl
  obtain ⟨s₂, m₂, mp_w, tf₂, hs₂', hstep₂, hst₂, hw_slot₂, _, hframes₂, ⟨c₂, hmls₂⟩, _,
    _, hmemw₂, hnodup₂, himm₂, hblk₂, hidx₂, _⟩ :=
    union_whole_copy_initMask_preservation_simulation hst₁ hnodup₁ hhw₁'.canReserveAllocId
      lm24_phase hbb₁ hstmt₁ rfl rfl rfl lm24_wt_U rfl (by decide) hu_slot₁ hu_mls₁ hmem₁
      hw_uninit₁ hw_imm₁
  have hs₂'' := MirStepNode_step_inj (hs₂.symm.trans hs₂')
  subst hs₂''
  refine ⟨m₁, m₂, mp_w, tf₂, hstep₁, hst₁, hstep₂, hst₂, hnodup₂, hw_slot₂,
    hblk₂.trans hblk₁, by rw [hidx₂, hidx₁]; rfl, hframes₂, ⟨c₂, hmls₂⟩, hmemw₂,
    himm₂ tf₁ hframes₁ 2 (by decide) (himm₁' 2 (by decide)),
    himm₂ tf₁ hframes₁ 3 (by decide) (himm₁' 3 (by decide))⟩

/-- The Anneal state of `lm24Body` at statement `k` of block `b` with the given
locals. -/
def lm24AnnealState (b k : Nat) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := k, locals := locals }
    memory := (initMachineState lm24Body []).memory }

/-- The Anneal value of `U { a: 5 }`. -/
def lm24USlot : LocalSlot := .init (.aggregate 0 [.scalar ⟨5, 1⟩, .unit])

theorem lm24_bb0_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 0) =
    .step (lm24AnnealState 0 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl
theorem lm24_bb0_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 0 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 0 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) := rfl
theorem lm24_bb0_anneal₃ :
    stepMirFn lm24Body (lm24AnnealState 0 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) =
      .step (lm24AnnealState 0 3
        [.uninit, lm24USlot, .init (.scalar ⟨5, 1⟩), .uninit, lm24USlot]) := rfl
theorem lm24_bb2_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 2) =
    .step (lm24AnnealState 2 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl
theorem lm24_bb2_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 2 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 2 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) := rfl
theorem lm24_bb2_anneal₃ :
    stepMirFn lm24Body (lm24AnnealState 2 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) =
      .fail .ub := rfl

/-- **Witness for `union_whole_copy_initMask_preservation_simulation` (`I-11`)**
from block `0`: `_1 = U { a: 5 }`, `_4 = copy _1`, and `_2 = copy (_4.0: u8)`
step normally in both machines, to related states. After the copy, `_4`'s
allocation has the initialization mask `unionPrefixMask 4 1`: its byte `0` is
initialized, while the whole union `[0, 4)` is not, so the copy neither required
nor created initialized padding. The read of the copy's field `0` then returns
`5_u8`. -/
theorem lm24_copy_initMask_steps :
    ∃ (m₁ m₂ m₃ : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 0 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 0 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) m₂ ∧
      UnionMemRel m₂.machine lm24UTy lm24Layouts 4 lm24U8Ty ⟨5, 1⟩ mp_w ∧
      (∃ allocId tag localAlloc,
        mp_w.ptr.provenance = some (.concrete allocId tag) ∧
        (allocId, localAlloc) ∈ m₂.machine.memory.live.toList ∧
        IsUnionPrefixMask 4 1 localAlloc.allocation.initializationMask ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) = .ok (.ok ()) ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) ≠ .ok (.ok ()) ∧
        (∀ idx : Nat, idx < 4 →
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) =
            .ok (decide (idx < 1)))) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 0 3 [.uninit, lm24USlot, .init (.scalar ⟨5, 1⟩), .uninit, lm24USlot]) m₃ := by
  obtain ⟨m₁, m₂, mp_w, tf₂, hstep₁, hst₁, hstep₂, hst₂, hnodup₂, hw_slot₂, _, _, hframes₂,
    ⟨c₂, hmls₂⟩, hmemw₂, himm₂, _⟩ :=
    lm24_agg_copy_chain 0 rfl rfl rfl lm24_bb0_anneal₁ lm24_bb0_anneal₂
  obtain ⟨allocId, tag, la, hprov, hlive, hmask, hpre, hwhole, hget⟩ :=
    hmemw₂.initMask_spec lm24_wt_U.size_valid
  have hwhole' : la.allocation.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) ≠ .ok (.ok ()) :=
    fun h => absurd (hwhole.mp h) (by decide)
  have hu_mls₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[4]? = some ⟨.live (.indirect mp_w), c⟩ := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact ⟨c₂, hmls₂⟩
  have hr_imm₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 2 := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact himm₂
  have hread := step_union_field_read_simulation hst₂ hnodup₂ lm24_phase (r := 2) (u := 4)
    (bb := _) rfl rfl rfl rfl rfl lm24_isPrim_u8 (w := 1) (Or.inl rfl) rfl (f := 0) lm24_wt_U rfl
    (by decide) (by decide) hw_slot₂ hu_mls₂ hmemw₂ hr_imm₂
  obtain ⟨hrel₃, _, _⟩ := hread.1 rfl rfl
  rw [lm24_bb0_anneal₃] at hrel₃
  generalize hr : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) () m₂ = r at hrel₃
  cases hrel₃ with
  | step _ m₃ hst₃ =>
    exact ⟨m₁, m₂, m₃, mp_w, hstep₁, hst₁, hstep₂, hst₂, hmemw₂,
      ⟨allocId, tag, la, hprov, hlive, hmask, hpre, hwhole', hget⟩, hr, hst₃⟩

/-- **Witness for `union_uninit_bytes_read_ub_simulation`**: from block `2`,
after `_1 = U { a: 5 }` and `_4 = copy _1` step normally in both machines,
reading the larger field `_3 = copy (_4.1: u32)` is undefined behavior in both:
the copy's bytes `[1, 4)` are uninitialized. -/
theorem lm24_copy_larger_field_ub :
    ∃ (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 2) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 2 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 2 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) m₂ ∧
      stepMirFn lm24Body (lm24AnnealState 2 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₂ = (m₃, .error (.undefinedBehavior msg)) := by
  obtain ⟨m₁, m₂, mp_w, tf₂, hstep₁, hst₁, hstep₂, hst₂, hnodup₂, hw_slot₂, _, _, hframes₂,
    ⟨c₂, hmls₂⟩, hmemw₂, _, himm₃⟩ :=
    lm24_agg_copy_chain 2 rfl rfl rfl lm24_bb2_anneal₁ lm24_bb2_anneal₂
  have hu_mls₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[4]? = some ⟨.live (.indirect mp_w), c⟩ := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact ⟨c₂, hmls₂⟩
  have hr_imm₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 3 := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact himm₃
  obtain ⟨hub_a, m₃, msg, hub_m⟩ := union_uninit_bytes_read_ub_simulation hst₂ hnodup₂ lm24_phase
    (r := 3) (u := 4) (j := 1) (bb := _) rfl rfl rfl rfl rfl lm24_isPrim_u32 (w := 4)
    (Or.inr (Or.inr (Or.inl rfl))) rfl (f := 0) lm24_wt_U rfl (by decide) (by decide) hw_slot₂
    hu_mls₂ hmemw₂ hr_imm₂ (by decide) (by decide) (by decide)
  exact ⟨m₁, m₂, m₃, msg, hstep₁, hst₁, hstep₂, hst₂, hub_a, hub_m⟩

/-! ## 5. `Subslice` Projections -/

/-- **Witness for `evalProjection_subslice_simulation`** on the `[u16; 3]` array
`[0x0102, 0x0304, 0x0506]` of `WitLM2_1` (relative offset `4`): `a[1..3]` is
`[0x0304, 0x0506]` in Anneal and the place `2` bytes further in `lean-miri`;
`a[1..len - 1]` (`fromEnd`) is `[0x0304]`; and `a[2..len - 2]` is undefined
behavior in both machines. -/
theorem lm24_subslice_witness :
    let cx := annealSubsliceProjectionCx (lm21InitMiriFrame 0) emptyLayoutTable
      (witnessMachineOf lm21ArrAlloc)
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty emptyLayoutTable⟩
    readProjectedValue [] (.aggregate 0 lm21ArrElems) [.subslice 1 3 false] =
      .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩]) ∧
    (∃ op, annealProjectList cx base [.Subslice 1 3 false] = .ok op ∧
      ∃ mp, op.op = .indirect mp ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (witnessMemPlace.ptr.offset.bytes + 2)) ∧
    readProjectedValue [] (.aggregate 0 lm21ArrElems) [.subslice 1 1 true] =
      .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩]) ∧
    readProjectedValue [] (.aggregate 0 lm21ArrElems) [.subslice 2 2 true] = .ub ∧
    ∃ msg, (annealProjectList cx base [.Subslice 2 2 true]).mapError annealLiftProjectionError =
      .error (.undefinedBehavior msg) := by
  intro cx base
  have h := evalProjection_subslice_simulation (lm21InitMiriFrame 0) [] lm21_wf_u16Arr3
    lm21_nodup_arr lm21_memPlaceRel
  obtain ⟨hread₁, hproj₁, _⟩ := (h 1 3 false).1 (Or.inl ⟨rfl, by decide, by decide⟩)
  obtain ⟨hread₂, _, _⟩ := (h 1 1 true).1 (Or.inr ⟨rfl, by decide⟩)
  obtain ⟨hub, msg, hub_m⟩ := (h 2 2 true).2 rfl (by decide) (by decide)
  exact ⟨hread₁, ⟨_, hproj₁, _, rfl, rfl⟩, hread₂, hub, msg, hub_m⟩

/-! ## 6. Field Writes and Whole-Union Moves -/

/-- The step `_1 = U { a: 5 }` at the start of block `b`, through
`step_union_aggregate_simulation`, with the facts that later steps need. -/
theorem lm24_agg_step (b : Nat) {bb : BasicBlockData}
    (hbb : get? lm24Body.basicBlocks b = some bb)
    (h0 : get? bb.statements 0 = some (lm24AggStmt 1 5))
    {S₁ : MachineState} (hs₁ : stepMirFn lm24Body (lm24InitAnneal b) = .step S₁) :
    ∃ (m₁ : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri b) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body S₁ m₁ ∧
      LiveAllocsNodup m₁.machine ∧
      CanReserveAllocId m₁.machine.memory ∧
      m₁.stack.frames = #[tf₁] ∧
      (∃ c, tf₁.locals[1]? = some ⟨.live (.indirect mp), c⟩) ∧
      UnionMemRel m₁.machine lm24UTy lm24Layouts 4 lm24U8Ty ⟨5, 1⟩ mp ∧
      (∀ j, j ≠ 1 → IsImmediateFrameLocal tf₁ j) := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24_init_stateRel b).toLM2_4
    lm24_nodup_empty
    lm24_canReserve_empty lm24_phase (u := 1) hbb h0 rfl lm24_wt_U rfl (by decide) rfl rfl rfl
    (lm24_init_frame_imm b 1) lm24_isPrim_u8 (fun tf _ => lm24_constU8_wt 5 (by decide) tf)
    (by decide) (hdecls_adt := lm24_decls_adt)
  obtain ⟨sc, mp, m₁, tf₁, hstep₁, hop₁, hst₁, _, hframes₁, hmls₁, hmem₁, hnodup₁, himm₁, _,
    _, _, hhw₁⟩ := hpost₁ S₁ hs₁
  have hsc : sc = ⟨5, 1⟩ := by
    have h : evalOperand (lm24InitAnneal b).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24InitAnneal b).memory.globals lm24Body.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24InitAnneal b).frame.locals := rfl
    rw [h] at hop₁
    injection hop₁ with h1 _
    injection h1 with h1
    exact h1.symm
  subst hsc
  obtain ⟨hhw₁', _⟩ := hhw₁ rfl MemoryHighWater.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 64 by decide)
  exact ⟨m₁, mp, tf₁, hstep₁, hst₁, hnodup₁, hhw₁'.canReserveAllocId, hframes₁, hmls₁, hmem₁,
    fun j hj => himm₁ (lm24InitMiriFrame b) rfl j hj (lm24_init_imm b j)⟩

/-- The Anneal value of `U { a: 7 }`. -/
def lm24U7Slot : LocalSlot := .init (.aggregate 0 [.scalar ⟨7, 1⟩, .unit])

theorem lm24_bb3_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 3) =
    .step (lm24AnnealState 3 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl
theorem lm24_bb3_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 3 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 3 2 [.uninit, lm24U7Slot, .uninit, .uninit, .uninit]) := rfl
theorem lm24_bb3_anneal₃ :
    stepMirFn lm24Body (lm24AnnealState 3 2 [.uninit, lm24U7Slot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 3 3
        [.uninit, lm24U7Slot, .init (.scalar ⟨7, 1⟩), .uninit, .uninit]) := rfl
theorem lm24_bb4_anneal : stepMirFn lm24Body (lm24InitAnneal 4) =
    .step (lm24AnnealState 4 1 [.uninit, lm24U7Slot, .uninit, .uninit, .uninit]) := rfl
theorem lm24_bb5_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 5) =
    .step (lm24AnnealState 5 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl
theorem lm24_bb5_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 5 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 5 2 [.uninit, .uninit, .uninit, .uninit, lm24USlot]) := rfl
theorem lm24_bb5_anneal₃ :
    stepMirFn lm24Body (lm24AnnealState 5 2 [.uninit, .uninit, .uninit, .uninit, lm24USlot]) =
      .step (lm24AnnealState 5 3
        [.uninit, .uninit, .init (.scalar ⟨5, 1⟩), .uninit, lm24USlot]) := rfl

/-- **Witness for `step_union_field_write_simulation`**: from block `3`,
`_1 = U { a: 5 }`, `_1.0 = 7`, and `_2 = copy (_1.0: u8)` step normally in both
machines, to related states; the field write rewrites the union's allocation in
place, and the read returns `7_u8`. -/
theorem lm24_field_write_read_steps :
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 3) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 3 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 3 2 [.uninit, lm24U7Slot, .uninit, .uninit, .uninit]) m₂ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 3 3 [.uninit, lm24U7Slot, .init (.scalar ⟨7, 1⟩), .uninit, .uninit]) m₃ := by
  obtain ⟨m₁, mp, tf₁, hstep₁, hst₁, hnodup₁, _, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, himm₁⟩ :=
    lm24_agg_step 3 rfl rfl lm24_bb3_anneal₁
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact ⟨c₁, hmls₁⟩
  obtain ⟨_, hpost₂⟩ := step_union_field_write_simulation hst₁ hnodup₁ lm24_phase (u := 1)
    (bb := _) rfl rfl rfl lm24_wt_U rfl (by decide) rfl hu_mls₁ hmem₁
    (fun tf _ => lm24_constU8_wt 7 (by decide) tf)
  obtain ⟨sc', m₂, tf₂, hstep₂, hop₂, hst₂, hu_slot₂, _, hframes₂, ⟨c₂, hmls₂⟩, hmem₂, hnodup₂,
    himm₂, _, _, _⟩ := hpost₂ _ lm24_bb3_anneal₂
  have hsc' : sc' = ⟨7, 1⟩ := by
    have h : evalOperand
        (lm24AnnealState 3 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals
        (.constant (lm24ConstU8 7)) .nil
        (lm24AnnealState 3 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).memory.globals
        lm24Body.layouts .nil =
        .ok (.scalar ⟨7, 1⟩)
          (lm24AnnealState 3 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals := rfl
    rw [h] at hop₂
    injection hop₂ with h1 _
    injection h1 with h1
    exact h1.symm
  subst hsc'
  have hu_mls₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact ⟨c₂, hmls₂⟩
  have hr_imm₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 2 := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact himm₂ tf₁ hframes₁ 2 (himm₁ 2 (by decide))
  have hread := step_union_field_read_simulation hst₂ hnodup₂ lm24_phase (r := 2) (u := 1)
    (bb := _) rfl rfl rfl rfl rfl lm24_isPrim_u8 (w := 1) (Or.inl rfl) rfl lm24_wt_U rfl
    (by decide) (by decide) hu_slot₂ hu_mls₂ hmem₂ hr_imm₂
  obtain ⟨hrel₃, _, _⟩ := hread.1 rfl rfl
  rw [lm24_bb3_anneal₃] at hrel₃
  generalize hr : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) () m₂ = r at hrel₃
  cases hrel₃ with
  | step _ m₃ hst₃ => exact ⟨m₁, m₂, m₃, hstep₁, hst₁, hstep₂, hst₂, hr, hst₃⟩

/-- **Witness for `step_union_field_write_uninit_simulation`** (`D13b`): from
block `4`, `_1.0 = 7` on the uninitialized union `_1` steps both machines in
lockstep (`StateRelLM2_4`): Anneal materializes `lm24U7Slot` via
`uninitFieldWriteShell?` + `writeProjectedForLocal`, and `lean-miri` moves `_1`
to a fresh stack allocation and writes byte `0` (`UnionMemRel`, bytes `[1, 4)`
uninitialized). -/
theorem lm24_field_write_uninit_simulation :
    stepMirFn lm24Body (lm24InitAnneal 4) =
      .step (lm24AnnealState 4 1 [.uninit, lm24U7Slot, .uninit, .uninit, .uninit]) ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 4) = (m', .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 4 1 [.uninit, lm24U7Slot, .uninit, .uninit, .uninit]) m' ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[1]? = some ⟨.live (.indirect mp), c'⟩) ∧
      UnionMemRel m'.machine lm24UTy lm24Layouts 4 lm24U8Ty ⟨7, 1⟩ mp := by
  obtain ⟨_, hpost⟩ := step_union_field_write_uninit_simulation (lm24_init_stateRel 4).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24_phase (u := 1) (j := 0) (bb := _)
    rfl rfl rfl lm24_wt_U rfl (by decide) rfl (lm24_init_frame_imm 4 1) lm24_isPrim_u8
    (fun tf _ => lm24_constU8_wt 7 (by decide) tf) (by decide)
  obtain ⟨sc, mp, m', tf', hstep, hop, hst', _, _, hframes', hmls', hmem', _, _, _, _, _⟩ :=
    hpost _ lm24_bb4_anneal
  have hsc : sc = ⟨7, 1⟩ := by
    have h : evalOperand (lm24InitAnneal 4).frame.locals (.constant (lm24ConstU8 7)) .nil
        (lm24InitAnneal 4).memory.globals lm24Body.layouts .nil =
        .ok (.scalar ⟨7, 1⟩) (lm24InitAnneal 4).frame.locals := rfl
    rw [h] at hop; injection hop with h1 _; injection h1 with h1; exact h1.symm
  subst hsc
  exact ⟨lm24_bb4_anneal, m', tf', mp, hstep, hst', hframes', hmls', hmem'⟩

/-- **Witness for `union_whole_move_initMask_preservation_simulation`**: from
block `5`, `_1 = U { a: 5 }`, `_4 = move _1`, and `_2 = copy (_4.0: u8)` step
normally in both machines, to related states; the move deinitializes `_1` in
both, and the read of the moved-to union returns `5_u8`. -/
theorem lm24_move_read_steps :
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 5) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 5 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 5 2 [.uninit, .uninit, .uninit, .uninit, lm24USlot]) m₂ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 5 3 [.uninit, .uninit, .init (.scalar ⟨5, 1⟩), .uninit, lm24USlot]) m₃ := by
  obtain ⟨m₁, mp, tf₁, hstep₁, hst₁, hnodup₁, hcan₁, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, himm₁⟩ :=
    lm24_agg_step 5 rfl rfl lm24_bb5_anneal₁
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact ⟨c₁, hmls₁⟩
  have hw_imm₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 4 := by
    intro tf htf
    rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h
    exact himm₁ 4 (by decide)
  obtain ⟨s₂, m₂, mp_w, tf₂, hs₂, hstep₂, hst₂, hw_slot₂, _, _, hframes₂, ⟨c₂, hmls₂⟩, _,
    hmemw₂, hnodup₂, _, himm₂, _, _, _⟩ :=
    union_whole_move_initMask_preservation_simulation hst₁ hnodup₁ hcan₁ lm24_phase (w := 4)
      (u := 1) (bb := _) rfl rfl rfl rfl rfl (f := 0) lm24_wt_U rfl (by decide) rfl hu_mls₁ hmem₁
      rfl hw_imm₁
  have hs₂' := MirStepNode_step_inj (lm24_bb5_anneal₂.symm.trans hs₂)
  subst hs₂'
  have hu_mls₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[4]? = some ⟨.live (.indirect mp_w), c⟩ := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact ⟨c₂, hmls₂⟩
  have hr_imm₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 2 := by
    intro tf htf
    rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h
    exact himm₂ tf₁ hframes₁ 2 (by decide) (himm₁ 2 (by decide))
  have hread := step_union_field_read_simulation hst₂ hnodup₂ lm24_phase (r := 2) (u := 4)
    (bb := _) rfl rfl rfl rfl rfl lm24_isPrim_u8 (w := 1) (Or.inl rfl) rfl (f := 0) lm24_wt_U rfl
    (by decide) (by decide) hw_slot₂ hu_mls₂ hmemw₂ hr_imm₂
  obtain ⟨hrel₃, _, _⟩ := hread.1 rfl rfl
  rw [lm24_bb5_anneal₃] at hrel₃
  generalize hr : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) () m₂ = r at hrel₃
  cases hrel₃ with
  | step _ m₃ hst₃ => exact ⟨m₁, m₂, m₃, hstep₁, hst₁, hstep₂, hst₂, hr, hst₃⟩

/-! ## 7. `Subslice` Operands -/

/-- **Witness for `evalSubsliceOperand_simulation`** on the `[u16; 3]` local
`_1` of `WitLM2_1`. With `_1 = [0x0102, 0x0304, 0x0506]` memory-backed at
`witnessMemPlace`, the operand `copy _1[1..3]` is `[0x0304, 0x0506]` in Anneal
and, in `lean-miri`, the place `2` bytes further into `_1`'s allocation, the
states staying related; `move _1[2..len - 2]` is undefined behavior in both
machines. With `_1` uninitialized, `copy _1[1..3]` is undefined behavior in
both. -/
theorem lm24_subslice_operand_witness :
    evalOperand (lm21ArrAnneal 0 .uninit).frame.locals (.copy ⟨1, [.subslice 1 3 false]⟩) .nil
        (lm21ArrAnneal 0 .uninit).memory.globals lm21Body.layouts .nil =
      .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩])
        (lm21ArrAnneal 0 .uninit).frame.locals ∧
    (∃ (op : Miri.Interpreter.OpTy AnnealProv) (m' : AnnealStepState)
        (mp : Miri.Interpreter.MemPlace AnnealProv),
      annealEvalOperandLM2_4 lm21Body.localDecls lm21Body.layouts
          (.Copy ⟨1, #[.Subslice 1 3 false]⟩) none (lm21ArrMiri 0 .uninit) = .ok op m' ∧
      StateRelLM2_4 lm21Body (lm21ArrAnneal 0 .uninit) m' ∧
      op.op = .indirect mp ∧
      mp.ptr.offset = Miri.ABI.Size.ofBytes (witnessMemPlace.ptr.offset.bytes + 2)) ∧
    evalOperand (lm21ArrAnneal 0 .uninit).frame.locals (.move ⟨1, [.subslice 2 2 true]⟩) .nil
        (lm21ArrAnneal 0 .uninit).memory.globals lm21Body.layouts .nil = .ub ∧
    (∃ (m' : AnnealStepState) (msg : String),
      annealEvalOperandLM2_4 lm21Body.localDecls lm21Body.layouts
          (.Move ⟨1, #[.Subslice 2 2 true]⟩) none (lm21ArrMiri 0 .uninit) =
        .error (.undefinedBehavior msg) m') ∧
    evalOperand (lm21InitAnneal 0).frame.locals (.copy ⟨1, [.subslice 1 3 false]⟩) .nil
        (lm21InitAnneal 0).memory.globals lm21Body.layouts .nil = .ub ∧
    (∃ (m' : AnnealStepState) (msg : String),
      annealEvalOperandLM2_4 lm21Body.localDecls lm21Body.layouts
          (.Copy ⟨1, #[.Subslice 1 3 false]⟩) none (lm21InitMiri 0) =
        .error (.undefinedBehavior msg) m') := by
  have hst := (lm21_arr_stateRel 0 .uninit .uninit (Or.inl ⟨rfl, rfl⟩)).toLM2_4
  obtain ⟨mp, _, _, ⟨c, hc⟩, _, _, _, hst', hin, _⟩ :=
    (evalSubsliceOperand_simulation hst rfl lm21_nodup_arr (arrIdx := 1) rfl lm21_wf_u16Arr3
      false 1 3 false none).2 lm21ArrElems rfl
  obtain ⟨hev₁, hmv₁, _⟩ := hin (Or.inl ⟨rfl, by decide, by decide⟩)
  obtain ⟨_, _, _, _, _, _, _, _, _, hoob⟩ :=
    (evalSubsliceOperand_simulation hst rfl lm21_nodup_arr (arrIdx := 1) rfl lm21_wf_u16Arr3
      true 2 2 true none).2 lm21ArrElems rfl
  obtain ⟨hev₂, msg₂, hmv₂⟩ := hoob rfl (by decide) (by decide)
  obtain ⟨hev₃, m₃, msg₃, hmv₃⟩ :=
    (evalSubsliceOperand_simulation (lm21_init_stateRel 0).toLM2_4 rfl lm21_nodup_empty
      (arrIdx := 1) rfl lm21_wf_u16Arr3 false 1 3 false none).1 (Or.inr ⟨rfl, Or.inl (by decide)⟩)
  have hmp : mp = witnessMemPlace := by
    have h : (lm21ArrMiriFrame 0 .uninit).locals[1]? =
        some ⟨.live (.indirect witnessMemPlace), none⟩ := rfl
    rw [h] at hc
    cases hc
    rfl
  subst hmp
  exact ⟨hev₁, ⟨_, _, _, hmv₁, hst', rfl, rfl⟩, hev₂, ⟨_, msg₂, hmv₂⟩, hev₃, ⟨m₃, msg₃, hmv₃⟩⟩

/-! ## 8. Union Active-Field Overlay (`D13a`), Type-Punning Read, and Nonzero-Field Write Simulations -/

theorem lm24_constU32_wt (n : Nat) (hn : n < 2 ^ 32)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand lm24Body tf (.constant (lm24ConstU32 n)) lm24U32Ty :=
  .constScalar (lm24ConstU32 n) ⟨n, 4⟩ rfl lm24_isPrim_u32
    (Or.inr (Or.inr (Or.inl rfl))) hn rfl (fun h => nomatch h) (fun h => nomatch h)

def lm24UU32Slot : LocalSlot := .init (.aggregate 0 [.unit, .scalar ⟨0x01020304, 4⟩])

/-- **Witness for `evalRvalue_union_aggregate_activeField_simulation`** (`D13a`):
evaluating `U { b: 0x01020304_u32 }` (`activeField = some 1`) on `lm24Body`
places the scalar at slot `1` (`unionSlotFields 2 1 = [.unit, .scalar ⟨0x01020304, 4⟩]`)
rather than ignoring `activeField`. -/
theorem lm24_rvalue_union_aggregate_activeField_witness :
    evalRvalue (lm24InitAnneal 6).frame.locals
        (.aggregate (.adt "U" 0 (some 1)) [.constant (lm24ConstU32 0x01020304)])
        (lm24InitAnneal 6).memory lm24Body.localDecls lm24Body.layouts =
      .ok (.aggregate 0 [.unit, .scalar ⟨0x01020304, 4⟩])
        (lm24InitAnneal 6).frame.locals (lm24InitAnneal 6).memory := by
  have himm : ImmediateRel lm24U32Ty lm24Layouts (.scalar ⟨0x01020304, 4⟩)
      (.scalar (.fromScalarInt (extractExceptOk (translateScalarInt ⟨0x01020304, 4⟩) (by decide)))) :=
    .scalar ⟨0x01020304, 4⟩ (extractExceptOk (translateScalarInt ⟨0x01020304, 4⟩) (by decide))
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, by decide, by decide⟩
      rfl (fun h => nomatch h) (fun h => nomatch h)
  exact (evalRvalue_union_aggregate_activeField_simulation (body := lm24Body)
    (u := 1) (n := 2) (f := 1) rfl rfl rfl ⟨[], rfl⟩
    lm24_wt_U rfl (by decide) rfl lm24_isPrim_u32 rfl
    (lm24_constU32_wt 0x01020304 (by decide) (lm24InitMiriFrame 6)) rfl himm
    (hdecls_adt := lm24_decls_adt)).1

theorem lm24_bb6_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 6) =
    .step (lm24AnnealState 6 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) := rfl

theorem lm24_bb6_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 6 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 6 2
        [.uninit, lm24UU32Slot, .init (.scalar ⟨0x04, 1⟩), .uninit, .uninit]) := rfl

/-- **Witness for `step_union_type_punning_read_simulation`**: from block `6`,
`_1 = U { b: 0x01020304_u32 }` (`activeField = some 1`) and the subsequent
type-punning read `_2 = copy (_1.0: u8)` both step normally in lockstep
(`StateRelLM2_4`), reading the little-endian low byte `0x04_u8` (`msc_w.data = 0x04`,
`msc_w.size = 1`). -/
theorem lm24_type_punning_read_simulation :
    ∃ (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (msc_w : Miri.Memory.ScalarInt),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 6) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 6 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn lm24Body
        (lm24AnnealState 6 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) =
          .step (lm24AnnealState 6 2
            [.uninit, lm24UU32Slot, .init (.scalar ⟨0x04, 1⟩), .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 6 2
          [.uninit, lm24UU32Slot, .init (.scalar ⟨0x04, 1⟩), .uninit, .uninit]) m₂ ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc_w))), c⟩) ∧
      msc_w.data = 0x04 ∧
      msc_w.size = Miri.ABI.Size.ofBytes 1 := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24_init_stateRel 6).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24_init_frame_imm 6 1) lm24_isPrim_u32
    (fun tf _ => lm24_constU32_wt 0x01020304 (by decide) tf) (by decide)
    (hdecls_adt := lm24_decls_adt)
  obtain ⟨sc, mp, m₁, tf₁, hstep₁, hop₁, hst₁, hu_slot₁, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    himm₁, _, _, _, _⟩ := hpost₁ _ lm24_bb6_anneal₁
  have hsc : sc = ⟨0x01020304, 4⟩ := by
    have h : evalOperand (lm24InitAnneal 6).frame.locals (.constant (lm24ConstU32 0x01020304)) .nil
        (lm24InitAnneal 6).memory.globals lm24Body.layouts .nil =
        .ok (.scalar ⟨0x01020304, 4⟩) (lm24InitAnneal 6).frame.locals := rfl
    rw [h] at hop₁
    injection hop₁ with h1 _
    injection h1 with h1
    exact h1.symm
  subst hsc
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have hr_imm₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 2 := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact himm₁ (lm24InitMiriFrame 6) rfl 2 (by decide) (lm24_init_imm 6 2)
  obtain ⟨_, _, hlive₂⟩ :=
    step_union_type_punning_read_simulation hst₁ hnodup₁ lm24_phase (r := 2) (u := 1) (j := 0)
      (bb := _) rfl rfl rfl rfl rfl lm24_isPrim_u8 (w := 1) (Or.inl rfl) rfl (f := 1) lm24_wt_U rfl
      (by decide) (by decide) hu_slot₁ hu_mls₁ hmem₁ hr_imm₁ (by decide) (by decide)
  obtain ⟨s₂, m₂, tf₂, msc_w, hs₂, hstep₂, hst₂, _, _, hframes₂, ⟨_, _, hsize, hdata⟩, hloc₂⟩ :=
    hlive₂ (fun h => nomatch h)
  have hs₂_eq := MirStepNode_step_inj (lm24_bb6_anneal₂.symm.trans hs₂)
  subst hs₂_eq
  have hmod : 0x01020304 % scalarModulus 1 = 0x04 := by
    rw [scalarModulus_eq_two_pow]
  dsimp only at hdata
  exact ⟨m₁, m₂, tf₂, msc_w, hstep₁, hst₁, lm24_bb6_anneal₂, hstep₂, hst₂, hframes₂, hloc₂,
    by rw [hdata, hmod]; rfl, hsize⟩

theorem lm24_bb7_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 7) =
    .step (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl

theorem lm24_bb7_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 7 2 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) := rfl

/-- **Witness for `step_union_nonzero_field_write_simulation`**: from block `7`,
`_1 = U { a: 5 }` and the subsequent nonzero-field write `_1.1 = 0x01020304_u32`
both step normally in lockstep (`StateRelLM2_4`), updating `_1` to `lm24UU32Slot`
(`[.unit, .scalar ⟨0x01020304, 4⟩]`) in Anneal and overwriting bytes `[0, 4)` at
offset `0` with `UnionMemRel` for `(lm24U32Ty, ⟨0x01020304, 4⟩)` in `lean-miri`. -/
theorem lm24_nonzero_field_write_simulation :
    ∃ (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 7) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn lm24Body
        (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
          .step (lm24AnnealState 7 2 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 7 2 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) m₂ ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[1]? = some ⟨.live (.indirect mp), c⟩) ∧
      UnionMemRel m₂.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x01020304, 4⟩ mp := by
  obtain ⟨m₁, mp, tf₁, hstep₁, hst₁, hnodup₁, _, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, _⟩ :=
    lm24_agg_step 7 rfl rfl lm24_bb7_anneal₁
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  obtain ⟨_, hpost₂⟩ :=
    step_union_nonzero_field_write_simulation hst₁ hnodup₁ lm24_phase (u := 1) (j := 1)
      (bb := _) rfl rfl rfl (f := 0) lm24_wt_U rfl (by decide) (by decide) rfl hu_mls₁ hmem₁
      lm24_isPrim_u32 (fun tf _ => lm24_constU32_wt 0x01020304 (by decide) tf)
      (by decide) (by decide)
  obtain ⟨sc', m₂, tf₂, hstep₂, hop₂, hst₂, _, _, hframes₂, hloc₂, hmem₂, _, _, _, _, _⟩ :=
    hpost₂ _ lm24_bb7_anneal₂
  have hsc' : sc' = ⟨0x01020304, 4⟩ := by
    have h : evalOperand
        (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals
        (.constant (lm24ConstU32 0x01020304)) .nil
        (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).memory.globals
        lm24Body.layouts .nil =
        .ok (.scalar ⟨0x01020304, 4⟩)
          (lm24AnnealState 7 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals := rfl
    rw [h] at hop₂; injection hop₂ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc'
  exact ⟨m₁, m₂, tf₂, mp, hstep₁, hst₁, lm24_bb7_anneal₂, hstep₂, hst₂, hframes₂, hloc₂, hmem₂⟩


theorem lm24_bb8_anneal : stepMirFn lm24Body (lm24InitAnneal 8) =
    .step (lm24AnnealState 8 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) := rfl

/-- **Witness for `step_union_field_write_uninit_simulation` at a nonzero field**
(`D13b`, `j = 1`): from block `8`, `_1.1 = 0x01020304_u32` on the uninitialized
union `_1` steps both machines in lockstep (`StateRelLM2_4`): Anneal materializes
`lm24UU32Slot` (`unionSlotFields 2 1 (.scalar ⟨0x01020304, 4⟩)`) via
`uninitFieldWriteShell?` + `writeProjectedForLocal`, and `lean-miri` moves `_1` to
a fresh stack allocation and writes bytes `[0, 4)` (`UnionMemRel` for
`(lm24U32Ty, ⟨0x01020304, 4⟩)`). Together with `lm24_field_write_uninit_simulation`
(`j = 0`), this exercises the general-`j` statement on both union fields. -/
theorem lm24_field1_write_uninit_simulation :
    stepMirFn lm24Body (lm24InitAnneal 8) =
      .step (lm24AnnealState 8 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) ()
          (lm24InitMiri 8) = (m', .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 8 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) m' ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[1]? = some ⟨.live (.indirect mp), c'⟩) ∧
      UnionMemRel m'.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x01020304, 4⟩ mp := by
  obtain ⟨_, hpost⟩ := step_union_field_write_uninit_simulation (lm24_init_stateRel 8).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24_phase (u := 1) (j := 1) (bb := _)
    rfl rfl rfl lm24_wt_U rfl (by decide) rfl (lm24_init_frame_imm 8 1) lm24_isPrim_u32
    (fun tf _ => lm24_constU32_wt 0x01020304 (by decide) tf) (by decide)
  obtain ⟨sc, mp, m', tf', hstep, hop, hst', _, _, hframes', hmls', hmem', _, _, _, _, _⟩ :=
    hpost _ lm24_bb8_anneal
  have hsc : sc = ⟨0x01020304, 4⟩ := by
    have h : evalOperand (lm24InitAnneal 8).frame.locals (.constant (lm24ConstU32 0x01020304)) .nil
        (lm24InitAnneal 8).memory.globals lm24Body.layouts .nil =
        .ok (.scalar ⟨0x01020304, 4⟩) (lm24InitAnneal 8).frame.locals := rfl
    rw [h] at hop; injection hop with h1 _; injection h1 with h1; exact h1.symm
  subst hsc
  exact ⟨lm24_bb8_anneal, m', tf', mp, hstep, hst', hframes', hmls', hmem'⟩

/-- Anneal `LocalSlot` for `_1 : U` after `_1 = U { b: 0x01020304_u32 }` followed
by narrower projected write `_1.0 = 0x77_u8`: typed slot `0` holds `0x77_u8` and
the `D13a` raw-byte overlay retains high bytes `[0x03, 0x02, 0x01]`. -/
def lm24USplicedSlot : LocalSlot :=
  .init (.aggregate 0
    (unionSlotFields 2 0 (.scalar ⟨0x77, 1⟩) ++
      [.aggregate 0
        (encodeRawAbstractByteVals
          (encodeLittleEndianBytes 0x77 1 none ++
            ((encodeLittleEndianBytes 0x01020304 4 none).drop 1 ++
              replicateUninitBytes 0)))]))

/-- Anneal `LocalSlot` for `_1 : U` after the second chained narrower projected
write `_1.0 = 0x88_u8` onto `lm24USplicedSlot`: typed slot `0` holds `0x88_u8`
and the `D13a` raw-byte overlay still retains high bytes `[0x03, 0x02, 0x01]`. -/
def lm24USplicedSlot2 : LocalSlot :=
  .init (.aggregate 0
    (unionSlotFields 2 0 (.scalar ⟨0x88, 1⟩) ++
      [.aggregate 0
        (encodeRawAbstractByteVals
          (encodeLittleEndianBytes 0x88 1 none ++
            ((encodeLittleEndianBytes 0x01020377 4 none).drop 1 ++
              replicateUninitBytes 0)))]))

theorem lm24_bb9_anneal₁ : stepMirFn lm24Body (lm24InitAnneal 9) =
    .step (lm24AnnealState 9 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) := rfl

theorem lm24_bb9_anneal₂ :
    stepMirFn lm24Body (lm24AnnealState 9 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 9 2 [.uninit, lm24USplicedSlot, .uninit, .uninit, .uninit]) := rfl

theorem lm24_bb9_anneal₃ :
    stepMirFn lm24Body
      (lm24AnnealState 9 2 [.uninit, lm24USplicedSlot, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 9 3 [.uninit, lm24USplicedSlot2, .uninit, .uninit, .uninit]) := rfl

theorem lm24_bb9_anneal₄ :
    stepMirFn lm24Body
      (lm24AnnealState 9 3 [.uninit, lm24USplicedSlot2, .uninit, .uninit, .uninit]) =
      .step (lm24AnnealState 9 4
        [.uninit, lm24USplicedSlot2, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) := rfl

theorem lm24_bb9_anneal₅ :
    stepMirFn lm24Body
      (lm24AnnealState 9 4
        [.uninit, lm24USplicedSlot2, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) =
      .step (lm24AnnealState 9 5
        [.uninit, .dead, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) := rfl

/-- **End-to-end 5-step `StateRelLM2_4` witness for
`step_union_narrower_field_write_simulation`, `step_union_overlay_field_read_simulation`,
and `step_storageDead_LM2_4_simulation` on `UnionLocalRel.unionOverlay`**
(contrasting projected `_1.0 = 0x77_u8; _1.0 = 0x88_u8` with unprojected
`lm24_union_agg_smaller_overwrite_divergence`):
1. `_1 = U { b: 0x01020304_u32 }` initializes all 4 bytes `[0x04, 0x03, 0x02, 0x01]`
   in lockstep (`StateRelLM2_4`);
2. Narrower projected write `_1.0 = 0x77_u8` attaches the raw-byte overlay
   `lm24USplicedSlot` in Anneal while overwriting byte `0` and retaining
   `[0x03, 0x02, 0x01]` in `lean-miri`, re-establishing `StateRelLM2_4` via
   `UnionLocalRel.unionOverlay` (`UnionMemRel` for `⟨0x01020377, 4⟩`);
3. Chained narrower projected write `_1.0 = 0x88_u8` onto the overlay-carrying
   union updates `_1` to `lm24USplicedSlot2` while preserving `StateRelLM2_4`
   (`UnionMemRel` for `⟨0x01020388, 4⟩`);
4. Wide cross-field read `_3 = copy (_1.1: u32)` steps both machines in
   `StateRelLM2_4` lockstep and decodes `0x01020388_u32` into `_3`
   (`step_union_overlay_field_read_simulation`);
5. `StorageDead(_1)` composes directly on the overlay-carrying `StateRelLM2_4`
   state, marking `_1` dead and freeing its stack allocation in `StateRelLM2_4`
   (`step_storageDead_LM2_4_simulation`). -/
theorem lm24_narrower_field_write_retains_high_bytes_simulation :
    ∃ (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (msc₄ : Miri.Memory.ScalarInt),
      let hooks := annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts
      stepMirFn lm24Body (lm24InitAnneal 9) =
        .step (lm24AnnealState 9 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step hooks () (lm24InitMiri 9) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 9 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn lm24Body
        (lm24AnnealState 9 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) =
          .step (lm24AnnealState 9 2 [.uninit, lm24USplicedSlot, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 9 2 [.uninit, lm24USplicedSlot, .uninit, .uninit, .uninit]) m₂ ∧
      UnionMemRel m₂.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x01020377, 4⟩ mp ∧
      stepMirFn lm24Body
        (lm24AnnealState 9 2 [.uninit, lm24USplicedSlot, .uninit, .uninit, .uninit]) =
          .step (lm24AnnealState 9 3 [.uninit, lm24USplicedSlot2, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 9 3 [.uninit, lm24USplicedSlot2, .uninit, .uninit, .uninit]) m₃ ∧
      UnionMemRel m₃.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x01020388, 4⟩ mp ∧
      stepMirFn lm24Body
        (lm24AnnealState 9 3 [.uninit, lm24USplicedSlot2, .uninit, .uninit, .uninit]) =
          .step (lm24AnnealState 9 4
            [.uninit, lm24USplicedSlot2, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 9 4
          [.uninit, lm24USplicedSlot2, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) m₄ ∧
      ScalarRel ⟨0x01020388, 4⟩ msc₄ ∧
      m₄.stack.frames = #[tf₄] ∧
      (∃ c, tf₄.locals[3]? =
        some ⟨.live (.immediate (.scalar (.fromScalarInt msc₄))), c⟩) ∧
      stepMirFn lm24Body
        (lm24AnnealState 9 4
          [.uninit, lm24USplicedSlot2, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) =
          .step (lm24AnnealState 9 5
            [.uninit, .dead, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_4 lm24Body
        (lm24AnnealState 9 5
          [.uninit, .dead, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit]) m₅ := by
  -- Step 1: `_1 = U { b: 0x01020304_u32 }`
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24_init_stateRel 9).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24_init_frame_imm 9 1) lm24_isPrim_u32
    (fun tf _ => lm24_constU32_wt 0x01020304 (by decide) tf) (by decide)
    (hdecls_adt := lm24_decls_adt)
  obtain ⟨sc₁, mp, m₁, tf₁, hstep₁, hop₁, hst₁, hu_slot₁, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    himm₁, _, _, _, _⟩ := hpost₁ _ lm24_bb9_anneal₁
  have hsc₁ : sc₁ = ⟨0x01020304, 4⟩ := by
    have h : evalOperand (lm24InitAnneal 9).frame.locals (.constant (lm24ConstU32 0x01020304)) .nil
        (lm24InitAnneal 9).memory.globals lm24Body.layouts .nil =
        .ok (.scalar ⟨0x01020304, 4⟩) (lm24InitAnneal 9).frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  have hu_mls₁ : ∀ topFrame, m₁.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have hmsc₀ : ∃ msc0 : Miri.Memory.ScalarInt,
      ImmediateRel lm24U32Ty lm24Body.layouts (.scalar ⟨0x01020304, 4⟩)
        (.scalar (.fromScalarInt msc0)) := by
    cases hmem₁ with
    | mk _ _ _ _ msc0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi0 _ => exact ⟨msc0, hi0⟩
  have hu_init₁ : UnionInitSlotRel lm24Body.layouts lm24UTy 4 2 ⟨0x01020304, 4⟩ lm24UU32Slot :=
    .plain 1 lm24U32Ty (by decide) lm24_isPrim_u32 hmsc₀ ⟨_, rfl, rfl⟩
  -- Step 2: `_1.0 = 0x77_u8` (narrower projected write -> `UnionLocalRel.unionOverlay`)
  obtain ⟨_, hpost₂⟩ := step_union_narrower_field_write_simulation hst₁ hnodup₁ lm24_phase
    (u := 1) (j := 0) (bb := _) rfl rfl rfl lm24_wt_U rfl (by decide) hu_slot₁ hu_init₁
    hu_mls₁ hmem₁ (by intro h; cases h) (by intro h; cases h) lm24_isPrim_u8
    (fun tf _ => lm24_constU8_wt 0x77 (by decide) tf) (by decide)
  obtain ⟨_, _, hu_init₂_raw, m₂, _, tf₂, _, _, _, hstep₂, hst₂, _, hframes₂, hu_mls₂_eq,
    himm₂, _, _, hnodup₂, _, _, _, hmem₂_raw, _⟩ := hpost₂ ⟨0x77, 1⟩ rfl
  change StateRelLM2_4 lm24Body
    (lm24AnnealState 9 2 [.uninit, lm24USplicedSlot, .uninit, .uninit, .uninit]) m₂ at hst₂
  have hsp₁ : unionSpliceLowScalar ⟨0x01020304, 4⟩ ⟨0x77, 1⟩ = ⟨0x01020377, 4⟩ := by
    unfold unionSpliceLowScalar; rw [scalarModulus_eq_two_pow]; rfl
  have hmem₂ : UnionMemRel m₂.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x01020377, 4⟩ mp :=
    hsp₁ ▸ hmem₂_raw
  have hu_init₂ : UnionInitSlotRel lm24Body.layouts lm24UTy 4 2 ⟨0x01020377, 4⟩ lm24USplicedSlot :=
    hsp₁ ▸ hu_init₂_raw
  have hu_mls₂ : ∀ topFrame, m₂.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h; exact ⟨_, hu_mls₂_eq⟩
  -- Step 3: `_1.0 = 0x88_u8` (chained narrower projected write on `UnionLocalRel.unionOverlay`)
  obtain ⟨_, hpost₃⟩ := step_union_narrower_field_write_simulation hst₂ hnodup₂ lm24_phase
    (u := 1) (j := 0) (bb := _) rfl rfl rfl lm24_wt_U rfl (by decide) rfl hu_init₂
    hu_mls₂ hmem₂ (by intro h; cases h) (by intro h; cases h) lm24_isPrim_u8
    (fun tf _ => lm24_constU8_wt 0x88 (by decide) tf) (by decide)
  obtain ⟨_, hov₃_raw, _, m₃, _, tf₃, _, _, _, hstep₃, hst₃, _, hframes₃, hu_mls₃_eq,
    himm₃, _, _, hnodup₃, _, _, _, hmem₃_raw, _⟩ := hpost₃ ⟨0x88, 1⟩ rfl
  change StateRelLM2_4 lm24Body
    (lm24AnnealState 9 3 [.uninit, lm24USplicedSlot2, .uninit, .uninit, .uninit]) m₃ at hst₃
  have hsp₂ : unionSpliceLowScalar ⟨0x01020377, 4⟩ ⟨0x88, 1⟩ = ⟨0x01020388, 4⟩ := by
    unfold unionSpliceLowScalar; rw [scalarModulus_eq_two_pow]; rfl
  have hmem₃ : UnionMemRel m₃.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x01020388, 4⟩ mp :=
    hsp₂ ▸ hmem₃_raw
  have hov₃ : UnionOverlaySlotSpec lm24Body.layouts lm24UTy 4 2 0 ⟨0x01020388, 4⟩ ⟨0x88, 1⟩
      (encodeLittleEndianBytes 0x88 1 none ++
        ((encodeLittleEndianBytes 0x01020377 4 none).drop 1 ++ replicateUninitBytes 0)) :=
    hsp₂ ▸ hov₃_raw
  have hu_mls₃ : ∀ topFrame, m₃.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[1]? = some ⟨.live (.indirect mp), c⟩ := by
    intro tf htf; rw [hframes₃] at htf
    have h : tf₃ = tf := by simpa using htf
    subst h; exact ⟨_, hu_mls₃_eq⟩
  -- Step 4: `_3 = copy (_1.1: u32)` reads `0x01020388_u32` in `StateRelLM2_4` lockstep
  have hr_imm₃ : ∀ topFrame, m₃.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 3 := by
    intro tf htf; rw [hframes₃] at htf
    have h : tf₃ = tf := by simpa using htf
    subst h
    exact himm₃ tf₂ hframes₂ 3
      (himm₂ tf₁ hframes₁ 3 (himm₁ (lm24InitMiriFrame 9) rfl 3 (by decide) (lm24_init_imm 9 3)))
  obtain ⟨_, _, hpost₄⟩ := step_union_overlay_field_read_simulation hst₃ hnodup₃ lm24_phase
    (bb := _) (r := 3) (u := 1) (j := 1) (fty := lm24U32Ty) (isMove := false)
    rfl rfl rfl rfl rfl lm24_isPrim_u32 (Or.inr (Or.inr (Or.inl rfl))) rfl lm24_wt_U rfl
    (by decide) hov₃ rfl hu_mls₃ hmem₃ hr_imm₃ (by decide) (by decide)
    (fun h => nomatch h) (fun h => nomatch h)
  obtain ⟨s₄, m₄, tf₄, msc₄, hs₄, hstep₄, hst₄, _, hmach₄, hframes₄, hrel₄, hc₄⟩ :=
    hpost₄ (fun h => nomatch h)
  have hs₄_eq : s₄ = lm24AnnealState 9 4
      [.uninit, lm24USplicedSlot2, .uninit, .init (.scalar ⟨0x01020388, 4⟩), .uninit] := by
    rw [lm24_bb9_anneal₄] at hs₄; exact MirStepNode_step_inj hs₄.symm
  subst hs₄_eq
  have hmod₄ : (0x01020388 : Nat) % scalarModulus 4 = 0x01020388 := by
    rw [scalarModulus_eq_two_pow]
  dsimp only at hrel₄
  rw [hmod₄] at hrel₄
  -- Step 5: `StorageDead(_1)` frees `_1`'s stack allocation in `StateRelLM2_4`
  have hnodup₄ : LiveAllocsNodup m₄.machine := hmach₄ ▸ hnodup₃
  obtain ⟨hrel₅, _, _⟩ := step_storageDead_LM2_4_simulation hst₄ hnodup₄ lm24_phase
    (bb := _) (loc := 1) rfl rfl rfl (by decide)
  rw [lm24_bb9_anneal₅] at hrel₅
  generalize hm₅_eq :
    Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24Body.localDecls lm24Body.layouts) () m₄ =
      res₅ at hrel₅
  cases hrel₅ with
  | step _ m₅ hst₅ =>
    exact ⟨m₁, m₂, m₃, m₄, m₅, tf₄, mp, msc₄,
      lm24_bb9_anneal₁, hstep₁, hst₁,
      lm24_bb9_anneal₂, hstep₂, hst₂, hmem₂,
      lm24_bb9_anneal₃, hstep₃, hst₃, hmem₃,
      lm24_bb9_anneal₄, hstep₄, hst₄, hrel₄, hframes₄, hc₄,
      lm24_bb9_anneal₅, hm₅_eq, hst₅⟩

/-! ## 9. Statement-Level `Subslice` Assignments & `[T; 0]` Dichotomy -/

def lm24U16Arr2Ty : Ty := { kind := .array (.uint .u16) 2, layoutIdx := 0 }
def lm24U16Arr2Decl : LocalDecl := { mutability := .mut, ty := lm24U16Arr2Ty, debugName := none }

private theorem lm24_elemLayout_u16Arr2 :
    arrayElemLayoutOf emptyLayoutTable
      (translateTy lm24U16Arr2Ty emptyLayoutTable)
      (translateTy lm21U16Ty emptyLayoutTable).layout.size =
    translateTy lm21U16Ty emptyLayoutTable := by
  have hty : (translateTy lm24U16Arr2Ty emptyLayoutTable).ty = 1021 := rfl
  unfold arrayElemLayoutOf
  rw [hty]
  have hge : (1021 : Nat) ≥ 1000 := by decide
  have hmod : (1021 - 1000) % 100 = 21 := by decide
  simp only [hge, ↓reduceIte, hmod, layoutOfEncodedTyId, lm21U16Ty]

theorem lm24_wf_u16Arr2 : WellTypedArrayTy emptyLayoutTable lm24U16Arr2Ty (.uint .u16) 2 :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm24_elemLayout_u16Arr2,
    show 0 < 2 by decide, show 2 ≤ 16 by decide, show 2 * 2 < 2 ^ 32 by decide, rfl⟩

/-- Locals: `_0: u16`, `_1: [u16; 3]`, `_2: [u16; 2]`, `_3: [u16; 0]`.
- `stmt 0`: `_2 = move _1[1..3]` (`fromEnd = false`, non-empty subslice,
  `_1` stays initialized)
- `stmt 1`: `_3 = copy _1[1..1]` (`fromEnd = false`, `0`-length subslice into
  `[u16; 0]`)
- `stmt 2`: `_3 = copy _1[2..len - 2]` (`fromEnd = true`, `2 + 2 > 3`
  out-of-bounds UB) -/
def lm24SubsliceBody : CapturedMir where
  defPath := "lm_2_4_witness::subslice"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm21U16Decl, lm21U16Arr3Decl, lm24U16Arr2Decl, lm21U16Arr0Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.use (subsliceReadOperand true 1 1 3 false))),
        mkStmt (.assign (local_ 3) (.use (subsliceReadOperand false 1 1 1 false))),
        mkStmt (.assign (local_ 3) (.use (subsliceReadOperand false 1 2 2 true)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm24_subslice_phase : ∀ p, lm24SubsliceBody.phase ≠ .other p := by
  intro p h; cases h

def lm24SubsliceAnneal (k : Nat) (arrSlot : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := k, locals := [.uninit, arrSlot, .uninit, .uninit] }
    memory := (initMachineState lm24SubsliceBody []).memory }

def lm24SubsliceMiriFrame (k : Nat) (arrOp : Miri.Interpreter.Operand AnnealProv) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm24SubsliceBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21U16Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live arrOp, layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, k⟩ }

def lm24SubsliceMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24SubsliceMiriFrame k (.indirect witnessMemPlace)]⟩
    machine := witnessMachineOf lm21ArrAlloc }

def lm24SubsliceUninitMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24SubsliceMiriFrame k (.immediate .uninit)]⟩
    machine := AnnealMachine.empty }

theorem lm24_subslice_stateRel (k : Nat) :
    StateRel lm24SubsliceBody
      (lm24SubsliceAnneal k (.init (.aggregate 0 lm21ArrElems)))
      (lm24SubsliceMiri k) := by
  refine StateRel.mk (lm24SubsliceMiriFrame k (.indirect witnessMemPlace)) rfl rfl
    ⟨translateTy lm21U16Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j mp_i mp_j lay_i lay_j hneq hi hj
      match i, j with
      | 0, _ | 2, _ | 3, _ | _ + 4, _ => simp [lm24SubsliceMiriFrame] at hi
      | 1, 0 | 1, 2 | 1, 3 | 1, _ + 4 => simp [lm24SubsliceMiriFrame] at hj
      | 1, 1 => exact absurd rfl hneq)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm21U16Decl := by simpa [lm24SubsliceBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24SubsliceMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm24SubsliceBody, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm24SubsliceMiriFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun lm21_memPlaceRel
  | 2 =>
    have hd : decl = lm24U16Arr2Decl := by simpa [lm24SubsliceBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24SubsliceMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = lm21U16Arr0Decl := by simpa [lm24SubsliceBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24SubsliceMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm24SubsliceBody, get?] at hdecl

theorem lm24_subslice_uninit_stateRel (k : Nat) :
    StateRel lm24SubsliceBody (lm24SubsliceAnneal k .uninit) (lm24SubsliceUninitMiri k) := by
  refine StateRel.mk (lm24SubsliceMiriFrame k (.immediate .uninit)) rfl rfl
    ⟨translateTy lm21U16Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => simp [lm24SubsliceMiriFrame] at hi)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24SubsliceMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm24SubsliceBody, get?] at hdecl

theorem lm24_highWater_arr : MemoryHighWater (witnessMachineOf lm21ArrAlloc).memory :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem lm24_subslice_imm (k j : Nat) (hj : j ≠ 1) :
    IsImmediateFrameLocal (lm24SubsliceMiriFrame k (.indirect witnessMemPlace)) j := by
  intro mls hmls mp hv
  match j with
  | 0 | 2 | 3 => simp [lm24SubsliceMiriFrame] at hmls; subst hmls; cases hv
  | 1 => exact absurd rfl hj
  | _ + 4 => simp [lm24SubsliceMiriFrame] at hmls

/-- **Witness for `step_subslice_assign_simulation`**: chained execution of
`_2 = move _1[1..3]` followed by `_3 = copy _1[1..1]` on
`_1 = [0x0102, 0x0304, 0x0506]`. Step 1 extracts `[0x0304, 0x0506]` into `_2`
while keeping `_1` initialized despite `move`; Step 2 extracts `[] : [u16; 0]`
into `_3` across the `0`-byte canonicalization path of `annealMemCopyOp`, using
only the invariants re-established by Step 1. -/
theorem lm24_subslice_assign_steps :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (mp₂ mp₃ : Miri.Interpreter.MemPlace AnnealProv),
      stepMirFn lm24SubsliceBody
        (lm24SubsliceAnneal 0 (.init (.aggregate 0 lm21ArrElems))) = .step s₁ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24SubsliceBody.localDecls lm24SubsliceBody.layouts) ()
          (lm24SubsliceMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24SubsliceBody s₁ m₁ ∧
      get? s₁.frame.locals 2 =
        some (.init (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩])) ∧
      get? s₁.frame.locals 1 = some (.init (.aggregate 0 lm21ArrElems)) ∧
      MemPlaceRel m₁.machine lm24U16Arr2Ty emptyLayoutTable
        (some (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩])) mp₂ ∧
      stepMirFn lm24SubsliceBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24SubsliceBody.localDecls lm24SubsliceBody.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24SubsliceBody s₂ m₂ ∧
      get? s₂.frame.locals 3 = some (.init (.aggregate 0 [])) ∧
      MemPlaceRel m₂.machine lm21U16Arr0Ty emptyLayoutTable (some (.aggregate 0 [])) mp₃ := by
  have hd2_imm : ∀ tf, (lm24SubsliceMiri 0).stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf h
    have htf : lm24SubsliceMiriFrame 0 (.indirect witnessMemPlace) = tf := by
      simpa [lm24SubsliceMiri] using h
    subst htf
    exact lm24_subslice_imm 0 2 (by decide)
  obtain ⟨s₁, m₁, mp₂, tf₁, hs₁, hm₁, hst₁, hd₂, ha₁, hpres₁, hframes₁, _, hmp₂, hnodup₁,
    himm₁, hblk₁, hidx₁, hhw₁⟩ :=
    ((step_subslice_assign_simulation (lm24_subslice_stateRel 0).toLM2_4 lm21_nodup_arr
      lm24_highWater_arr.canReserveAllocId lm24_subslice_phase (d := 2) (arrIdx := 1)
      (isMove := true) (fromIdx := 1) (toIdx := 3) (fromEnd := false) (bb := _)
      rfl rfl rfl rfl lm21_wf_u16Arr3 lm24_wf_u16Arr2 rfl hd2_imm).2 lm21ArrElems rfl).2
      (Or.inl ⟨rfl, by decide, by decide⟩)
  obtain ⟨hhw₁', _⟩ := hhw₁ rfl lm24_highWater_arr
    (show (witnessMachineOf lm21ArrAlloc).memory.nextAllocId.toNat + 1 < 2 ^ 64 by decide)
  have hd3_uninit : get? s₁.frame.locals 3 = some .uninit := by
    rw [hpres₁ 3 (by decide)]; rfl
  have hd3_imm : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 := by
    intro tf h
    rw [hframes₁] at h
    have htf : tf₁ = tf := by simpa using h
    subst htf
    exact himm₁ _ rfl 3 (by decide) (lm24_subslice_imm 0 3 (by decide))
  have hbb₁ : get? lm24SubsliceBody.basicBlocks s₁.frame.blockIdx =
      get? lm24SubsliceBody.basicBlocks 0 := by rw [hblk₁]; rfl
  rw [show get? lm24SubsliceBody.basicBlocks 0 = _ from rfl] at hbb₁
  have hstmt₁ : get? (lm24SubsliceBody.basicBlocks[0]'(by decide)).statements s₁.frame.stmtIdx =
      some (mkStmt (.assign (local_ 3) (.use (subsliceReadOperand false 1 1 1 false)))) := by
    rw [hidx₁]; rfl
  obtain ⟨s₂, m₂, mp₃, _, hs₂, hm₂, hst₂, hd₃, _, _, _, _, hmp₃, _, _, _, _, _⟩ :=
    ((step_subslice_assign_simulation hst₁ hnodup₁ hhw₁'.canReserveAllocId lm24_subslice_phase
      (d := 3) (arrIdx := 1) (isMove := false) (fromIdx := 1) (toIdx := 1) (fromEnd := false)
      hbb₁ hstmt₁ rfl rfl lm21_wf_u16Arr3 lm21_wf_u16Arr0 hd3_uninit hd3_imm).2
      lm21ArrElems ha₁).2 (Or.inl ⟨rfl, by decide, by decide⟩)
  exact ⟨s₁, s₂, m₁, m₂, mp₂, mp₃, hs₁, hm₁, hst₁, hd₂, ha₁, hmp₂, hs₂, hm₂, hst₂, hd₃, hmp₃⟩

/-- **Witness for `step_subslice_assign_simulation` UB branches**: out-of-bounds
`fromEnd = true` (`_3 = copy _1[2..len - 2]` on `[u16; 3]`) and uninitialized
`_2 = move _1[1..3]` both report undefined behavior in Anneal and
`lean-miri`. -/
theorem lm24_subslice_assign_oob_and_uninit_ub :
    (stepMirFn lm24SubsliceBody
      (lm24SubsliceAnneal 2 (.init (.aggregate 0 lm21ArrElems))) = .fail .ub ∧
     StepRelLM2_4 lm24SubsliceBody (lm24SubsliceMiri 2)
      (stepMirFn lm24SubsliceBody (lm24SubsliceAnneal 2 (.init (.aggregate 0 lm21ArrElems))))
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 lm24SubsliceBody.localDecls lm24SubsliceBody.layouts) ()
        (lm24SubsliceMiri 2))) ∧
    (stepMirFn lm24SubsliceBody (lm24SubsliceAnneal 0 .uninit) = .fail .ub ∧
     StepRelLM2_4 lm24SubsliceBody (lm24SubsliceUninitMiri 0)
      (stepMirFn lm24SubsliceBody (lm24SubsliceAnneal 0 .uninit))
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 lm24SubsliceBody.localDecls lm24SubsliceBody.layouts) ()
        (lm24SubsliceUninitMiri 0))) := by
  have hd3_imm : ∀ tf, (lm24SubsliceMiri 2).stack.frames = #[tf] → IsImmediateFrameLocal tf 3 := by
    intro tf h
    have htf : lm24SubsliceMiriFrame 2 (.indirect witnessMemPlace) = tf := by
      simpa [lm24SubsliceMiri] using h
    subst htf
    exact lm24_subslice_imm 2 3 (by decide)
  have hd2_imm :
      ∀ tf, (lm24SubsliceUninitMiri 0).stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf h
    have htf : lm24SubsliceMiriFrame 0 (.immediate .uninit) = tf := by
      simpa [lm24SubsliceUninitMiri] using h
    subst htf
    intro mls hmls mp hv
    simp [lm24SubsliceMiriFrame] at hmls; subst hmls; cases hv
  refine ⟨?_, ?_⟩
  · exact ((step_subslice_assign_simulation (lm24_subslice_stateRel 2).toLM2_4 lm21_nodup_arr
      lm24_highWater_arr.canReserveAllocId lm24_subslice_phase (d := 3) (arrIdx := 1)
      (isMove := false) (fromIdx := 2) (toIdx := 2) (fromEnd := true) (bb := _)
      rfl rfl rfl rfl lm21_wf_u16Arr3 lm21_wf_u16Arr0 rfl hd3_imm).2 lm21ArrElems rfl).1
      rfl (by decide) (by decide)
  · exact (step_subslice_assign_simulation (lm24_subslice_uninit_stateRel 0).toLM2_4
      lm21_nodup_empty lm24_canReserve_empty lm24_subslice_phase (d := 2) (arrIdx := 1)
      (isMove := true) (fromIdx := 1) (toIdx := 3) (fromEnd := false) (bb := _)
      rfl rfl rfl rfl lm21_wf_u16Arr3 lm24_wf_u16Arr2 rfl hd2_imm).1
      (Or.inr ⟨rfl, Or.inl (by decide)⟩)

def lm24ZeroUninitFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm24SubsliceBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21U16Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.indirect witnessMemPlace), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def lm24ZeroUninitMiri
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealStepState :=
  { stack := ⟨#[lm24ZeroUninitFrame]⟩, machine := witnessMachineOf alloc }

private theorem lm24_zero_uninit_stateRel
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hmp : MemPlaceRel (witnessMachineOf alloc) lm21U16Arr0Ty emptyLayoutTable none
      witnessMemPlace) :
    StateRel lm24SubsliceBody (lm24SubsliceAnneal 0 .uninit) (lm24ZeroUninitMiri alloc) := by
  refine StateRel.mk lm24ZeroUninitFrame rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ hneq hi hj
      match i, j with
      | 0, _ | 1, _ | 2, _ | _ + 4, _ => simp [lm24ZeroUninitFrame] at hi
      | 3, 0 | 3, 1 | 3, 2 | 3, _ + 4 => simp [lm24ZeroUninitFrame] at hj
      | 3, 3 => exact absurd rfl hneq)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 =>
    have hs : slot = .uninit := by simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24ZeroUninitFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = lm21U16Arr0Decl := by simpa [lm24SubsliceBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm24SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm24ZeroUninitFrame] using hmls.symm
    subst hd hs hm
    exact .indirect .uninit witnessMemPlace none (fun _ h => nomatch h) nofun hmp
  | _ + 4 =>
    simp [lm24SubsliceBody, get?] at hdecl

/-- **Witness for `evalSubsliceOperand_zero_uninit_indirect_characterization`**:
for `_3 : [u16; 0]` held as `.uninit` in Anneal and
`.live (.indirect witnessMemPlace)` in `lean-miri`, `copy _3[0..0]` reports
undefined behavior in both machines when backed by `witnessUninitAlloc`
(`blocks = .Lazy false`), and succeeds in `lean-miri` (while Anneal reports
`.ub`) when backed by `lm21ArrAlloc`
(`initializationMask = InitMask.new _ true`). -/
theorem lm24_zero_uninit_indirect_subslice_witness :
    (evalOperand (lm24SubsliceAnneal 0 .uninit).frame.locals
        (subsliceReadOperand false 3 0 0 false) .nil
        (lm24SubsliceAnneal 0 .uninit).memory.globals emptyLayoutTable .nil = .ub ∧
     ∃ topFrame',
       annealEvalOperandLM2_4 lm24SubsliceBody.localDecls emptyLayoutTable
         (translateOperand (subsliceReadOperand false 3 0 0 false)) none
         (lm24ZeroUninitMiri witnessUninitAlloc) =
       .error (.undefinedBehavior "access to uninitialized indirect place")
         { (lm24ZeroUninitMiri witnessUninitAlloc) with stack := ⟨#[topFrame']⟩ }) ∧
    (evalOperand (lm24SubsliceAnneal 0 .uninit).frame.locals
        (subsliceReadOperand false 3 0 0 false) .nil
        (lm24SubsliceAnneal 0 .uninit).memory.globals emptyLayoutTable .nil = .ub ∧
     ∃ (op : Miri.Interpreter.OpTy AnnealProv) (topFrame' : Miri.Interpreter.Frame AnnealProv
         Miri.Interpreter.LocalLayout Unit),
       annealEvalOperandLM2_4 lm24SubsliceBody.localDecls emptyLayoutTable
         (translateOperand (subsliceReadOperand false 3 0 0 false)) none
         (lm24ZeroUninitMiri lm21ArrAlloc) =
       .ok op { (lm24ZeroUninitMiri lm21ArrAlloc) with stack := ⟨#[topFrame']⟩ } ∧
       op.op = .indirect witnessMemPlace) := by
  have hmp_false : MemPlaceRel (witnessMachineOf witnessUninitAlloc) lm21U16Arr0Ty
      emptyLayoutTable none witnessMemPlace :=
    MemPlaceRel.mk witnessAllocId witnessTag witnessBaseAddr witnessRelOffset
      { kind := .stack, allocation := witnessUninitAlloc } rfl rfl rfl (List.Mem.head _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ h => absurd h (by decide))
      (fun _ h _ => nomatch h) (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  have hmp_true : MemPlaceRel (witnessMachineOf lm21ArrAlloc) lm21U16Arr0Ty
      emptyLayoutTable none witnessMemPlace :=
    MemPlaceRel.mk witnessAllocId witnessTag witnessBaseAddr witnessRelOffset
      { kind := .stack, allocation := lm21ArrAlloc } rfl rfl rfl (List.Mem.head _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ h => absurd h (by decide))
      (fun _ h _ => nomatch h) (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  have hnodup_u : LiveAllocsNodup (witnessMachineOf witnessUninitAlloc) :=
    List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  obtain ⟨_, _, la₁, tf₁, _, hlive₁, _, hfalse, _⟩ :=
    evalSubsliceOperand_zero_uninit_indirect_characterization
      (lm24_zero_uninit_stateRel witnessUninitAlloc hmp_false).toLM2_4 rfl hnodup_u
      (arrIdx := 3) rfl lm21_wf_u16Arr0 rfl rfl
  have hla₁ : la₁.allocation = witnessUninitAlloc := by
    simp [lm24ZeroUninitMiri, witnessMachineOf] at hlive₁
    rw [hlive₁.2]
  obtain ⟨ha₁, hm₁⟩ := hfalse (by rw [hla₁]; rfl) false 0 0 false none
  obtain ⟨_, _, la₂, tf₂, _, hlive₂, _, _, htrue⟩ :=
    evalSubsliceOperand_zero_uninit_indirect_characterization
      (lm24_zero_uninit_stateRel lm21ArrAlloc hmp_true).toLM2_4 rfl lm21_nodup_arr
      (arrIdx := 3) rfl lm21_wf_u16Arr0 rfl rfl
  have hla₂ : la₂.allocation = lm21ArrAlloc := by
    simp [lm24ZeroUninitMiri, witnessMachineOf] at hlive₂
    rw [hlive₂.2]
  obtain ⟨ha₂, hm₂⟩ := htrue (by rw [hla₂]; rfl) false false none
  exact ⟨⟨ha₁, tf₁, hm₁⟩, ⟨ha₂, _, tf₂, hm₂, rfl⟩⟩

/-! ## 10. Union In-Place Overwrites, Lifecycle (`StorageLive`/`StorageDead`), `Rvalue.Repeat`, and Boundary Divergences -/

def lm24U8Arr3Ty : Ty := { kind := .array (.uint .u8) 3, layoutIdx := 3 }
def lm24U8Arr3Decl : LocalDecl := { mutability := .mut, ty := lm24U8Arr3Ty, debugName := none }

private theorem lm24_elemLayout_u8Arr3 :
    arrayElemLayoutOf lm24Layouts
      (translateTy lm24U8Arr3Ty lm24Layouts)
      (translateTy lm24U8Ty lm24Layouts).layout.size =
    translateTy lm24U8Ty lm24Layouts := by
  have hty : (translateTy lm24U8Arr3Ty lm24Layouts).ty = 1320 := rfl
  unfold arrayElemLayoutOf
  rw [hty]
  have hge : (1320 : Nat) ≥ 1000 := by decide
  have hmod : (1320 - 1000) % 100 = 20 := by decide
  simp only [hge, ↓reduceIte, hmod, layoutOfEncodedTyId, lm24U8Ty]
  rfl

theorem lm24_wf_u8Arr3 : WellTypedArrayTy lm24Layouts lm24U8Arr3Ty (.uint .u8) 3 :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm24_elemLayout_u8Arr3,
    show 0 < 1 by decide, show 1 ≤ 16 by decide, show 3 * 1 < 2 ^ 32 by decide, rfl⟩

/-- Locals: `_0: u32`, `_1: U`, `_2: u8`, `_3: [u8; 3]`, `_4: U`.
- `bb0`: 8-step lifecycle & overwrite chain:
  `_1 = U { a: 5 }; _4 = copy _1; _4 = copy _1;
   _4 = U { 0: 0x05060708_u32 }; StorageDead(_1); StorageLive(_1);
   StorageDead(_1); _1 = U { a: 9 }`
- `bb1`: `_1 = U { a: 5 }; _1 = copy _1` (self-copy overlap divergence)
- `bb2`: `_4 = copy _1` (whole-union copy of indirect uninitialized `_1`)
- `bb3`: `_1 = U { 0: 0x01020304_u32 }; _1 = U { a: 0x77_u8 }` (smaller union
  aggregate overwrite `I-11` divergence)
- `bb4`: `_1 = U { a: 5 }; _3 = [copy (_1.0: u8); 3]`
  (`Rvalue.Repeat` normal lockstep)
- `bb5`: `_1 = U { a: 5 }; _3 = [copy (_1.1: u32); 3]`
  (`Rvalue.Repeat` wider uninitialized union field UB) -/
def lm24A2UnionBody : CapturedMir where
  defPath := "lm_2_4_witness::a2_unions"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm24Decl lm24U32Ty, lm24Decl lm24UTy, lm24Decl lm24U8Ty,
    lm24U8Arr3Decl, lm24Decl lm24UTy]
  basicBlocks := [
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        lm24AggU32Stmt 4 0x05060708,
        mkStmt (.storageDead 1),
        mkStmt (.storageLive 1),
        mkStmt (.storageDead 1),
        lm24AggStmt 1 9],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 1) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggU32Stmt 1 0x01020304,
        lm24AggStmt 1 0x77],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 3) (.repeat (unionFieldReadOperand false 1 0 lm24U8Ty) 3))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 3) (.repeat (unionFieldReadOperand false 1 1 lm24U32Ty) 3))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        lm24AggStmt 1 5,
        mkStmt (.assign (local_ 1) (.use (.move (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm24FnAbi
  layouts := lm24Layouts
  allocations := []

theorem lm24A2_phase : ∀ p, lm24A2UnionBody.phase ≠ .other p := by
  intro p h; cases h

private theorem lm24A2_decls_adt :
    ∀ l ∈ collectAdtLayoutsInDecls lm24A2UnionBody.layouts "U" lm24A2UnionBody.localDecls,
      lm24A2UnionBody.layouts.entries[(lm24Decl lm24UTy).ty.layoutIdx]? = some l := by
  have hs : stringEq "U" "U" = true := by decide
  simp [collectAdtLayoutsInDecls, collectAdtLayoutsInTyAux, hs, LayoutTable.lookup,
    lm24A2UnionBody, lm24Layouts, lm24Decl, lm24UTy, lm24U8Ty, lm24U32Ty,
    lm24U8Arr3Decl, lm24U8Arr3Ty, get?, eq_comm]

def lm24A2InitAnneal (b : Nat) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := 0,
               locals := [.uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm24A2UnionBody []).memory }

def lm24A2AnnealState (b k : Nat) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := k, locals := locals }
    memory := (initMachineState lm24A2UnionBody []).memory }

def lm24A2InitMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm24A2UnionBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm24U32Ty lm24Layouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨b, 0⟩ }

def lm24A2InitMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24A2InitMiriFrame b]⟩, machine := AnnealMachine.empty }

theorem lm24A2_init_stateRel (b : Nat) :
    StateRel lm24A2UnionBody (lm24A2InitAnneal b) (lm24A2InitMiri b) := by
  refine StateRel.mk (lm24A2InitMiriFrame b) rfl rfl ⟨translateTy lm24U32Ty lm24Layouts, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      match i with
      | 0 | 1 | 2 | 3 | 4 => simp [lm24A2InitMiriFrame] at hi
      | _ + 5 => simp [lm24A2InitMiriFrame] at hi)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 | 4 =>
    have hs : slot = .uninit := by simpa [lm24A2InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24A2InitMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 5 =>
    simp [lm24A2UnionBody, get?] at hdecl

theorem lm24A2_init_imm (b j : Nat) : IsImmediateFrameLocal (lm24A2InitMiriFrame b) j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 | 3 | 4 => simp [lm24A2InitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 5 => simp [lm24A2InitMiriFrame] at hmls

theorem lm24A2_init_frame_imm (b j : Nat) :
    ∀ tf, (lm24A2InitMiri b).stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
  intro tf h
  have htf : lm24A2InitMiriFrame b = tf := by simpa [lm24A2InitMiri] using h
  subst htf
  exact lm24A2_init_imm b j

theorem lm24A2_constU8_wt (n : Nat) (hn : n < 256)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand lm24A2UnionBody tf (.constant (lm24ConstU8 n)) lm24U8Ty :=
  .constScalar (lm24ConstU8 n) ⟨n, 1⟩ rfl lm24_isPrim_u8 (Or.inl rfl) hn rfl
    (fun h => nomatch h) (fun h => nomatch h)

theorem lm24A2_constU32_wt (n : Nat) (hn : n < scalarModulus 4)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand lm24A2UnionBody tf (.constant (lm24ConstU32 n)) lm24U32Ty :=
  .constScalar (lm24ConstU32 n) ⟨n, 4⟩ rfl lm24_isPrim_u32
    (Or.inr (Or.inr (Or.inl rfl))) hn rfl (fun h => nomatch h) (fun h => nomatch h)

def lm24UU32Slot2 : LocalSlot := .init (.aggregate 0 [.unit, .scalar ⟨0x05060708, 4⟩])

theorem lm24A2_bb0_a₁ : stepMirFn lm24A2UnionBody (lm24A2InitAnneal 0) =
    .step (lm24A2AnnealState 0 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl
theorem lm24A2_bb0_a₂ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24A2AnnealState 0 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) := rfl
theorem lm24A2_bb0_a₃ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 2 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) =
      .step (lm24A2AnnealState 0 3 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) := rfl
theorem lm24A2_bb0_a₄ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 3 [.uninit, lm24USlot, .uninit, .uninit, lm24USlot]) =
      .step (lm24A2AnnealState 0 4 [.uninit, lm24USlot, .uninit, .uninit, lm24UU32Slot2]) := rfl
theorem lm24A2_bb0_a₅ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 4 [.uninit, lm24USlot, .uninit, .uninit, lm24UU32Slot2]) =
      .step (lm24A2AnnealState 0 5 [.uninit, .dead, .uninit, .uninit, lm24UU32Slot2]) := rfl
theorem lm24A2_bb0_a₆ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 5 [.uninit, .dead, .uninit, .uninit, lm24UU32Slot2]) =
      .step (lm24A2AnnealState 0 6 [.uninit, .uninit, .uninit, .uninit, lm24UU32Slot2]) := rfl
theorem lm24A2_bb0_a₇ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 6 [.uninit, .uninit, .uninit, .uninit, lm24UU32Slot2]) =
      .step (lm24A2AnnealState 0 7 [.uninit, .dead, .uninit, .uninit, lm24UU32Slot2]) := rfl
theorem lm24A2_bb0_a₈ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 0 7 [.uninit, .dead, .uninit, .uninit, lm24UU32Slot2]) = .fail .ub := rfl

/-- **Witness for `step_union_whole_copy_or_move_overwrite_simulation`,
`step_union_aggregate_overwrite_simulation`, `step_storageDead_LM2_4_simulation`,
and `step_storageLive_LM2_4_simulation`**: 8-step concrete execution in `bb0` of
`lm24A2UnionBody` chaining:
1. `_1 = U { a: 5_u8 }` (fresh `1`-byte union allocation for `_1`),
2. `_4 = copy _1` (fresh `1`-byte union allocation for `_4`),
3. `_4 = copy _1` (in-place whole-union overwrite of `_4` via
   `step_union_whole_copy_or_move_overwrite_simulation`),
4. `_4 = U { 0: 0x05060708_u32 }` (in-place aggregate overwrite widening `_4`'s
   `InitMask` from `1` byte up to `4` bytes via `step_union_aggregate_overwrite_simulation`),
5. `StorageDead(_1)` (freeing `_1`'s union allocation via `step_storageDead_LM2_4_simulation`),
6. `StorageLive(_1)` (re-activating `_1` via `step_storageLive_LM2_4_simulation`),
7. `StorageDead(_1)`, and
8. `_1 = U { a: 9_u8 }` into `.dead` `_1` (reporting UB in lockstep via
   `step_union_aggregate_overwrite_simulation` branch `(1)`). -/
theorem lm24_overwrite_and_lifecycle_steps :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : AnnealStepState)
      (mp₁ mp₄ : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          (lm24A2InitMiri 0) = (m₁, .ok true) ∧
      UnionMemRel m₁.machine lm24UTy lm24Layouts 4 lm24U8Ty ⟨5, 1⟩ mp₁ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          m₁ = (m₂, .ok true) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          m₂ = (m₃, .ok true) ∧
      UnionMemRel m₃.machine lm24UTy lm24Layouts 4 lm24U8Ty ⟨5, 1⟩ mp₄ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          m₃ = (m₄, .ok true) ∧
      UnionMemRel m₄.machine lm24UTy lm24Layouts 4 lm24U32Ty ⟨0x05060708, 4⟩ mp₄ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          m₄ = (m₅, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody
        (lm24A2AnnealState 0 5 [.uninit, .dead, .uninit, .uninit, lm24UU32Slot2]) m₅ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          m₅ = (m₆, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody
        (lm24A2AnnealState 0 6 [.uninit, .uninit, .uninit, .uninit, lm24UU32Slot2]) m₆ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          m₆ = (m₇, .ok true) ∧
      StepRelLM2_4 lm24A2UnionBody m₇
        (stepMirFn lm24A2UnionBody
          (lm24A2AnnealState 0 7 [.uninit, .dead, .uninit, .uninit, lm24UU32Slot2]))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₇) := by
  -- Step 1: `_1 = U { a: 5 }`
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24A2_init_stateRel 0).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24A2_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24A2_init_frame_imm 0 1) lm24_isPrim_u8
    (fun tf _ => lm24A2_constU8_wt 5 (by decide) tf) (by decide)
    (hdecls_adt := lm24A2_decls_adt)
  obtain ⟨sc₁, mp₁, m₁, tf₁, hstep₁, hop₁, hst₁, _, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    himm₁, _, _, _, hhw₁⟩ := hpost₁ _ lm24A2_bb0_a₁
  have hsc₁ : sc₁ = ⟨5, 1⟩ := by
    have h : evalOperand (lm24A2InitAnneal 0).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24A2InitAnneal 0).memory.globals lm24A2UnionBody.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24A2InitAnneal 0).frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  obtain ⟨hhw₁', _⟩ := hhw₁ rfl MemoryHighWater.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 64 by decide)
  have hu1_mls₁ : ∀ tf, m₁.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp₁), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have hw4_imm₁ : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 4 := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact himm₁ (lm24A2InitMiriFrame 0) rfl 4 (by decide) (lm24A2_init_imm 0 4)
  -- Step 2: `_4 = copy _1` (fresh allocation for `_4`, preserving `_1` too!)
  obtain ⟨s₂, m₂, mp₄, tf₂, hs₂, hstep₂, hst₂, _, _, hframes₂, ⟨c₄_2, hmls₄_2⟩,
    ⟨c₁_2, hmls₁_2⟩, hmem₁_2, hmem₄_2, hnodup₂, _, _, _, _⟩ :=
    union_whole_copy_initMask_preservation_simulation hst₁ hnodup₁ hhw₁'.canReserveAllocId
      lm24A2_phase (w := 4) (u := 1) (bb := _) rfl rfl rfl rfl rfl (f := 0) lm24_wt_U rfl
      (by decide) rfl hu1_mls₁ hmem₁ rfl hw4_imm₁
  have hs₂_eq := MirStepNode_step_inj (lm24A2_bb0_a₂.symm.trans hs₂)
  subst hs₂_eq
  have hu1_mls₂ : ∀ tf, m₂.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp₁), c⟩ := by
    intro tf htf; rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h; exact ⟨c₁_2, hmls₁_2⟩
  have hw4_mls₂ : ∀ tf, m₂.stack.frames = #[tf] →
      ∃ c, tf.locals[4]? = some ⟨.live (.indirect mp₄), c⟩ := by
    intro tf htf; rw [hframes₂] at htf
    have h : tf₂ = tf := by simpa using htf
    subst h; exact ⟨c₄_2, hmls₄_2⟩
  -- Step 3: `_4 = copy _1` (in-place whole-union overwrite of `_4`)
  obtain ⟨s₃, m₃, tf₃, hs₃, hstep₃, hst₃, _, _, hframes₃, ⟨c₄_3, hmls₄_3⟩, hmem₄_3,
    hnodup₃, _⟩ :=
    (step_union_whole_copy_or_move_overwrite_simulation hst₂ hnodup₂ lm24A2_phase
      (w := 4) (u := 1) (isMove := false) (bb := _) rfl rfl rfl rfl rfl lm24_wt_U (n := 2) rfl).2.2
      0 0 lm24U8Ty ⟨5, 1⟩ mp₁ lm24U8Ty ⟨5, 1⟩ mp₄ (by decide) (by decide) (by decide) rfl
      hu1_mls₂ hmem₁_2 rfl hw4_mls₂ hmem₄_2
  have hs₃_eq := MirStepNode_step_inj (lm24A2_bb0_a₃.symm.trans hs₃)
  subst hs₃_eq
  have hw4_mls₃ : ∀ tf, m₃.stack.frames = #[tf] →
      ∃ c, tf.locals[4]? = some ⟨.live (.indirect mp₄), c⟩ := by
    intro tf htf; rw [hframes₃] at htf
    have h : tf₃ = tf := by simpa using htf
    subst h; exact ⟨c₄_3, hmls₄_3⟩
  -- Step 4: `_4 = U { b: 0x05060708_u32 }` (in-place aggregate overwrite widening `1 -> 4` bytes)
  obtain ⟨_, hpost₄⟩ :=
    (step_union_aggregate_overwrite_simulation hst₃ hnodup₃ lm24A2_phase (u := 4) (bb := _)
      rfl rfl rfl lm24_wt_U rfl (by decide) rfl rfl lm24_isPrim_u32
      (fun tf _ => lm24A2_constU32_wt 0x05060708 (by rw [scalarModulus_eq_two_pow]; decide) tf)
      (by decide) (hdecls_adt := lm24A2_decls_adt)).2 0 lm24U8Ty ⟨5, 1⟩ mp₄ (by decide) rfl
      hw4_mls₃ hmem₄_3 (by decide)
  obtain ⟨sc₄, m₄, _, hstep₄, hst₄, hw4_slot₄, _, _, hmem₄_4, hnodup₄, _⟩ :=
    hpost₄ _ lm24A2_bb0_a₄
  have hsc₄ : sc₄ = ⟨0x05060708, 4⟩ := by
    have h : get?
        (lm24A2AnnealState 0 4 [.uninit, lm24USlot, .uninit, .uninit, lm24UU32Slot2]).frame.locals
        4 = some lm24UU32Slot2 := rfl
    rw [h] at hw4_slot₄
    dsimp only [lm24UU32Slot2, unionSlotFields, replicateValue, appendValueList] at hw4_slot₄
    injection hw4_slot₄ with h1
    injection h1 with h1
    injection h1 with _ h1
    injection h1 with _ h1
    injection h1 with h1 _
    injection h1 with h1
    exact h1.symm
  subst hsc₄
  -- Step 5: `StorageDead(_1)` (deallocates `_1`'s union stack allocation)
  obtain ⟨hrel₅, hpn₅, _⟩ := step_storageDead_LM2_4_simulation hst₄ hnodup₄ lm24A2_phase
    (loc := 1) (bb := _) rfl rfl rfl (by decide)
  rw [lm24A2_bb0_a₅] at hrel₅
  generalize hstep₅ : Miri.Interpreter.Step.step
    (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₄ = r₅ at hrel₅ hpn₅
  cases hrel₅ with
  | step _ m₅ hst₅ =>
    have hnodup₅ : LiveAllocsNodup m₅.machine := hpn₅ rfl
    -- Step 6: `StorageLive(_1)`
    obtain ⟨hrel₆, hpn₆, _⟩ := step_storageLive_LM2_4_simulation hst₅ hnodup₅ lm24A2_phase
      (loc := 1) (bb := _) rfl rfl rfl
    rw [lm24A2_bb0_a₆] at hrel₆
    generalize hstep₆ : Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₅ = r₆ at hrel₆ hpn₆
    cases hrel₆ with
    | step _ m₆ hst₆ =>
      have hnodup₆ : LiveAllocsNodup m₆.machine := hpn₆ rfl
      -- Step 7: `StorageDead(_1)`
      obtain ⟨hrel₇, hpn₇, _⟩ := step_storageDead_LM2_4_simulation hst₆ hnodup₆ lm24A2_phase
        (loc := 1) (bb := _) rfl rfl rfl (by decide)
      rw [lm24A2_bb0_a₇] at hrel₇
      generalize hstep₇ : Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₆ = r₇ at hrel₇ hpn₇
      cases hrel₇ with
      | step _ m₇ hst₇ =>
        have hnodup₇ : LiveAllocsNodup m₇.machine := hpn₇ rfl
        -- Step 8: `_1 = U { a: 9_u8 }` into `.dead` `_1` -> UB in both!
        have hrel₈ :=
          (step_union_aggregate_overwrite_simulation hst₇ hnodup₇ lm24A2_phase (u := 1) (bb := _)
            rfl rfl rfl lm24_wt_U rfl (by decide) rfl rfl lm24_isPrim_u8
            (fun tf _ => lm24A2_constU8_wt 9 (by decide) tf) (by decide)
            (hdecls_adt := lm24A2_decls_adt)).1 rfl
        exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, mp₁, mp₄, hstep₁, hmem₁, hstep₂, hstep₃, hmem₄_3,
          hstep₄, hmem₄_4, hstep₅, hst₅, hstep₆, hst₆, hstep₇, hrel₈⟩

theorem lm24A2_bb1_a₁ : stepMirFn lm24A2UnionBody (lm24A2InitAnneal 1) =
    .step (lm24A2AnnealState 1 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl

/-- **Witness for `step_union_self_copy_overlap_divergence`**: in `bb1` of
`lm24A2UnionBody`, `_1 = U { a: 5 }` steps normally in both machines, and
self-copy `_1 = copy _1` steps normally in Anneal while `lean-miri` reports
`StepError.undefinedBehavior "whole-value copy between overlapping ranges"`. -/
theorem lm24_union_self_copy_overlap_divergence :
    ∃ (m₁ m₂ : AnnealStepState) (s₂ : MachineState),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          (lm24A2InitMiri 1) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody
        (lm24A2AnnealState 1 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn lm24A2UnionBody
        (lm24A2AnnealState 1 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) = .step s₂ ∧
      get? s₂.frame.locals 1 = some lm24USlot ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₁ =
        (m₂, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24A2_init_stateRel 1).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24A2_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24A2_init_frame_imm 1 1) lm24_isPrim_u8
    (fun tf _ => lm24A2_constU8_wt 5 (by decide) tf) (by decide)
    (hdecls_adt := lm24A2_decls_adt)
  obtain ⟨sc₁, mp₁, m₁, tf₁, hstep₁, hop₁, hst₁, _, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    _, _, _, _, _⟩ := hpost₁ _ lm24A2_bb1_a₁
  have hsc₁ : sc₁ = ⟨5, 1⟩ := by
    have h : evalOperand (lm24A2InitAnneal 1).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24A2InitAnneal 1).memory.globals lm24A2UnionBody.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24A2InitAnneal 1).frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  have hu1_mls₁ : ∀ tf, m₁.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp₁), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  obtain ⟨⟨s₂, hs₂, hslot₂⟩, m₂, hm₂⟩ :=
    step_union_self_copy_overlap_divergence hst₁ hnodup₁ lm24A2_phase (u := 1) (bb := _)
      rfl rfl rfl lm24_wt_U (n := 2) (f := 0) rfl hu1_mls₁ hmem₁
  exact ⟨m₁, m₂, s₂, hstep₁, hst₁, hs₂, hslot₂, hm₂⟩

def lm24InitAlloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[0, 0, 0, 0] (translateAlignBytes 4) .Mut)
    (by decide)).withExtra none

def lm24UninitAlloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeUninit
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4))
      (Miri.ABI.Size.ofBytes 8)
      lm24InitAlloc4 with
  | .ok () alloc => alloc
  | .error _ alloc => alloc

def lm24BaseMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes witnessBaseAddr, some (.concrete witnessAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm24A2UninitIndirectFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (lm24A2InitMiriFrame 2) with
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.indirect lm24BaseMemPlace), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }] }

def lm24A2UninitIndirectMiri : AnnealStepState :=
  { stack := ⟨#[lm24A2UninitIndirectFrame]⟩, machine := witnessMachineOf lm24UninitAlloc4 }

private theorem lm24A2_uninit_indirect_stateRel :
    StateRel lm24A2UnionBody (lm24A2InitAnneal 2) lm24A2UninitIndirectMiri := by
  have hmp : MemPlaceRel (witnessMachineOf lm24UninitAlloc4) lm24UTy lm24Layouts none
      lm24BaseMemPlace :=
    MemPlaceRel.mk witnessAllocId witnessTag witnessBaseAddr Miri.ABI.Size.ZERO
      { kind := .stack, allocation := lm24UninitAlloc4 } rfl rfl rfl (List.Mem.head _)
      (by decide) (by decide) (by decide) (by decide)
      (by
        change lm24BaseMemPlace.ptr.offset.isAligned (translateAlignBytes 4) = .ok true
        decide)
      (by
        change Miri.ABI.Size.ZERO.bytes.toNat + 4 ≤ lm24UninitAlloc4.byteSize.bytes.toNat
        decide)
      (fun _ _ => by
        change lm24UninitAlloc4.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) ≠ .ok (.ok ())
        decide)
      (fun _ h _ => nomatch h) (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  refine StateRel.mk lm24A2UninitIndirectFrame rfl rfl
    ⟨translateTy lm24U32Ty lm24Layouts, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ hneq hi hj
      match i, j with
      | 0, _ | 2, _ | 3, _ | 4, _ | _ + 5, _ => simp [lm24A2UninitIndirectFrame] at hi
      | 1, 0 | 1, 2 | 1, 3 | 1, 4 | 1, _ + 5 => simp [lm24A2UninitIndirectFrame] at hj
      | 1, 1 => exact absurd rfl hneq)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 | 4 =>
    have hs : slot = .uninit := by simpa [lm24A2InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24A2UninitIndirectFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm24Decl lm24UTy := by simpa [lm24A2UnionBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm24A2InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect lm24BaseMemPlace), layout := none } := by
      simpa [lm24A2UninitIndirectFrame] using hmls.symm
    subst hd hs hm
    exact .indirect .uninit lm24BaseMemPlace none (fun _ h => nomatch h) nofun hmp
  | _ + 5 =>
    simp [lm24A2UnionBody, get?] at hdecl

/-- **Witness for `step_union_copy_indirect_uninit_divergence`** (`MaybeUninit::uninit()`
semantics): in `bb2` of `lm24A2UnionBody`, `_4 = copy _1` on an uninitialized
indirect union `_1` (`lm24UninitAlloc4`, `InitMask.new (translateSizeBytes 4) false`)
reports `.fail .ub` in Anneal while `lean-miri` steps normally `(m', .ok true)`
and initializes `_4`'s fresh allocation with `InitMask.new (translateSizeBytes 4) false`. -/
theorem lm24_union_copy_indirect_uninit_divergence :
    stepMirFn lm24A2UnionBody (lm24A2InitAnneal 2) = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp_w : Miri.Interpreter.MemPlace AnnealProv) (id : Miri.Memory.AllocId)
      (la_w : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          lm24A2UninitIndirectMiri = (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[4]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      mp_w.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id ∧
      (id, la_w) ∈ m'.machine.memory.live.toList ∧
      la_w.allocation.initializationMask =
        Miri.Memory.InitMask.new (translateSizeBytes 4) false := by
  have hnodup : LiveAllocsNodup (witnessMachineOf lm24UninitAlloc4) :=
    List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  have hhw : MemoryHighWater (witnessMachineOf lm24UninitAlloc4).memory :=
    ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hu_mls : ∀ tf, lm24A2UninitIndirectMiri.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect lm24BaseMemPlace), c⟩ := by
    intro tf htf
    have h : lm24A2UninitIndirectFrame = tf := by simpa [lm24A2UninitIndirectMiri] using htf
    subst h; exact ⟨none, rfl⟩
  have hw_imm : ∀ tf, lm24A2UninitIndirectMiri.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 4 := by
    intro tf htf
    have h : lm24A2UninitIndirectFrame = tf := by simpa [lm24A2UninitIndirectMiri] using htf
    subst h
    intro mls hmls mp hv
    simp [lm24A2UninitIndirectFrame] at hmls; subst hmls; cases hv
  exact step_union_copy_indirect_uninit_divergence lm24A2_uninit_indirect_stateRel.toLM2_4
    hnodup hhw.canReserveAllocId lm24A2_phase (w := 4) (u := 1) (bb := _) rfl rfl rfl rfl rfl
    lm24_wt_U (la_u := { kind := .stack, allocation := lm24UninitAlloc4 }) rfl hu_mls rfl
    (List.Mem.head _) rfl rfl rfl rfl rfl (by decide) rfl hw_imm

theorem lm24A2_bb3_a₁ : stepMirFn lm24A2UnionBody (lm24A2InitAnneal 3) =
    .step (lm24A2AnnealState 3 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) := rfl

/-- **Witness for `step_union_aggregate_smaller_overwrite_divergence`** (`I-11`
raw-byte retention across narrower union aggregate writes): in `bb3` of
`lm24A2UnionBody`, `_1 = U { 0: 0x01020304_u32 }` steps normally in both
machines, and overwriting `_1` with narrower `_1 = U { a: 0x77_u8 }` replaces `_1`
with `.init (.aggregate 0 [.scalar ⟨0x77, 1⟩])` in Anneal, while `lean-miri`
preserves `IsUnionPrefixMask 4 4`, writes `0x77` to byte `0`, and retains the
trailing high bytes `(unionAllocRaw A').extract 1 4 = #[0x03, 0x02, 0x01]`. -/
theorem lm24_union_agg_smaller_overwrite_divergence :
    ∃ (m₁ m₂ : AnnealStepState) (s₂ : MachineState) (msc : Miri.Memory.ScalarInt)
      (allocId : Miri.Memory.AllocId)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          (lm24A2InitMiri 3) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody
        (lm24A2AnnealState 3 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn lm24A2UnionBody
        (lm24A2AnnealState 3 1 [.uninit, lm24UU32Slot, .uninit, .uninit, .uninit]) = .step s₂ ∧
      get? s₂.frame.locals 1 = some (.init (.aggregate 0 [.scalar ⟨0x77, 1⟩, .unit])) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₁ =
        (m₂, .ok true) ∧
      ScalarRel ⟨0x77, 1⟩ msc ∧
      (∃ kind, (allocId, ⟨kind, A'⟩) ∈ m₂.machine.memory.live.toList) ∧
      IsUnionPrefixMask 4 4 A'.initializationMask ∧
      A'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) false =
          .ok (.fromScalarInt msc) ∧
      (unionAllocRaw A').extract 1 4 = #[0x03, 0x02, 0x01] := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24A2_init_stateRel 3).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24A2_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24A2_init_frame_imm 3 1) lm24_isPrim_u32
    (fun tf _ => lm24A2_constU32_wt 0x01020304 (by rw [scalarModulus_eq_two_pow]; decide) tf)
    (by decide) (hdecls_adt := lm24A2_decls_adt)
  obtain ⟨sc₁, mp₁, m₁, tf₁, hstep₁, hop₁, hst₁, _, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    _, _, _, _, _⟩ := hpost₁ _ lm24A2_bb3_a₁
  have hsc₁ : sc₁ = ⟨0x01020304, 4⟩ := by
    have h : evalOperand (lm24A2InitAnneal 3).frame.locals (.constant (lm24ConstU32 0x01020304)) .nil
        (lm24A2InitAnneal 3).memory.globals lm24A2UnionBody.layouts .nil =
        .ok (.scalar ⟨0x01020304, 4⟩) (lm24A2InitAnneal 3).frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  have hu1_mls₁ : ∀ tf, m₁.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp₁), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have hmem₁_copy := hmem₁
  cases hmem₁ with
  | mk allocId tag _ la_old _ hprov _ _ hlive_old _ _ _ _ hlen_old _ _ _ _ _ _ _ _ _ _ hraw_old =>
  obtain ⟨⟨s₂, hs₂, hslot₂⟩, m₂, msc, A', hstep₂, hrel, hlive', hmask, hread, hhigh⟩ :=
    step_union_aggregate_smaller_overwrite_divergence hst₁ hnodup₁ lm24A2_phase (u := 1)
      (bb := _) rfl rfl rfl lm24_wt_U rfl (by decide) rfl rfl (f_old := 1) rfl hu1_mls₁ hprov
      hlive_old hmem₁_copy lm24_isPrim_u8 (fun tf _ => lm24A2_constU8_wt 0x77 (by decide) tf)
      (by decide) (sc := ⟨0x77, 1⟩) rfl (hdecls_adt := lm24A2_decls_adt)
  have hextr_eq : (unionAllocRaw la_old.allocation).extract 0 4 = unionAllocRaw la_old.allocation := by
    have hsz : (unionAllocRaw la_old.allocation).size = 4 := hlen_old
    rw [← hsz, Array.extract_size]
  have hhigh_bytes : (unionAllocRaw A').extract 1 4 = #[0x03, 0x02, 0x01] := by
    dsimp only at hhigh
    rw [hhigh, ← hextr_eq, hraw_old]
    decide
  exact ⟨m₁, m₂, s₂, msc, allocId, A', hstep₁, hst₁, hs₂, hslot₂, hstep₂, hrel,
    ⟨la_old.kind, hlive'⟩, hmask, hread, hhigh_bytes⟩

theorem lm24A2_bb4_a₁ : stepMirFn lm24A2UnionBody (lm24A2InitAnneal 4) =
    .step (lm24A2AnnealState 4 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl

theorem lm24A2_bb5_a₁ : stepMirFn lm24A2UnionBody (lm24A2InitAnneal 5) =
    .step (lm24A2AnnealState 5 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl

/-- **Witness for `step_repeat_union_field_simulation`**:
1. In `bb4` of `lm24A2UnionBody`, `_1 = U { a: 5 }` followed by
   `_3 = [copy (_1.0: u8); 3]` steps normally in both machines to related states
   with `_3 = [5_u8, 5_u8, 5_u8]` (`MemPlaceRel`);
2. In `bb5` of `lm24A2UnionBody`, `_1 = U { a: 5 }` followed by
   `_3 = [copy (_1.1: u32); 3]` (repeating the wider uninitialized union field)
   reports undefined behavior in both machines (`StepRelLM2_4.ub`). -/
theorem lm24_repeat_union_field_steps :
    ∃ (m₁ m₂ m₁_ub : AnnealStepState) (s₂ : MachineState)
      (mp_arr : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          (lm24A2InitMiri 4) = (m₁, .ok true) ∧
      stepMirFn lm24A2UnionBody
        (lm24A2AnnealState 4 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) = .step s₂ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₁ =
        (m₂, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody s₂ m₂ ∧
      get? s₂.frame.locals 3 =
        some (.init (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩])) ∧
      MemPlaceRel m₂.machine lm24U8Arr3Ty lm24Layouts
        (some (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩])) mp_arr ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
          (lm24A2InitMiri 5) = (m₁_ub, .ok true) ∧
      stepMirFn lm24A2UnionBody
        (lm24A2AnnealState 5 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) = .fail .ub ∧
      StepRelLM2_4 lm24A2UnionBody m₁_ub
        (stepMirFn lm24A2UnionBody
          (lm24A2AnnealState 5 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₁_ub) := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24A2_init_stateRel 4).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24A2_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24A2_init_frame_imm 4 1) lm24_isPrim_u8
    (fun tf _ => lm24A2_constU8_wt 5 (by decide) tf) (by decide)
    (hdecls_adt := lm24A2_decls_adt)
  obtain ⟨sc₁, mp₁, m₁, tf₁, hstep₁, hop₁, hst₁, _, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    himm₁, _, _, _, hhw₁⟩ := hpost₁ _ lm24A2_bb4_a₁
  have hsc₁ : sc₁ = ⟨5, 1⟩ := by
    have h : evalOperand (lm24A2InitAnneal 4).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24A2InitAnneal 4).memory.globals lm24A2UnionBody.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24A2InitAnneal 4).frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  obtain ⟨hhw₁', _⟩ := hhw₁ rfl MemoryHighWater.empty
    (show AnnealMachine.empty.memory.nextAllocId.toNat + 1 < 2 ^ 64 by decide)
  have hu1_mls₁ : ∀ tf, m₁.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp₁), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have harr_imm₁ : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact himm₁ (lm24A2InitMiriFrame 4) rfl 3 (by decide) (lm24A2_init_imm 4 3)
  obtain ⟨s₂, m₂, mp_arr, _, hs₂, hstep₂, hst₂, hslot_arr₂, _, _, hmp_arr, _, _, _⟩ :=
    (step_repeat_union_field_simulation hst₁ hnodup₁ lm24A2_phase (arrIdx := 3) (u := 1)
      (j := 0) (fty := lm24U8Ty) (isMove := false) (count := 3) (bb := _)
      rfl rfl rfl rfl lm24_wf_u8Arr3 lm24_isPrim_u8 (w := 1) (Or.inl rfl) rfl (f := 0) lm24_wt_U rfl
      (by decide) (by decide) rfl hu1_mls₁ hmem₁ rfl (fun h => nomatch h) (fun h => nomatch h)).2.2
      rfl rfl rfl harr_imm₁ hhw₁'.canReserveAllocId
  -- `bb5`: wider uninitialized union field `Repeat` -> UB in both
  obtain ⟨_, hpost_ub⟩ := step_union_aggregate_simulation (lm24A2_init_stateRel 5).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24A2_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24A2_init_frame_imm 5 1) lm24_isPrim_u8
    (fun tf _ => lm24A2_constU8_wt 5 (by decide) tf) (by decide)
    (hdecls_adt := lm24A2_decls_adt)
  obtain ⟨sc_ub, mp_ub, m₁_ub, tf_ub, hstep_ub₁, hop_ub, hst_ub, _, hframes_ub, ⟨c_ub, hmls_ub⟩,
    hmem_ub, hnodup_ub, _, _, _, _, _⟩ := hpost_ub _ lm24A2_bb5_a₁
  have hsc_ub : sc_ub = ⟨5, 1⟩ := by
    have h : evalOperand (lm24A2InitAnneal 5).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24A2InitAnneal 5).memory.globals lm24A2UnionBody.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24A2InitAnneal 5).frame.locals := rfl
    rw [h] at hop_ub; injection hop_ub with h1 _; injection h1 with h1; exact h1.symm
  subst hsc_ub
  have hu1_mls_ub : ∀ tf, m₁_ub.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp_ub), c⟩ := by
    intro tf htf; rw [hframes_ub] at htf
    have h : tf_ub = tf := by simpa using htf
    subst h; exact ⟨c_ub, hmls_ub⟩
  have hrel_ub :=
    (step_repeat_union_field_simulation hst_ub hnodup_ub lm24A2_phase (arrIdx := 3) (u := 1)
      (j := 1) (fty := lm24U32Ty) (isMove := false) (count := 3) (bb := _)
      rfl rfl rfl rfl lm24_wf_u8Arr3 lm24_isPrim_u32 (w := 4)
      (Or.inr (Or.inr (Or.inl rfl))) rfl (f := 0) lm24_wt_U rfl (by decide) (by decide) rfl hu1_mls_ub
      hmem_ub rfl (fun h => nomatch h) (fun h => nomatch h)).1 (by decide) (by decide) (by decide)
  exact ⟨m₁, m₂, m₁_ub, s₂, mp_arr, hstep₁, hs₂, hstep₂, hst₂, hslot_arr₂, hmp_arr,
    hstep_ub₁, rfl, hrel_ub⟩

/-! ## 11. Nested `Subslice`, In-Place `Subslice` Overwrite, and Projected `Subslice` Element Writes -/

/-- **Witness for `evalProjection_nested_subslice_simulation`**: on `[0x0102, 0x0304, 0x0506]`,
composing `[.subslice 0 3 false, .subslice 1 2 false]` extracts `[0x0304]` in
Anneal and advances `witnessMemPlace` by `2` bytes in `lean-miri`, while
composing `[.subslice 0 3 false, .subslice 2 2 true]` (`fromEnd = true`,
`2 + 2 > 3`) reports undefined behavior in both machines. -/
theorem lm24_nested_subslice_witness :
    let cx := annealSubsliceProjectionCx (lm21InitMiriFrame 0) emptyLayoutTable
      (witnessMachineOf lm21ArrAlloc)
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty emptyLayoutTable⟩
    readProjectedValue [] (.aggregate 0 lm21ArrElems)
      [.subslice 0 3 false, .subslice 1 2 false] =
        .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩]) ∧
    (∃ op, annealProjectList cx base [.Subslice 0 3 false, .Subslice 1 2 false] = .ok op ∧
      ∃ mp, op.op = .indirect mp ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (witnessMemPlace.ptr.offset.bytes + 2)) ∧
    readProjectedValue [] (.aggregate 0 lm21ArrElems)
      [.subslice 0 3 false, .subslice 2 2 true] = .ub ∧
    ∃ msg, (annealProjectList cx base
      [.Subslice 0 3 false, .Subslice 2 2 true]).mapError annealLiftProjectionError =
        .error (.undefinedBehavior msg) := by
  intro cx base
  have h1 := evalProjection_nested_subslice_simulation (lm21InitMiriFrame 0) []
    lm21_wf_u16Arr3 lm21_nodup_arr lm21_memPlaceRel (by decide)
    (f1 := 0) (t1 := 3) (fe1 := false) (Or.inl ⟨rfl, by decide, by decide⟩) 1 2 false
  obtain ⟨hr1, hp1, _⟩ := h1.1 (Or.inl ⟨rfl, by decide, by decide⟩)
  have h2 := evalProjection_nested_subslice_simulation (lm21InitMiriFrame 0) []
    lm21_wf_u16Arr3 lm21_nodup_arr lm21_memPlaceRel (by decide)
    (f1 := 0) (t1 := 3) (fe1 := false) (Or.inl ⟨rfl, by decide, by decide⟩) 2 2 true
  obtain ⟨hub, msg, hub_m⟩ := h2.2 rfl (by decide) (by decide)
  exact ⟨hr1, ⟨_, hp1, _, rfl, rfl⟩, hub, msg, hub_m⟩

def lm24ConstU16 (n : Nat) : ConstOperand := { ty := lm21U16Ty, val := .scalar (.int ⟨n, 2⟩) }

/-- Locals: `_0: u16`, `_1: [u16; 3]`, `_2: [u16; 2]`, `_3: [u16; 0]`.
- `stmt 0`: `_2 = move _1[1..3]` (initializes `_2` to `[0x0304, 0x0506]`)
- `stmt 1`: `_2 = copy _1[0..2]` (overwrites already-allocated `_2` in place
  with `[0x0102, 0x0304]`, and reports UB on `.dead` `_2`)
- `stmt 2`: `_1[1..3][0 of 2] = const 0x0099_u16` (projected subslice element
  write: `.unsupported` in Anneal, in-place write to `[0x0102, 0x0099, 0x0506]`
  in `lean-miri`; UB in both on uninitialized `_1`) -/
def lm24A2SubsliceBody : CapturedMir where
  defPath := "lm_2_4_witness::a2_subslice"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm21U16Decl, lm21U16Arr3Decl, lm24U16Arr2Decl, lm21U16Arr0Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.use (subsliceReadOperand true 1 1 3 false))),
        mkStmt (.assign (local_ 2) (.use (subsliceReadOperand false 1 0 2 false))),
        mkStmt (.assign ⟨1, [.subslice 1 3 false, .constantIndex 0 2 false]⟩
          (.use (.constant (lm24ConstU16 0x0099))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm24A2_subslice_phase : ∀ p, lm24A2SubsliceBody.phase ≠ .other p := by
  intro p h; cases h

def lm24Arr2Alloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[0x04, 0x03, 0x06, 0x05]
      (translateAlignBytes 2) .Mut)
    (by decide)).withExtra none

def lm24Arr2Elems : List Value := [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩]

def lm24SecondAllocId : Miri.Memory.AllocId := ⟨2, by decide⟩
def lm24SecondBaseAddr : UInt64 := 0x2000

def lm24Arr2MemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes lm24SecondBaseAddr,
            some (.concrete lm24SecondAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm24TwoArrMachine : AnnealMachine :=
  { memory :=
      { (Miri.Memory.MemoryState.empty : AnnealMemory) with
        nextAllocId := 3
        live := #[(witnessAllocId, { kind := .stack, allocation := lm21ArrAlloc }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24Arr2Alloc })] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[{ allocId := witnessAllocId, address := witnessBaseAddr },
                      { allocId := lm24SecondAllocId, address := lm24SecondBaseAddr }]
        intToPtrMap := #[{ address := witnessBaseAddr, allocId := witnessAllocId },
                         { address := lm24SecondBaseAddr, allocId := lm24SecondAllocId }] }
    borrowTracker := none }

private theorem lm24_arr2_sliceRel :
    ArraySliceRel (.uint .u16) 2 emptyLayoutTable lm24Arr2Elems Miri.ABI.Size.ZERO
      lm24Arr2Alloc := by
  refine ⟨rfl, by decide, rfl, rfl, rfl, by decide, ?_⟩
  intro k elemVal hk
  match k with
  | 0 =>
    have he : elemVal = .scalar ⟨0x0304, 2⟩ := by simpa [lm24Arr2Elems, get?] using hk.symm
    subst he
    exact ⟨⟨0x0304, 2⟩, extractExceptOk (translateScalarInt ⟨0x0304, 2⟩) (by decide),
      rfl, rfl, (fun h => nomatch h), (fun h => nomatch h),
      ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩,
      by with_unfolding_all rfl⟩
  | 1 =>
    have he : elemVal = .scalar ⟨0x0506, 2⟩ := by simpa [lm24Arr2Elems, get?] using hk.symm
    subst he
    exact ⟨⟨0x0506, 2⟩, extractExceptOk (translateScalarInt ⟨0x0506, 2⟩) (by decide),
      rfl, rfl, (fun h => nomatch h), (fun h => nomatch h),
      ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩,
      by with_unfolding_all rfl⟩
  | _ + 2 =>
    simp [lm24Arr2Elems, get?] at hk

private theorem lm24_twoArr_mp1 :
    MemPlaceRel lm24TwoArrMachine lm21U16Arr3Ty emptyLayoutTable
      (some (.aggregate 0 lm21ArrElems)) witnessMemPlace :=
  MemPlaceRel.mk witnessAllocId witnessTag witnessBaseAddr witnessRelOffset
    { kind := .stack, allocation := lm21ArrAlloc } rfl rfl rfl (List.Mem.head _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    nofun (fun _ _ _ => by decide) (fun _ h => nomatch h)
    (fun ek cnt' es' hk hopt => by
      injection hk with hek hcnt'; subst hek hcnt'
      injection hopt with hagg; injection hagg with _ hes'; subst hes'
      exact ⟨rfl, rfl, rfl, lm21_arraySliceRel⟩)

private theorem lm24_twoArr_mp2 :
    MemPlaceRel lm24TwoArrMachine lm24U16Arr2Ty emptyLayoutTable
      (some (.aggregate 0 lm24Arr2Elems)) lm24Arr2MemPlace :=
  MemPlaceRel.mk lm24SecondAllocId witnessTag lm24SecondBaseAddr Miri.ABI.Size.ZERO
    { kind := .stack, allocation := lm24Arr2Alloc } rfl rfl rfl (List.Mem.tail _ (List.Mem.head _))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    nofun (fun _ _ _ => by decide) (fun _ h => nomatch h)
    (fun ek cnt' es' hk hopt => by
      injection hk with hek hcnt'; subst hek hcnt'
      injection hopt with hagg; injection hagg with _ hes'; subst hes'
      exact ⟨rfl, rfl, rfl, lm24_arr2_sliceRel⟩)

def lm24A2SubsliceAnneal (k : Nat) (arrSlot dstSlot : LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := k, locals := [.uninit, arrSlot, dstSlot, .uninit] }
    memory := (initMachineState lm24A2SubsliceBody []).memory }

def lm24A2SubsliceFrame (k : Nat) (arrOp : Miri.Interpreter.Operand AnnealProv)
    (dstState : Miri.Interpreter.LocalValue AnnealProv) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { (lm24SubsliceMiriFrame k arrOp) with
    body := translateBody lm24A2SubsliceBody
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live arrOp, layout := none },
      { value := dstState, layout := none },
      { value := .live (.immediate .uninit), layout := none }] }

def lm24A2TwoArrMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24A2SubsliceFrame k (.indirect witnessMemPlace) (.live (.indirect lm24Arr2MemPlace))]⟩
    machine := lm24TwoArrMachine }

def lm24A2DeadDstMiri : AnnealStepState :=
  { stack := ⟨#[lm24A2SubsliceFrame 1 (.indirect witnessMemPlace) .dead]⟩
    machine := witnessMachineOf lm21ArrAlloc }

def lm24A2SubsliceMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24A2SubsliceFrame k (.indirect witnessMemPlace) (.live (.immediate .uninit))]⟩
    machine := witnessMachineOf lm21ArrAlloc }

def lm24A2SubsliceUninitMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24A2SubsliceFrame k (.immediate .uninit) (.live (.immediate .uninit))]⟩
    machine := AnnealMachine.empty }

private theorem lm24A2_twoArr_stateRel (k : Nat) :
    StateRel lm24A2SubsliceBody
      (lm24A2SubsliceAnneal k (.init (.aggregate 0 lm21ArrElems))
        (.init (.aggregate 0 lm24Arr2Elems)))
      (lm24A2TwoArrMiri k) := by
  refine StateRel.mk
    (lm24A2SubsliceFrame k (.indirect witnessMemPlace) (.live (.indirect lm24Arr2MemPlace)))
    rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j mp_i mp_j _ _ hneq hi hj
      match i, j with
      | 0, _ | 3, _ | _ + 4, _ => simp [lm24A2SubsliceFrame] at hi
      | 1, 0 | 1, 3 | 1, _ + 4 | 2, 0 | 2, 3 | 2, _ + 4 => simp [lm24A2SubsliceFrame] at hj
      | 1, 1 | 2, 2 => exact absurd rfl hneq
      | 1, 2 =>
        have h1 : mp_i = witnessMemPlace := by simp [lm24A2SubsliceFrame] at hi; exact hi.1.symm
        have h2 : mp_j = lm24Arr2MemPlace := by simp [lm24A2SubsliceFrame] at hj; exact hj.1.symm
        subst h1 h2; decide
      | 2, 1 =>
        have h1 : mp_i = lm24Arr2MemPlace := by simp [lm24A2SubsliceFrame] at hi; exact hi.1.symm
        have h2 : mp_j = witnessMemPlace := by simp [lm24A2SubsliceFrame] at hj; exact hj.1.symm
        subst h1 h2; decide)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 3 =>
    have hs : slot = .uninit := by simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm24A2SubsliceBody, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun lm24_twoArr_mp1
  | 2 =>
    have hd : decl = lm24U16Arr2Decl := by simpa [lm24A2SubsliceBody, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm24Arr2Elems) := by
      simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect lm24Arr2MemPlace), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ lm24Arr2MemPlace none (fun _ h => nomatch h) nofun lm24_twoArr_mp2
  | _ + 4 =>
    simp [lm24A2SubsliceBody, get?] at hdecl

private theorem lm24A2_deadDst_stateRel :
    StateRel lm24A2SubsliceBody
      (lm24A2SubsliceAnneal 1 (.init (.aggregate 0 lm21ArrElems)) .dead)
      lm24A2DeadDstMiri := by
  refine StateRel.mk (lm24A2SubsliceFrame 1 (.indirect witnessMemPlace) .dead) rfl rfl
    ⟨translateTy lm21U16Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ hneq hi hj
      match i, j with
      | 0, _ | 2, _ | 3, _ | _ + 4, _ => simp [lm24A2SubsliceFrame] at hi
      | 1, 0 | 1, 2 | 1, 3 | 1, _ + 4 => simp [lm24A2SubsliceFrame] at hj
      | 1, 1 => exact absurd rfl hneq)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 3 =>
    have hs : slot = .uninit := by simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm24A2SubsliceBody, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun lm21_memPlaceRel
  | 2 =>
    have hs : slot = .dead := by simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hs hm
    exact .dead none (fun _ h => nomatch h)
  | _ + 4 =>
    simp [lm24A2SubsliceBody, get?] at hdecl

private theorem lm24A2_subslice_stateRel (k : Nat) :
    StateRel lm24A2SubsliceBody
      (lm24A2SubsliceAnneal k (.init (.aggregate 0 lm21ArrElems)) .uninit)
      (lm24A2SubsliceMiri k) := by
  refine StateRel.mk
    (lm24A2SubsliceFrame k (.indirect witnessMemPlace) (.live (.immediate .uninit)))
    rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ hneq hi hj
      match i, j with
      | 0, _ | 2, _ | 3, _ | _ + 4, _ => simp [lm24A2SubsliceFrame] at hi
      | 1, 0 | 1, 2 | 1, 3 | 1, _ + 4 => simp [lm24A2SubsliceFrame] at hj
      | 1, 1 => exact absurd rfl hneq)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm24A2SubsliceBody, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun lm21_memPlaceRel
  | _ + 4 =>
    simp [lm24A2SubsliceBody, get?] at hdecl

private theorem lm24A2_subslice_uninit_stateRel (k : Nat) :
    StateRel lm24A2SubsliceBody
      (lm24A2SubsliceAnneal k .uninit .uninit)
      (lm24A2SubsliceUninitMiri k) := by
  refine StateRel.mk
    (lm24A2SubsliceFrame k (.immediate .uninit) (.live (.immediate .uninit)))
    rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => simp [lm24A2SubsliceFrame] at hi)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm24A2SubsliceAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm24A2SubsliceFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm24A2SubsliceBody, get?] at hdecl

/-- **Witness for `step_subslice_assign_overwrite_simulation` and
`step_subslice_elem_write_simulation`**:
1. In-place overwrite `_2 = copy _1[0..2]` on already memory-backed `_2`
   (`lm24A2TwoArrMiri 1`) steps in lockstep (`StateRelLM2_4`) to
   `_2 = [0x0102, 0x0304]` at the same `lm24Arr2MemPlace`;
2. Writing `_2 = copy _1[0..2]` into `.dead` `_2` (`lm24A2DeadDstMiri`) reports
   undefined behavior in both machines (`StepRelLM2_4.ub`);
3. Projected subslice element write `_1[1..3][0 of 2] = const 0x0099_u16` on
   initialized `_1` steps both machines in lockstep (`StateRelLM2_4`), updating
   `_1` in place to `[0x0102, 0x0099, 0x0506]`, and on uninitialized `_1`
   reports undefined behavior in both machines (`StepRelLM2_4.ub`). -/
theorem lm24_subslice_overwrite_and_elem_write_witness :
    ∃ (s_ovw s_elem : MachineState) (m_ovw m_elem : AnnealStepState)
      (mp₁' : Miri.Interpreter.MemPlace AnnealProv),
      stepMirFn lm24A2SubsliceBody
        (lm24A2SubsliceAnneal 1 (.init (.aggregate 0 lm21ArrElems))
          (.init (.aggregate 0 lm24Arr2Elems))) = .step s_ovw ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2SubsliceBody.localDecls lm24A2SubsliceBody.layouts) ()
          (lm24A2TwoArrMiri 1) = (m_ovw, .ok true) ∧
      StateRelLM2_4 lm24A2SubsliceBody s_ovw m_ovw ∧
      get? s_ovw.frame.locals 2 =
        some (.init (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩])) ∧
      MemPlaceRel m_ovw.machine lm24U16Arr2Ty emptyLayoutTable
        (some (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩])) lm24Arr2MemPlace ∧
      StepRelLM2_4 lm24A2SubsliceBody lm24A2DeadDstMiri
        (stepMirFn lm24A2SubsliceBody
          (lm24A2SubsliceAnneal 1 (.init (.aggregate 0 lm21ArrElems)) .dead))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2SubsliceBody.localDecls lm24A2SubsliceBody.layouts) ()
          lm24A2DeadDstMiri) ∧
      stepMirFn lm24A2SubsliceBody
        (lm24A2SubsliceAnneal 2 (.init (.aggregate 0 lm21ArrElems)) .uninit) = .step s_elem ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2SubsliceBody.localDecls lm24A2SubsliceBody.layouts) ()
          (lm24A2SubsliceMiri 2) = (m_elem, .ok true) ∧
      StateRelLM2_4 lm24A2SubsliceBody s_elem m_elem ∧
      get? s_elem.frame.locals 1 =
        some (.init (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0099, 2⟩, .scalar ⟨0x0506, 2⟩])) ∧
      MemPlaceRel m_elem.machine lm21U16Arr3Ty emptyLayoutTable
        (some (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0099, 2⟩, .scalar ⟨0x0506, 2⟩]))
        mp₁' ∧
      StepRelLM2_4 lm24A2SubsliceBody (lm24A2SubsliceUninitMiri 2)
        (stepMirFn lm24A2SubsliceBody (lm24A2SubsliceAnneal 2 .uninit .uninit))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 lm24A2SubsliceBody.localDecls lm24A2SubsliceBody.layouts) ()
          (lm24A2SubsliceUninitMiri 2)) := by
  have hnodup_two : LiveAllocsNodup lm24TwoArrMachine :=
    List.Pairwise.cons
      (fun p hp => by
        cases hp with
        | head _ => decide
        | tail _ h => nomatch h)
      (List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil)
  have hd_mls : ∀ tf, (lm24A2TwoArrMiri 1).stack.frames = #[tf] →
      ∃ c, tf.locals[2]? = some ⟨.live (.indirect lm24Arr2MemPlace), c⟩ := by
    intro tf htf
    have h : lm24A2SubsliceFrame 1 (.indirect witnessMemPlace)
        (.live (.indirect lm24Arr2MemPlace)) = tf := by simpa [lm24A2TwoArrMiri] using htf
    subst h; exact ⟨none, rfl⟩
  obtain ⟨s_ovw, m_ovw, hs_ovw, hm_ovw, hst_ovw, hd_ovw, _, hmp_ovw, _, _⟩ :=
    (step_subslice_assign_overwrite_simulation (lm24A2_twoArr_stateRel 1).toLM2_4 hnodup_two
      lm24A2_subslice_phase (d := 2) (arrIdx := 1) (isMove := false) (fromIdx := 0) (toIdx := 2)
      (fromEnd := false) (bb := _) rfl rfl rfl rfl lm21_wf_u16Arr3 lm24_wf_u16Arr2 rfl
      (Or.inl ⟨rfl, by decide, by decide⟩)).2
      lm24Arr2Elems lm24Arr2MemPlace lm24SecondAllocId witnessTag lm24SecondBaseAddr
      { kind := .stack, allocation := lm24Arr2Alloc } (by decide) rfl hd_mls rfl
      (List.Mem.tail _ (List.Mem.head _)) (by decide) rfl rfl (by decide) lm24_twoArr_mp2
  have hdead_ub :=
    (step_subslice_assign_overwrite_simulation lm24A2_deadDst_stateRel.toLM2_4 lm21_nodup_arr
      lm24A2_subslice_phase (d := 2) (arrIdx := 1) (isMove := false) (fromIdx := 0) (toIdx := 2)
      (fromEnd := false) (bb := _) rfl rfl rfl rfl lm21_wf_u16Arr3 lm24_wf_u16Arr2 rfl
      (Or.inl ⟨rfl, by decide, by decide⟩)).1 rfl
  have hovf_elem : ∀ mp,
      (∃ tf c_l, (lm24A2SubsliceMiri 2).stack.frames = #[tf] ∧
        tf.locals[1]? = some ⟨.live (.indirect mp), c_l⟩) →
      mp.ptr.offset.bytes.toNat +
        (translateTy lm21U16Arr3Decl.ty emptyLayoutTable).layout.size.bytes.toNat < 2 ^ 64 := by
    rintro mp ⟨tf, c_l, htf, hmls⟩
    have h : lm24A2SubsliceFrame 2 (.indirect witnessMemPlace) (.live (.immediate .uninit)) = tf := by
      simpa [lm24A2SubsliceMiri] using htf
    subst h
    have hmp_eq : mp = witnessMemPlace := by simp [lm24A2SubsliceFrame] at hmls; exact hmls.1.symm
    subst hmp_eq; decide
  obtain ⟨s_elem, m_elem, mp₁', hs_elem, hm_elem, hst_elem, hslot_elem, hmp₁', _, _⟩ :=
    (step_subslice_elem_write_simulation (lm24A2_subslice_stateRel 2).toLM2_4 lm21_nodup_arr
      lm24A2_subslice_phase (arrIdx := 1) (fromIdx := 1) (toIdx := 3) (off := 0) (minLen := 2)
      (fromEnd := false) (c := lm24ConstU16 0x0099) (bb := _) rfl rfl rfl lm21_wf_u16Arr3
      (sc := ⟨0x0099, 2⟩) rfl rfl (Or.inr (Or.inl rfl)) (by rw [scalarModulus_eq_two_pow]; decide)
      rfl (fun h => nomatch h) (fun h => nomatch h)).2
      lm21ArrElems rfl (Or.inl ⟨rfl, by decide, by decide⟩) (by decide) (by decide) hovf_elem
  have huninit_elem_ub :=
    (step_subslice_elem_write_simulation (lm24A2_subslice_uninit_stateRel 2).toLM2_4
      lm21_nodup_empty lm24A2_subslice_phase (arrIdx := 1) (fromIdx := 1) (toIdx := 3) (off := 0)
      (minLen := 2) (fromEnd := false) (c := lm24ConstU16 0x0099) (bb := _) rfl rfl rfl
      lm21_wf_u16Arr3 (sc := ⟨0x0099, 2⟩) rfl rfl (Or.inr (Or.inl rfl))
      (by rw [scalarModulus_eq_two_pow]; decide) rfl (fun h => nomatch h) (fun h => nomatch h)).1
      (Or.inr ⟨rfl, Or.inl (by decide)⟩)
  exact ⟨s_ovw, s_elem, m_ovw, m_elem, mp₁', hs_ovw, hm_ovw, hst_ovw, hd_ovw, hmp_ovw, hdead_ub,
    hs_elem, hm_elem, hst_elem, hslot_elem, hmp₁', huninit_elem_ub⟩


theorem lm24A2_bb6_a₁ :
    stepMirFn lm24A2UnionBody (lm24A2InitAnneal 6) =
      .step (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl

theorem lm24A2_bb6_a₂ :
    stepMirFn lm24A2UnionBody
      (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) =
      .step (lm24A2AnnealState 6 2 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) := rfl

/-- **Witness for union self-move**: Concrete execution demonstrating `_1 = move _1` on a union local `_1`. -/
theorem lm24_union_self_move_steps :
    ∃ (m₁ m₂ : AnnealStepState),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () (lm24A2InitMiri 6) = (m₁, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) () m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 lm24A2UnionBody (lm24A2AnnealState 6 2 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₂ := by
  obtain ⟨_, hpost₁⟩ := step_union_aggregate_simulation (lm24A2_init_stateRel 6).toLM2_4
    lm24_nodup_empty lm24_canReserve_empty lm24A2_phase (u := 1) (bb := _) rfl rfl rfl lm24_wt_U
    rfl (by decide) rfl rfl rfl (lm24A2_init_frame_imm 6 1) lm24_isPrim_u8
    (fun tf _ => lm24A2_constU8_wt 5 (by decide) tf) (by decide)
    (hdecls_adt := lm24A2_decls_adt)
  obtain ⟨sc₁, mp₁, m₁, tf₁, hstep₁, hop₁, hst₁, hmem_sz₁, hframes₁, ⟨c₁, hmls₁⟩, hmem₁, hnodup₁,
    hcan_res₁, hptr₁, hbase₁, hlive₁, hprov₁⟩ := hpost₁ _ lm24A2_bb6_a₁
  have hsc₁ : sc₁ = ⟨5, 1⟩ := by
    have h : evalOperand (lm24A2InitAnneal 6).frame.locals (.constant (lm24ConstU8 5)) .nil
        (lm24A2InitAnneal 6).memory.globals lm24A2UnionBody.layouts .nil =
        .ok (.scalar ⟨5, 1⟩) (lm24A2InitAnneal 6).frame.locals := rfl
    rw [h] at hop₁; injection hop₁ with h1 _; injection h1 with h1; exact h1.symm
  subst hsc₁
  have hu1_mls₁ : ∀ tf, m₁.stack.frames = #[tf] →
      ∃ c, tf.locals[1]? = some ⟨.live (.indirect mp₁), c⟩ := by
    intro tf htf; rw [hframes₁] at htf
    have h : tf₁ = tf := by simpa using htf
    subst h; exact ⟨c₁, hmls₁⟩
  have hdecl_1 : get? lm24A2UnionBody.localDecls 1 = some (lm24Decl lm24UTy) := rfl
  have hmls_1_eq : tf₁.locals[1]'(by
      rcases hst₁ with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
      have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
      subst heq
      obtain ⟨_, mls_1, hlt_af_1, hlt, _, hmls_1', hmls_1_eq, hloc_1⟩ := hframe.lookup_local hdecl_1
      exact hlt) = ⟨.live (.indirect mp₁), c₁⟩ := by
    rcases hst₁ with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
    have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
    subst heq
    obtain ⟨_, mls_1, hlt_af_1, hlt_1', _, hmls_1', hmls_1_eq, hloc_1⟩ := hframe.lookup_local hdecl_1
    have h1 : ⟨.live (.indirect mp₁), c₁⟩ = mls_1 := by
      have hh := hmls₁; rw [hmls_1'] at hh; exact (Option.some.inj hh).symm
    rw [h1]; exact hmls_1_eq
  have hlt_1 : 1 < tf₁.locals.size := by
    rcases hst₁ with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
    have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
    subst heq
    obtain ⟨_, mls_1, hlt_af_1, hlt, _, hmls_1', hmls_1_eq, hloc_1⟩ := hframe.lookup_local hdecl_1
    exact hlt
  let layU := translateTy lm24UTy lm24A2UnionBody.layouts
  let topFrame₀ := cacheFrameLocalLayout tf₁ 1 hlt_1 layU
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv := ⟨.local 0 1 none tf₁.localsIdentity, layU⟩
  let m₀ : AnnealStepState := { m₁ with stack := ⟨#[topFrame₀]⟩ }
  have hevalPlace : annealEvalPlace lm24A2UnionBody.localDecls lm24A2UnionBody.layouts ⟨1, #[]⟩ m₁ = .ok destPlace m₀ := by
    rcases hst₁ with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
    obtain ⟨_, mls_1, hlt_af_1, hlt_1', _, hmls_1', hmls_1_eq, hloc_1⟩ := hframe.lookup_local hdecl_1
    have heq : tf₁ = topFrame := by
      rw [hframes] at hframes₁
      exact (Array.singleton_inj.mp hframes₁).symm
    subst heq
    exact annealEvalPlace_unprojected hframes₁ hlt_1' hdecl_1 (by rw [hmls_1_eq]; exact hloc_1.layout_eq)
  have hlt_1₀ : 1 < topFrame₀.locals.size := by dsimp [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_1
  have hmls_1₀ : topFrame₀.locals[1]'hlt_1₀ = ⟨.live (.indirect mp₁), some layU⟩ := by
    dsimp [topFrame₀, cacheFrameLocalLayout]
    simp only [Array.getElem_set_self, hmls_1_eq]
  let tf_u := cacheFrameLocalLayout topFrame₀ 1 hlt_1₀ layU
  have hlt_u_size : 1 < tf_u.locals.size := by dsimp [tf_u]; rw [cacheFrameLocalLayout_size]; exact hlt_1₀
  let m₀' := { m₀ with stack := ⟨#[deinitFrameLocal tf_u 1 hlt_u_size]⟩ }

  have hop : annealEvalOperand lm24A2UnionBody.localDecls lm24A2UnionBody.layouts (.Move ⟨1, #[]⟩) (some layU) m₀ =
      .ok ⟨.indirect mp₁, layU⟩ m₀' := by
    exact annealEvalOperand_move_live (m := m₀) (known := some layU) rfl hlt_1₀ hdecl_1 hmls_1₀
      (by intro l hl; exact Option.some.inj hl.symm)

  have hlt_w₁ : 1 < (deinitFrameLocal tf_u 1 hlt_u_size).locals.size := by
    dsimp [deinitFrameLocal]; rw [Array.size_set]; exact hlt_u_size

  have hc_w₁ : ((deinitFrameLocal tf_u 1 hlt_u_size).locals[1]'hlt_w₁).layout = some layU := by
    have h_rw : ((deinitFrameLocal tf_u 1 hlt_u_size).locals[1]'hlt_w₁) = { tf_u.locals[1]'hlt_u_size with value := .live (.immediate .uninit) } := by
      revert hlt_w₁; dsimp [deinitFrameLocal]; intro _; simp [Array.getElem_set_self]
    rw [h_rw]
    have hc : (tf_u.locals[1]'hlt_u_size).layout = some layU := by
      revert hlt_u_size; dsimp [tf_u, cacheFrameLocalLayout]; intro _; simp [Array.getElem_set_self]
    rw [hc]

  have hval_w₁ : ((deinitFrameLocal tf_u 1 hlt_u_size).locals[1]'hlt_w₁).value = .live (.immediate .uninit) := by
    have h_rw : ((deinitFrameLocal tf_u 1 hlt_u_size).locals[1]'hlt_w₁) = { tf_u.locals[1]'hlt_u_size with value := .live (.immediate .uninit) } := by
      revert hlt_w₁; dsimp [deinitFrameLocal]; intro _; simp [Array.getElem_set_self]
    rw [h_rw]

  have h_align : layU.layout.align.abi.pow2 ≤ 29 := by decide
  obtain ⟨alloc, htry, hbs_eq, hlen_eq, hnat_eq, hmut_eq, halign_eq, hprov_alloc_eq, hmask_alloc_eq⟩ := freshUnionAlloc_spec layU.layout.size layU.layout.align.abi h_align

  obtain ⟨hw₁, _⟩ := hprov₁ rfl MemoryHighWater.empty (by decide)
  have hcanRes : CanReserveAllocId m₀'.machine.memory := hw₁.canReserveAllocId
  obtain ⟨mem', id, hres⟩ := hcanRes

  cases hmem₁ with
  | mk allocId tag baseAddr la msc hprov_u hmis_u hmeta_u hlive_u hbase_u hptr_u hovf_u hsz_u
      hlen_u hmut_u hp_u hal_u hex_u hnat_u hk hmask_u hrel hprim hf0imm hraw_u =>

  have hlayW_sz : layU.layout.size = translateSizeBytes 4 := rfl
  have hlayW_toNat : layU.layout.size.bytes.toNat = 4 := by rfl

  have hbs : alloc.byteSize = translateSizeBytes 4 := hbs_eq
  have hmut : alloc.mutability = .Mut := hmut_eq
  have hprov_alloc : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new := hprov_alloc_eq
  have hmask_alloc : alloc.initializationMask = .new (translateSizeBytes 4) false := hmask_alloc_eq
  have hraw_alloc : unionAllocRaw alloc = Array.replicate 4 0 := tryNew_uninit_raw layU.layout.size layU.layout.align.abi alloc htry
  have h_alloc_align : alloc.align = layU.layout.align.abi := halign_eq
  have h_alloc_extra : alloc.extra = () := rfl
  have h_alloc_native : alloc.nativeBuffer = none := hnat_eq

  have hS : ValidScalarBytes 4 := Or.inr (Or.inr (Or.inl rfl))
  have hk_valid : ValidScalarBytes 1 := Or.inl rfl
  obtain ⟨A_w, hcopy_w, hA_sz, hA_len, hA_align, hA_mut, hA_prov, _, hA_mask_pred,
      hA_extra, hA_native, hA_raw⟩ :=
    union_copy_freshAlloc_spec (src := la.allocation)
      (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
      hS hk_valid hk hlen_u hsz_u hp_u hmask_u
      hraw_alloc hbs hmut hprov_alloc hmask_alloc

  have hcopy_w' : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layU.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () A_w := by
    rw [hlayW_sz]
    exact hcopy_w

  have hmemcopy := annealMemCopyOp_freshUnion (body := lm24A2UnionBody) (m := m₀') rfl hlt_w₁ hdecl_1 hc_w₁
    hval_w₁ rfl htry hres hnodup₁ hprov_u hlive_u hbase_u hptr_u hcopy_w'
    layU tf₁.localsIdentity

  have hlm24 : lm24Assign lm24A2UnionBody.localDecls lm24A2UnionBody.layouts ⟨1, #[]⟩
      (translateRvalue (.use (.move ⟨1, .nil⟩))) = true := by decide

  have huse : usesMemCopy ⟨.indirect mp₁, layU⟩ = true := rfl

  have hevalPlace' : (annealRvalueHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts).evalPlace ()
      ⟨1, #[]⟩ true m₁ = .ok destPlace m₀ := hevalPlace

  have hop' : (annealRvalueHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.move ⟨1, .nil⟩))
      (some ((annealRvalueHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp₁, layU⟩ m₀' := hop

  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
      (translateStmt ⟨.assign ⟨1, .nil⟩ (.use (.move ⟨1, .nil⟩)), ""⟩) m₁ =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp lm24A2UnionBody.localDecls lm24A2UnionBody.layouts ⟨.indirect mp₁, layU⟩ destPlace) m₀' := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace']
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop']
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]

  let mp_w := stackAllocPlace id
  let mach₃ := stackAllocMachine m₀'.machine mem' id A_w
  let tf₃ := setFrameLocalIndirect (deinitFrameLocal tf_u 1 hlt_u_size) 1 hlt_w₁ mp_w
  let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }

  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts) ()
      (translateStmt ⟨.assign ⟨1, .nil⟩ (.use (.move ⟨1, .nil⟩)), ""⟩) m₁ = (st₃, .ok ()) := by
    rw [hm_eval]
    unfold Miri.Interpreter.runRvalue
    have hmemcopy_eq : annealMemCopyOp lm24A2UnionBody.localDecls lm24A2UnionBody.layouts ⟨.indirect mp₁, layU⟩ destPlace m₀' = EStateM.Result.ok () st₃ := hmemcopy
    rw [hmemcopy_eq]

  have hloc_1 : tf₁.location = .mir ⟨(lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.blockIdx, (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.stmtIdx⟩ := by
    rcases hst₁ with ⟨tf, htf, _, _, hf, _⟩
    have heq : tf = tf₁ := by rw [htf] at hframes₁; exact (Array.singleton_inj.mp hframes₁)
    exact heq ▸ hf.location_eq

  have hloc₃ : tf₃.location = .mir ⟨(lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.blockIdx, (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.stmtIdx⟩ := hloc_1

  have hstep_m := miri_step_at_statement_ok (body := lm24A2UnionBody) (annealStepHooksLM2_4 lm24A2UnionBody.localDecls lm24A2UnionBody.layouts)
    hframes₁ (by
      rcases hst₁ with ⟨tf, htf, _, _, hf, _⟩
      have heq : tf₁ = tf := by rw [htf] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
      exact heq ▸ hf.body_eq) hloc_1 (bb := lm24A2UnionBody.basicBlocks[6]'(by decide)) rfl rfl hm_stmt rfl hloc₃

  obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m₀'.machine) A_w hres
  have hmem_w : UnionMemRel mach₃ (lm24Decl lm24UTy).ty lm24A2UnionBody.layouts 4 lm24U8Ty ⟨5, 1⟩ mp_w :=
    .mk id .one (annealStackBaseAddr id) ⟨.stack, A_w⟩ msc rfl rfl rfl
      (by simp [mach₃, stackAllocMachine])
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id (by decide))
      hA_sz hA_len hA_mut hA_prov
      (by rw [hA_align]; exact h_alloc_align) (by rw [hA_extra]; rfl) (by rw [hA_native]; exact h_alloc_native) hk hA_mask_pred hrel
      hprim hf0imm (by rw [hA_raw]; exact hraw_u)

  have hframe₀' : FrameRelLM2_4 lm24A2UnionBody m₀.machine (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame topFrame₀ := by
    rcases hst₁ with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, _⟩
    have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
    subst heq
    exact hframe.cache_local_layout hdecl_1 hlt_1

  have hframe_u : FrameRelLM2_4 lm24A2UnionBody m₀.machine
      (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame tf_u := by
    exact hframe₀'.cache_local_layout hdecl_1 hlt_1₀

  have hnew_uninit : UnionLocalRel m₀.machine (lm24Decl lm24UTy) lm24A2UnionBody.layouts .uninit
      { tf_u.locals[1]'hlt_u_size with value := .live (.immediate .uninit) } := by
    have hlay_u : (tf_u.locals[1]'hlt_u_size).layout = some layU := by
      revert hlt_u_size; dsimp [tf_u, cacheFrameLocalLayout]; intro _; simp [Array.getElem_set_self]
    exact .base .uninit _ (.immediate .uninit .uninit _
      (by rw [hlay_u]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩))

  have hframe₁ : FrameRelLM2_4 lm24A2UnionBody m₀.machine
      { (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame with
        locals := (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals.set 1 .uninit }
      (deinitFrameLocal tf_u 1 hlt_u_size) :=
    hframe_u.update_local hdecl_1 .uninit (.live (.immediate .uninit)) hnew_uninit

  have hnew_w : UnionLocalRel mach₃ (lm24Decl lm24UTy) lm24A2UnionBody.layouts lm24USlot
      { (deinitFrameLocal tf_u 1 hlt_u_size).locals[1]'hlt_w₁ with value := .live (.indirect mp_w) } := by
    have hlay_u : ((deinitFrameLocal tf_u 1 hlt_u_size).locals[1]'hlt_w₁).layout = some layU := hc_w₁
    exact .union 4 2 0 lm24U8Ty ⟨5, 1⟩ mp_w _
      (by intro l hl; rw [hlay_u] at hl; exact (Option.some.inj hl).symm)
      lm24_wt_U rfl (by decide) hmem_w

  have hframe₂ : FrameRelLM2_4 lm24A2UnionBody mach₃
      (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame
      tf₃ :=
    { body_eq := hframe_u.body_eq
      location_eq := hframe_u.location_eq
      af_locals_len := hframe_u.af_locals_len
      mf_locals_size := by
        show (tf₃.locals).size = _
        dsimp [tf₃, setFrameLocalIndirect]
        rw [Array.size_set]
        dsimp [deinitFrameLocal]
        rw [Array.size_set]
        exact hframe_u.mf_locals_size
      locals_rel := by
        intro i decl slot mls hdecl hslot hmls
        have hmls' : (tf₃.locals)[i]? = some mls := hmls
        dsimp [tf₃, setFrameLocalIndirect] at hmls'
        rw [Array.getElem?_set] at hmls'
        by_cases hiw : 1 = i
        · subst hiw
          simp only [↓reduceIte, Option.some.injEq] at hmls'
          subst hmls'
          rw [hdecl_1] at hdecl
          cases hdecl
          have hslot_1 : slot = lm24USlot := by
            have hh : get? (lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals 1 = some slot := hslot
            exact (Option.some.inj hh).symm
          subst hslot_1
          exact hnew_w
        · simp only [hiw, ↓reduceIte] at hmls'
          have hslot_old : get? ((lm24A2AnnealState 6 1 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.locals.set 1 .uninit) i = some slot := by
            rw [get?_eq_getElem?, List.getElem?_set]; simp only [hiw, ↓reduceIte]
            have hh := hslot; rw [get?_eq_getElem?] at hh; exact hh
          exact (hframe₁.locals_rel i decl slot mls hdecl hslot_old hmls').of_live_base hlive_b hbase_b }

  let tf_fin := { tf₃ with location := .mir ⟨(lm24A2AnnealState 6 2 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.blockIdx, (lm24A2AnnealState 6 2 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame.stmtIdx⟩ }

  have hframe_fin : FrameRelLM2_4 lm24A2UnionBody mach₃
      (lm24A2AnnealState 6 2 [.uninit, lm24USlot, .uninit, .uninit, .uninit]).frame tf_fin := by
    exact { hframe₂ with location_eq := rfl }

  have hdisj₀' : MemoryAllocDisjoint topFrame₀ := by
    rcases hst₁ with ⟨topFrame, hframes, _, _, hframe, hcal, _, hbor, hprot, hcaller, hdisj⟩
    have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
    subst heq
    exact hdisj.cache_layout hlt_1 _

  have hdisj_u : MemoryAllocDisjoint tf_u := hdisj₀'.cache_layout hlt_1₀ _

  have hdisj₁ : MemoryAllocDisjoint (deinitFrameLocal tf_u 1 hlt_u_size) := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp [deinitFrameLocal] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases h1i : 1 = i
    · subst h1i; simp at hi
    · simp only [h1i, ↓reduceIte] at hi
      by_cases h1j : 1 = j
      · subst h1j; simp at hj
      · simp only [h1j, ↓reduceIte] at hj
        exact hdisj_u i j mp_i mp_j lay_i lay_j hij hi hj

  have hdisj_fin : MemoryAllocDisjoint tf_fin := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_w : 1 = i
    · subst hi_w
      have hj_w : 1 ≠ j := hij
      simp only [hj_w, ↓reduceIte] at hj
      simp only [↓reduceIte] at hi
      obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
      injection hi with hi; injection hi with hv _; injection hv with hv; injection hv with hv
      subst hv; rw [ha]
      simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq, Option.some.injEq]
      exact fun h => hfreshne a la' hla h.symm
    · simp only [hi_w, ↓reduceIte] at hi
      by_cases hj_w : 1 = j
      · subst hj_w
        simp only [↓reduceIte] at hj
        obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
        injection hj with hj; injection hj with hv _; injection hv with hv; injection hv with hv
        subst hv; rw [ha]
        simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq, Option.some.injEq]
        exact hfreshne a la' hla
      · simp only [hj_w, ↓reduceIte] at hj
        exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj

  let m₂ := { st₃ with stack := ⟨#[tf_fin]⟩ }

  have hst₃ : StateRelLM2_4 lm24A2UnionBody (lm24A2AnnealState 6 2 [.uninit, lm24USlot, .uninit, .uninit, .uninit]) m₂ := by
    rcases hst₁ with ⟨topFrame, hframes, hret, hret_pl, hframe, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    have hret_fin : tf_fin.returnContinuation = .stop false := by
      have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
      subst heq
      exact hret
    have hret_pl_fin : ∃ retLay, tf_fin.returnPlace = .frameLocal 0 0 none retLay tf_fin.localsIdentity := by
      have heq : tf₁ = topFrame := by rw [hframes] at hframes₁; exact (Array.singleton_inj.mp hframes₁).symm
      subst heq
      exact hret_pl
    exact .mk tf_fin rfl hret_fin hret_pl_fin hframe_fin hcal hstack hbor hprot hcaller hdisj_fin

  exact ⟨m₁, m₂, hstep₁, hst₁, hstep_m, hst₃⟩

/-! ## 12. Padded Union with `[(); N]` ZST Array Arm (`kani#5176` / `kani#5159`)

This section proves the Stage-1 simulation theorems and concrete multi-step
witnesses for `#[repr(C)] union` types carrying a zero-sized `[(); N]` array
arm alongside scalar payload arms (`u8`, `u32`) and an uninhabited 0-byte arm
(`VoidZst`). -/

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.layout_eq
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts := by
  cases h with
  | ofUnionLocalRel _ _ hu => exact hu.layout_eq
  | uninitIndirect _ _ _ _ _ _ _ hc _ _ _ => exact hc
  | zstArrayIndirect _ _ _ _ hc _ _ _ _ => exact hc
  | zstUninit _ _ _ _ _ _ _ hc _ _ _ => exact hc
  | zstOverlay _ _ _ _ _ _ _ _ _ hc _ _ _ => exact hc

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.cache_layout
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls) :
    PaddedZstUnionLocalRel mach decl layouts slot
      { mls with layout := some (translateTy decl.ty layouts) } := by
  cases h with
  | ofUnionLocalRel _ _ hu => exact .ofUnionLocalRel _ _ hu.cache_layout
  | uninitIndirect S n N f_z zstFlIdx mp _ _ hwt hfields hmem =>
    exact .uninitIndirect S n N f_z zstFlIdx mp _
      (fun l hl => (Option.some.inj hl).symm) hwt hfields hmem
  | zstArrayIndirect N _ mp _ _ hk hsz hsl hmem =>
    exact .zstArrayIndirect N slot mp _
      (fun l hl => (Option.some.inj hl).symm) hk hsz hsl hmem
  | zstUninit S n N f_z zstFlIdx mp _ _ hwt hfields hmem =>
    exact .zstUninit S n N f_z zstFlIdx mp _
      (fun l hl => (Option.some.inj hl).symm) hwt hfields hmem
  | zstOverlay S n N f_z zstFlIdx f0Ty sc mp _ _ hwt hfields hmem =>
    exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp _
      (fun l hl => (Option.some.inj hl).symm) hwt hfields hmem

theorem _root_.LeanMiriSpec.Correspondence.ZstZeroMemRel.of_live_base
    {mach mach' : AnnealMachine} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : ZstZeroMemRel mach mp)
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a) :
    ZstZeroMemRel mach' mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hsz hlen hmut =>
    exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ hl)
      ((hbase allocId la hl).trans hb) hptr hsz hlen hmut

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.of_live_base
    {mach mach' : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls)
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a) :
    PaddedZstUnionLocalRel mach' decl layouts slot mls := by
  cases h with
  | ofUnionLocalRel _ _ hu =>
    exact .ofUnionLocalRel _ _ (hu.of_live_base hlive hbase)
  | uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields
      (by
        cases hmem with
        | mk allocId tag baseAddr la hprov hmis hmeta hlive_u hbase_u hptr hovf hsz
            hlen hmut hp hal hex hnat hmask =>
          exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ hlive_u)
            ((hbase allocId la hlive_u).trans hbase_u) hptr hovf hsz hlen hmut hp hal hex hnat hmask)
  | zstArrayIndirect N _ mp c hc hk hsz hsl hmem =>
    exact .zstArrayIndirect N slot mp c hc hk hsz hsl (hmem.of_live_base hlive hbase)
  | zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields
      (by
        cases hmem with
        | mk allocId tag baseAddr la hprov hmis hmeta hlive_u hbase_u hptr hovf hsz
            hlen hmut hp hal hex hnat hmask =>
          exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ hlive_u)
            ((hbase allocId la hlive_u).trans hbase_u) hptr hovf hsz hlen hmut hp hal hex hnat hmask)
  | zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem =>
    exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields
      (hmem.of_live_base hlive hbase)

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.allocLive
    {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | ofUnionLocalRel _ _ hu => exact hu.allocLive
  | uninitIndirect _ _ _ _ _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc hprov _ _ hl _ _ _ _ _ _ _ _ _ _ _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]
  | zstArrayIndirect _ _ mp _ _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc hprov _ _ hl _ _ _ _ _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]
  | zstUninit _ _ _ _ _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc hprov _ _ hl _ _ _ _ _ _ _ _ _ _ _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]
  | zstOverlay _ _ _ _ _ _ _ mp _ _ _ _ hmem =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    cases hmem with
    | mk allocId tag _ localAlloc _ hprov _ _ hl _ =>
      refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
      rw [Array.any_eq_true]
      refine ⟨i, by simpa using hi, ?_⟩
      simp only [Array.getElem_toList] at hget
      simp [hget]

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionUninitMemRel.of_filter_live
    {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : PaddedZstUnionUninitMemRel mach uTy layouts S mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    PaddedZstUnionUninitMemRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } }
      uTy layouts S mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
    have hne_id : (allocId != id) = true := by
      rw [bne_iff_ne]
      intro heq; subst heq
      exact hne (by simp [hprov, Miri.Memory.Provenance.getAllocId])
    have hl' : (allocId, la) ∈
        (mach.memory.live.filter (fun entry => entry.1 != id)).toList := by
      rw [Array.toList_filter, List.mem_filter]
      exact ⟨hl, hne_id⟩
    exact .mk allocId tag baseAddr la hprov hmis hmeta hl' hb hptr hovf hsz hlen hmut hp hal hex hnat hmask

theorem _root_.LeanMiriSpec.Correspondence.ZstZeroMemRel.of_filter_live
    {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : ZstZeroMemRel mach mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    ZstZeroMemRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } } mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hsz hlen hmut =>
    have hne_id : (allocId != id) = true := by
      rw [bne_iff_ne]
      intro heq; subst heq
      exact hne (by simp [hprov, Miri.Memory.Provenance.getAllocId])
    have hl' : (allocId, la) ∈
        (mach.memory.live.filter (fun entry => entry.1 != id)).toList := by
      rw [Array.toList_filter, List.mem_filter]
      exact ⟨hl, hne_id⟩
    exact .mk allocId tag baseAddr la hprov hmis hmeta hl' hb hptr hsz hlen hmut

theorem _root_.LeanMiriSpec.Correspondence.PaddedZstUnionLocalRel.of_dealloc
    {mach : AnnealMachine} {val : Miri.Interpreter.LocalValue AnnealProv}
    {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot} {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : PaddedZstUnionLocalRel mach decl layouts slot mls)
    (hdisj : ∀ mp mp', val = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    PaddedZstUnionLocalRel { mach with memory := deallocLocalMemory mach.memory val }
      decl layouts slot mls := by
  cases h with
  | ofUnionLocalRel _ _ hu =>
    exact .ofUnionLocalRel _ _ (hu.of_dealloc hdisj)
  | uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    cases val with
    | dead => exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem
    | live op =>
      cases op with
      | immediate _ => exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .uninitIndirect S n N f_z zstFlIdx mp c hc hwt hfields (hmem.of_filter_live hne)
  | zstArrayIndirect N _ mp c hc hk hsz hsl hmem =>
    cases val with
    | dead => exact .zstArrayIndirect N slot mp c hc hk hsz hsl hmem
    | live op =>
      cases op with
      | immediate _ => exact .zstArrayIndirect N slot mp c hc hk hsz hsl hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .zstArrayIndirect N slot mp c hc hk hsz hsl hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .zstArrayIndirect N slot mp c hc hk hsz hsl (hmem.of_filter_live hne)
  | zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem =>
    cases val with
    | dead => exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem
    | live op =>
      cases op with
      | immediate _ => exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .zstUninit S n N f_z zstFlIdx mp c hc hwt hfields (hmem.of_filter_live hne)
  | zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem =>
    cases val with
    | dead => exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem
    | live op =>
      cases op with
      | immediate _ => exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem
      | indirect mp0 =>
        unfold deallocLocalMemory; dsimp only
        cases hp0 : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none => exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields hmem
        | some id =>
          have hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
            rw [← hp0]; exact Ne.symm (hdisj mp0 mp rfl rfl)
          exact .zstOverlay S n N f_z zstFlIdx f0Ty sc mp c hc hwt hfields (hmem.of_filter_live hne)

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.lookup_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf) {i : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls i = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : i < af.locals.length) (hlt_mf : i < mf.locals.size),
      get? af.locals i = some slot ∧
      mf.locals[i]? = some mls ∧
      mf.locals[i]'hlt_mf = mls ∧
      PaddedZstUnionLocalRel mach decl body.layouts slot mls := by
  rw [get?_eq_getElem?] at hdecl
  obtain ⟨hlt_d, _⟩ := List.getElem?_eq_some_iff.mp hdecl
  have hlt_af : i < af.locals.length := by rw [hrel.af_locals_len]; exact hlt_d
  have hlt_mf : i < mf.locals.size := by rw [hrel.mf_locals_size]; exact hlt_d
  have hslot : get? af.locals i = some (af.locals[i]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[i]? = some (mf.locals[i]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  have hdecl' : get? body.localDecls i = some decl := hdecl
  exact ⟨af.locals[i]'hlt_af, mf.locals[i]'hlt_mf, hlt_af, hlt_mf, hslot, hmls, rfl,
    hrel.locals_rel i decl _ _ hdecl' hslot hmls⟩

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.update_local
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : PaddedZstUnionLocalRel mach decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4PaddedZst body mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.cache_local_layout
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < mf.locals.size) :
    FrameRelLM2_4PaddedZst body mach af
      (cacheFrameLocalLayout mf idx hlt_mf (translateTy decl.ty body.layouts)) where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := hrel.af_locals_len
  mf_locals_size := by unfold cacheFrameLocalLayout; rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    unfold cacheFrameLocalLayout at hmls_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, Option.some.injEq] at hmls_i
      rw [hdecl] at hdecl_i
      cases hdecl_i
      cases hmls_i
      have hmls_orig : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
        Array.getElem?_eq_getElem hlt_mf
      exact (hrel.locals_rel idx decl slot_i _ hdecl hslot_i hmls_orig).cache_layout
    · simp only [h_eq, ↓reduceIte] at hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.indirect_allocId
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf)
    {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), c⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  have hlt_mf : j < mf.locals.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hlt_d : j < body.localDecls.length := hrel.mf_locals_size ▸ hlt_mf
  have hlt_af : j < af.locals.length := hrel.af_locals_len ▸ hlt_d
  have hdecl : get? body.localDecls j = some (body.localDecls[j]'hlt_d) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_d]
  have hslot : get? af.locals j = some (af.locals[j]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hloc := hrel.locals_rel j _ _ _ hdecl hslot hj
  generalize body.localDecls[j]'hlt_d = decl_j at hloc
  generalize af.locals[j]'hlt_af = slot_j at hloc
  cases hloc with
  | ofUnionLocalRel _ _ hu =>
    cases hu with
    | base _ _ hl =>
      cases hl with
      | indirect _ _ _ _ _ hmp =>
        cases hmp with
        | mk a t _ _ la hprov _ _ hlive _ _ _ _ _ _ _ _ _ =>
          exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
    | union _ _ _ _ _ _ _ _ _ _ _ hmem =>
      cases hmem with
      | mk a t _ la _ hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
    | unionOverlay _ _ _ _ _ _ _ _ _ _ _ _ _ hmem =>
      cases hmem with
      | mk a t _ la _ hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | uninitIndirect _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | zstArrayIndirect _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la hprov _ _ hlive _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | zstUninit _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩
  | zstOverlay _ _ _ _ _ _ _ _ _ _ _ _ hmem =>
    cases hmem with
    | mk a t _ la _ hprov _ _ hlive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨a, la, by simp [hprov, Miri.Memory.Provenance.getAllocId], hlive⟩

theorem _root_.LeanMiriSpec.Correspondence.FrameRelLM2_4PaddedZst.update_local_dealloc
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4PaddedZst body mach af mf) (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : PaddedZstUnionLocalRel
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4PaddedZst body
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf }
    where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj idx i mp mp' (mf.locals[idx]'hlt_mf).layout mls_i.layout h_eq
      · have h0 : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
          Array.getElem?_eq_getElem hlt_mf
        rw [h0]
        cases hls : mf.locals[idx]'hlt_mf
        rw [hls] at hv; dsimp only at hv; subst hv; rfl
      · rw [hmls_i]
        cases mls_i
        dsimp only at hv'; subst hv'; rfl

/-- **`step_storageLive_LM2_4PaddedZst_simulation`** (`G3`): `StorageLive(loc)`
on any declared local `loc` in `StateRelLM2_4PaddedZst` (including active
padded ZST unions `zstUninit`, `zstOverlay`, `uninitIndirect`, and
`zstArrayIndirect`): both `annealStepHooksLM2_4PaddedZst` and `annealStepHooksLM2_4`
step in lockstep with `stepMirFn body s` to `StateRelLM2_4PaddedZst`, freeing any
stack allocation owned by `loc` and preserving `StepPreservesNodup` and
`StepPreservesHighWater m 0`. -/
theorem step_storageLive_LM2_4PaddedZst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) :
    StepRelLM2_4PaddedZst body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s { kind := StatementKind.storageLive loc, span := span }
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.uninit)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af, ht_prot, ht_bor]
    dsimp only [disableLocalBorrows]
    congr 1; congr 1; cases hm_eq : s.memory; simp_all
  rw [ha]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
      annealStepHooksLM2_4PaddedZst, annealStepHooksLM2_4]
    exact annealStepHooksLM2_2_storageLive_any_eq hframes hlt_mf hty hlive
  have hm_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := hm
  have hstep_pz := miri_step_at_statement_ok
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl hfr.location_eq
  have hstep_base := miri_step_at_statement_ok
    (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm_base rfl hfr.location_eq
  rw [hstep_pz, hstep_base]
  refine ⟨?_, rfl, StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_⟩
  · apply StepRelLM2_4PaddedZst.step
    have hnew : PaddedZstUnionLocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .uninit
        { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
      rw [hmls_eq]
      exact .ofUnionLocalRel _ _ (.base _ _
        (.immediate .uninit .uninit mls.layout hloc.layout_eq (Or.inl ⟨rfl, rfl⟩)))
    have hfr' := hfr.update_local_dealloc hdisj hdecl .uninit (.live (.immediate .uninit)) hnew
    exact StateRelLM2_4PaddedZst.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro _ hw0 _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.deallocLocalMemory hw0
      (topFrame.locals[loc]'hlt_mf).value
    exact ⟨hw', by rw [hnext]; omega⟩

/-- **`step_storageDead_LM2_4PaddedZst_simulation`** (`G3`): `StorageDead(loc)`
on any declared local `loc ≠ 0` in `StateRelLM2_4PaddedZst`: both
`annealStepHooksLM2_4PaddedZst` and `annealStepHooksLM2_4` step in lockstep with
`stepMirFn body s` to `StateRelLM2_4PaddedZst`, freeing any stack allocation
owned by `loc` and preserving `StepPreservesNodup` and `StepPreservesHighWater m 0`. -/
theorem step_storageDead_LM2_4PaddedZst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne : loc ≠ 0) :
    StepRelLM2_4PaddedZst body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s { kind := StatementKind.storageDead loc, span := span }
      body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.dead)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af, ht_prot, ht_bor]
    dsimp only [disableLocalBorrows]
    congr 1; congr 1; cases hm_eq : s.memory; simp_all
  rw [ha]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
      annealStepHooksLM2_4PaddedZst, annealStepHooksLM2_4]
    exact annealStepHooksLM2_2_storageDead_any_eq hframes hlt_mf hne hlive
  have hm_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := hm
  have hstep_pz := miri_step_at_statement_ok
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl hfr.location_eq
  have hstep_base := miri_step_at_statement_ok
    (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hfr.body_eq hfr.location_eq hbb hstmt hm_base rfl hfr.location_eq
  rw [hstep_pz, hstep_base]
  refine ⟨?_, rfl, StepPreservesNodup.of_nodup (hnodup.deallocLocalMemory _), ?_⟩
  · apply StepRelLM2_4PaddedZst.step
    have hnew : PaddedZstUnionLocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .dead
        { topFrame.locals[loc]'hlt_mf with value := .dead } := by
      rw [hmls_eq]
      exact .ofUnionLocalRel _ _ (.base _ _ (.dead mls.layout hloc.layout_eq))
    have hfr' := hfr.update_local_dealloc hdisj hdecl .dead .dead hnew
    exact StateRelLM2_4PaddedZst.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨(topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])
  · intro _ hw0 _
    obtain ⟨hw', hnext⟩ := MemoryHighWater.deallocLocalMemory hw0
      (topFrame.locals[loc]'hlt_mf).value
    exact ⟨hw', by rw [hnext]; omega⟩

/-- **Conservativity & Transfer Theorem (`G4`)**:
For any statement `⟨.assign dst (.use op), span⟩` at `s.frame.stmtIdx` of `bb`
where `annealEvalOperandLM2_4PaddedZst` agrees with `annealEvalOperandLM2_4` on
`translateOperand op` (including all non-union operands via
`annealEvalOperandLM2_4PaddedZst_eq_of_not_unionLocal`, all `[]`-projected union
copies/moves via `annealEvalOperandLM2_4PaddedZst_eq_of_projection`, and all
inhabited `[Field j fty]` union field reads via
`annealEvalOperandLM2_4PaddedZst_eq_of_inhabited_field`):
1. `Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
   Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m`;
2. Any `StepRelLM2_4 body m (stepMirFn body s) (Step.step (annealStepHooksLM2_4 ...) () m)`
   transfers immediately to `StepRelLM2_4PaddedZst` under `annealStepHooksLM2_4PaddedZst`! -/
theorem step_padded_zst_transfer_assign_use
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    {bb : BasicBlockData} {dst : Place} {op : Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign dst (.use op), span⟩)
    (hop : ∀ known,
      annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts (translateOperand op) known =
        annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known) :
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 body.localDecls body.layouts) () m ∧
    (StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) →
      StepRelLM2_4PaddedZst body m (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m)) := by
  have heval_eq :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
        (translateStmt ⟨.assign dst (.use op), span⟩) m =
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4 body.localDecls body.layouts) ()
        (translateStmt ⟨.assign dst (.use op), span⟩) m := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind, translateRvalue]
    exact annealStepHooksLM2_4PaddedZst_assign_use_eq body.localDecls body.layouts ()
      (translatePlace dst) (translateOperand op) _ m hop
  have hstep_eq :
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 body.localDecls body.layouts) () m := by
    unfold Miri.Interpreter.Step.step
    rw [stack_currentFrame?_singleton m.stack topFrame hframes]
    dsimp only
    rw [hloc, hbody]
    dsimp only
    rw [translateBody_basicBlocks_getElem?, hbb]
    dsimp only [Option.map]
    rw [translateBasicBlockData_statements_getElem?, hstmt]
    dsimp only [Option.map]
    rw [heval_eq]
  exact ⟨hstep_eq, fun h => by rw [hstep_eq]; exact h.toPaddedZst⟩

/-- `isUnionLocal` holds for any local declared with a `WellTypedPaddedZstUnionTy`. -/
theorem isUnionLocal_of_wellTypedPaddedZst {body : CapturedMir} {u : Local} {uDecl : LocalDecl}
    {S N f_z zstFlIdx : Nat} (hdecl : get? body.localDecls u = some uDecl)
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx) :
    isUnionLocal body.localDecls body.layouts u = true := by
  obtain ⟨n, hn, _⟩ := hwt.fields_union
  simp only [isUnionLocal, lookupLocalDeclLayout, hdecl, LeanMiriSpec.Correspondence.isUnionLayout, hn]

/-- Whole-union copy (`_w = copy _u`) of an all-uninit `[(); N]`-initialized
padded union (`PaddedZstUnionLocalRel.zstUninit`) into an uninitialized immediate
union local `_w` steps both machines in lockstep (`StateRelLM2_4PaddedZst`),
copying `InitMask.new (translateSizeBytes S) false` into `_w`'s fresh allocation
via `union_copy_uninit_alloc_spec` (`kani#5176`). -/
theorem step_padded_zst_union_whole_copy_uninit_mask_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S n N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (List.replicate n .unit))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    ∃ (s' : MachineState) (m' : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_4PaddedZst body s' m' ∧
      get? s'.frame.locals w =
        some (.init (.aggregate 0 (List.replicate n .unit))) ∧
      (∀ j, j ≠ w → get? s'.frame.locals j = get? s.frame.locals j) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
      PaddedZstUnionUninitMemRel m'.machine uDecl.ty body.layouts S mp ∧
      PaddedZstUnionUninitMemRel m'.machine wDecl.ty body.layouts S mp_w ∧
      LiveAllocsNodup m'.machine ∧
      (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  rcases hstate with ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
    hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨mem', id, hres⟩ := hcanRes
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  have hstep_a : stepMirFn body s = evalStmt s
      ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩ body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
  have hwu : w ≠ u := by
    intro h; subst h; rw [hw_uninit] at hu_slot; cases hu_slot
  have hwt_w : WellTypedPaddedZstUnionTy body.layouts wDecl.ty S N f_z zstFlIdx := hty ▸ hwt
  have hfields_w : (translateTy wDecl.ty body.layouts).layout.fields = .Union n := hty ▸ hfields_u
  have hS := hwt.size_valid
  have hS16 : S ≤ 16 := by rcases hS with h | h | h | h | h <;> omega
  obtain ⟨c_u, hmls_u⟩ := hu_mls topFrame hframes
  obtain ⟨slot_w, mls_w, hlt_af_w, hlt_w, hslot_w, hmls_w, hmls_w_eq, hloc_w⟩ :=
    hframe.lookup_local hdecl_w
  rw [hw_uninit] at hslot_w
  injection hslot_w with hslot_w
  subst hslot_w
  have hw_imm' := hw_imm topFrame hframes mls_w hmls_w
  have hloc_w' : LocalRel m.machine wDecl body.layouts .uninit mls_w := by
    cases hloc_w with
    | ofUnionLocalRel _ _ hu =>
      cases hu with
      | base _ _ hl => exact hl
    | uninitIndirect _ _ _ _ _ mp' _ _ _ _ _ => exact absurd rfl (hw_imm' mp')
    | zstArrayIndirect _ _ mp' _ _ _ _ _ _ => exact absurd rfl (hw_imm' mp')
  have hcache_w := hloc_w'.layout_eq
  have hmls_w_val : mls_w.value = .live (.immediate .uninit) := by
    cases hloc_w' with
    | indirect _ mp' _ _ _ _ => exact absurd rfl (hw_imm' mp')
    | immediate _ imm _ _ hv =>
      rcases hv with ⟨_, rfl⟩ | ⟨_, h, _⟩
      · rfl
      · cases h
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', hmls_u_eq, hloc_u⟩ := hframe.lookup_local hdecl_u
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_u := hloc_u.layout_eq
  let layW := translateTy wDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame w hlt_w layW
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 w none topFrame.localsIdentity, layW⟩
  have hevalPlace : annealEvalPlace body.localDecls body.layouts ⟨w, #[]⟩ m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_w hdecl_w (by rw [hmls_w_eq]; exact hcache_w)
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp), c_u⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hwu] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
  have hop : annealEvalOperand body.localDecls body.layouts (.Copy ⟨u, #[]⟩) (some layW) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ :=
    annealEvalOperand_copy_live (m := m₀) rfl hlt_u₀ hdecl_u hmls_u₀ hcache_u
  have hlt_w₁ : w < topFrame₁.locals.size := by
    dsimp only [topFrame₁, topFrame₀]; rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size]
    exact hlt_w
  have hmls_w₁ : topFrame₁.locals[w]? = some { mls_w with layout := some layW } := by
    dsimp only [topFrame₁, topFrame₀, cacheFrameLocalLayout]
    simp [Ne.symm hwu, hmls_w_eq]
  have hw₁ : topFrame₁.locals[w]'hlt_w₁ = { mls_w with layout := some layW } := by
    have h := Array.getElem?_eq_getElem hlt_w₁
    rw [hmls_w₁] at h
    exact (Option.some.inj h).symm
  have hc_w₁ : (topFrame₁.locals[w]'hlt_w₁).layout = some layW := by rw [hw₁]
  have hval_w₁ : (topFrame₁.locals[w]'hlt_w₁).value = .live (.immediate .uninit) := by
    rw [hw₁]; exact hmls_w_val
  obtain ⟨alloc, htry, hbs, hlen_alloc, hnat, hmut, hal, hprov_alloc, hmask_alloc⟩ :=
    freshUnionAlloc_spec layW.layout.size layW.layout.align.abi (translateTy_align_pow2_le_29 _ _)
  have hmem_orig := hmem
  cases hmem with
  | mk allocId tag baseAddr la hprov_u hmis_u hmeta_u hlive_u hbase_u hptr_u hovf_u hsz_u
      hlen_u hmut_u hp_u hal_u hex_u hnat_u hmask_u =>
  have hlayW_sz : layW.layout.size = translateSizeBytes S := hwt_w.size_eq
  have hlayW_toNat : layW.layout.size.bytes.toNat = S := by
    rw [hlayW_sz]
    exact translateSizeBytes_toNat_of_valid hS
  obtain ⟨A_w, hcopy_w, hA_sz, hA_len, hA_align, hA_mut, hA_prov, hA_mask,
      hA_extra, hA_native, _⟩ :=
    union_copy_uninit_alloc_spec (src := la.allocation)
      (dest := alloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree))
      hS false hlen_u hsz_u hp_u hmask_u
      (by change alloc.len = S; rw [hlen_alloc, hlayW_toNat])
      (by change alloc.byteSize = translateSizeBytes S; rw [hbs, hlayW_sz])
      hmut hprov_alloc
      (by show (alloc.withExtra none).initializationMask.len = translateSizeBytes S
          change alloc.initializationMask.len = translateSizeBytes S
          rw [hmask_alloc, hlayW_sz]; rfl)
  have hcopy_w' : Miri.Memory.Allocation.copy la.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO layW.layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true (alloc.withExtra none) =
        .ok () A_w := by
    rw [hlayW_sz]; exact hcopy_w
  have hmemcopy := annealMemCopyOp_freshUnion (body := body) (m := m₁) rfl hlt_w₁ hdecl_w hc_w₁
    hval_w₁ hwt_w.sized htry hres hnodup hprov_u hlive_u hbase_u hptr_u hcopy_w'
    layU topFrame.localsIdentity
  have hunion_w := isUnionLocal_of_wellTypedPaddedZst hdecl_w hwt_w
  have hunion_u := isUnionLocal_of_wellTypedPaddedZst hdecl_u hwt
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨w, #[]⟩
      (translateRvalue (.use (.copy ⟨u, .nil⟩))) = true := by
    simp [lm24Assign, lm24Place, hunion_w]
  have huse : usesMemCopy ⟨.indirect mp, layU⟩ = true := by
    simp [usesMemCopy, layU, hfields_u]
  have hevalPlace' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalPlace ()
      ⟨w, #[]⟩ true m = .ok destPlace m₀ := hevalPlace
  have hop' : (annealRvalueHooksLM2_4 body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy ⟨u, .nil⟩))
      (some ((annealRvalueHooksLM2_4 body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ := hop
  have hop_pz : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy ⟨u, .nil⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp, layU⟩ m₁ := by
    show annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
      (.Copy ⟨u, #[]⟩) (some layW) m₀ = .ok ⟨.indirect mp, layU⟩ m₁
    unfold annealEvalOperandLM2_4PaddedZst
    simp only [hunion_u, ↓reduceIte]
    exact hop
  let mp_w := stackAllocPlace id
  let mach₃ := stackAllocMachine m.machine mem' id A_w
  let tf₃ := setFrameLocalIndirect topFrame₁ w hlt_w₁ mp_w
  let st₃ : AnnealStepState := { stack := ⟨#[tf₃]⟩, machine := mach₃ }
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    rw [show Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksLM2_4 body.localDecls body.layouts) ()
          (translateRvalue (.use (.copy ⟨u, .nil⟩))) ⟨w, #[]⟩) m =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₁ by
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace
      rw [EStateM.bind_eq_ok hevalPlace']
      dsimp only [translateRvalue]
      rw [EStateM.bind_eq_ok hop']
      simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hm_stmt_pz : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩) m = (st₃, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    rw [show Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts) ()
          (translateRvalue (.use (.copy ⟨u, .nil⟩))) ⟨w, #[]⟩) m =
      Miri.Interpreter.runRvalue
        (annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp, layU⟩ destPlace) m₁ by
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace
      rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
        ⟨w, #[]⟩ true m = .ok destPlace m₀ from hevalPlace)]
      dsimp only [translateRvalue]
      rw [EStateM.bind_eq_ok hop_pz]
      simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2, huse, ↓reduceIte]]
    unfold Miri.Interpreter.runRvalue
    rw [hmemcopy]
  have hloc₃ : tf₃.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hframe.location_eq
  have hstep_m := miri_step_at_statement_ok (annealStepHooksLM2_4 body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt rfl hloc₃
  have hstep_m_pz := miri_step_at_statement_ok (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt_pz rfl hloc₃
  -- Anneal side: `validateLoadedValue` accepts `.aggregate 0 (List.replicate n .unit)` on a union local.
  have hvld : validateLoadedValue body.layouts body.localDecls (.copy ⟨u, .nil⟩)
      (.aggregate 0 (List.replicate n .unit)) = true := by
    obtain ⟨defPath, args, _, _, _, hk, _⟩ := hwt.adt_spec
    have hpt : placeTy body.localDecls body.layouts ⟨u, .nil⟩ = some uDecl.ty := by
      simp [placeTy, hdecl_u, resolveProjectedTy]
    simp only [validateLoadedValue, operandTy]
    rw [hpt]; dsimp only; rw [hk]
  have hrv : evalRvalue s.frame.locals (.use (.copy ⟨u, .nil⟩)) s.memory body.localDecls
      body.layouts =
      .ok (.aggregate 0 (List.replicate n .unit)) s.frame.locals s.memory := by
    unfold evalRvalue; dsimp only; rw [hbor, hcaller]
    simp only [evalOperand, hu_slot, readProjectedValue, hvld]
  let locals₂ := s.frame.locals.set w (.init (.aggregate 0 (List.replicate n .unit)))
  have ha_ok : evalStmt s ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩
      body.localDecls body.layouts = MirStepNode.step (advanceStmt s locals₂ s.memory) := by
    unfold evalStmt
    dsimp only
    rw [hrv]
    simp only []
    rw [hprot, hbor]
    dsimp only [invalidateConflictingBorrows]
    rw [hmem_same]
    simp [hw_uninit, set?_eq_some_set hlt_af_w, locals₂]
  obtain ⟨hlive_b, hfreshne, hbase_b⟩ := stackAllocMachine_live_base (mach := m.machine) A_w hres
  have hmem_w : PaddedZstUnionUninitMemRel mach₃ wDecl.ty body.layouts S mp_w :=
    .mk id .one (annealStackBaseAddr id) ⟨.stack, A_w⟩ rfl rfl rfl
      (by simp [mach₃, stackAllocMachine])
      (lookupBaseAddr_stackAllocMachine_self _ _ _ _) rfl (annealStackBaseAddr_add_lt id hS16)
      hA_sz hA_len hA_mut hA_prov
      (by rw [hA_align]; exact hal) hA_extra (by rw [hA_native]; exact hnat) hA_mask
  have hmem_u : PaddedZstUnionUninitMemRel mach₃ uDecl.ty body.layouts S mp := by
    cases hmem_orig with
    | mk allocId tag baseAddr la hprov hmis hmeta hlive_u hbase_u hptr hovf hsz
        hlen hmut hp hal hex hnat hmask =>
      exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive_b _ hlive_u)
        ((hbase_b allocId la hlive_u).trans hbase_u) hptr hovf hsz hlen hmut hp hal hex hnat hmask
  have hframe₁ : FrameRelLM2_4PaddedZst body m.machine s.frame topFrame₁ :=
    (hframe.cache_local_layout hdecl_w hlt_w).cache_local_layout hdecl_u hlt_u₀
  have hdisj₁ : MemoryAllocDisjoint topFrame₁ :=
    (hdisj.cache_layout hlt_w _).cache_layout hlt_u₀ _
  let tf_fin := { tf₃ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
  let m' : AnnealStepState := { st₃ with stack := ⟨#[tf_fin]⟩ }
  have hframe_fin : FrameRelLM2_4PaddedZst body mach₃ (advanceStmt s locals₂ s.memory).frame tf_fin :=
    { body_eq := hframe.body_eq
      location_eq := rfl
      af_locals_len := by
        show (s.frame.locals.set w _).length = _
        rw [List.length_set]; exact hframe.af_locals_len
      mf_locals_size := by
        show (topFrame₁.locals.set w _ hlt_w₁).size = _
        rw [Array.size_set]; exact hframe₁.mf_locals_size
      locals_rel := by
        intro i decl slot mls hdecl hslot hmls
        have hslot' : get? locals₂ i = some slot := hslot
        have hmls' : (topFrame₁.locals.set w
            { topFrame₁.locals[w]'hlt_w₁ with value := .live (.indirect mp_w) } hlt_w₁)[i]? =
            some mls := hmls
        rw [get?_eq_getElem?, List.getElem?_set] at hslot'
        rw [Array.getElem?_set] at hmls'
        by_cases hiw : w = i
        · subst hiw
          simp only [↓reduceIte, hlt_af_w, Option.some.injEq] at hslot' hmls'
          subst hslot' hmls'
          rw [hdecl_w] at hdecl
          cases hdecl
          refine .zstUninit S n N f_z zstFlIdx mp_w _ ?_ hwt_w hfields_w hmem_w
          intro l hl; rw [hc_w₁] at hl; exact (Option.some.inj hl).symm
        · simp only [hiw, ↓reduceIte] at hslot' hmls'
          exact (hframe₁.locals_rel i decl slot mls hdecl hslot' hmls').of_live_base hlive_b hbase_b }
  have hdisj_fin : MemoryAllocDisjoint tf_fin := by
    intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_w : w = i
    · subst hi_w
      have hj_w : w ≠ j := hij
      simp only [hj_w, ↓reduceIte] at hj
      simp only [↓reduceIte] at hi
      obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hj
      injection hi with hi; injection hi with hv _; injection hv with hv; injection hv with hv
      subst hv; rw [ha]
      simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
        Option.some.injEq]
      exact fun h => hfreshne a la' hla h.symm
    · simp only [hi_w, ↓reduceIte] at hi
      by_cases hj_w : w = j
      · subst hj_w
        simp only [↓reduceIte] at hj
        obtain ⟨a, la', ha, hla⟩ := hframe₁.indirect_allocId hi
        injection hj with hj; injection hj with hv _; injection hv with hv; injection hv with hv
        subst hv; rw [ha]
        simp only [mp_w, stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
          Option.some.injEq]
        exact hfreshne a la' hla
      · simp only [hj_w, ↓reduceIte] at hj
        exact hdisj₁ i j mp_i mp_j lay_i lay_j hij hi hj
  have hstate' : StateRelLM2_4PaddedZst body (advanceStmt s locals₂ s.memory) m' :=
    StateRelLM2_4PaddedZst.mk tf_fin rfl hretCont ⟨retLay, hretPlace⟩ hframe_fin hcal hstack hbor hprot
      hcaller hdisj_fin
  have himm_fin : ∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
      IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf_fin j := by
    intro tf htf j hj himm_j
    rw [hframes] at htf
    have htf' : topFrame = tf := by simpa using htf
    subst htf'
    have h₁ := (himm_j.cache_layout hlt_w layW).cache_layout hlt_u₀ layU
    intro mls hmls
    dsimp only [tf_fin, tf₃, setFrameLocalIndirect] at hmls
    rw [Array.getElem?_set_ne _ (Ne.symm hj)] at hmls
    exact h₁ mls hmls
  refine ⟨advanceStmt s locals₂ s.memory, m', mp_w, tf_fin, by rw [hstep_a, ha_ok],
    hstep_m, hstep_m_pz, hstate', ?_, ?_, rfl, ⟨(topFrame₁.locals[w]'hlt_w₁).layout, ?_⟩,
    ⟨some layU, ?_⟩, hmem_u, hmem_w, LiveAllocsNodup.stackAllocMachine A_w hnodup hres,
    himm_fin, rfl, rfl⟩
  · simp [advanceStmt, locals₂, get?_eq_getElem?, hlt_af_w]
  · intro j hj
    simp [advanceStmt, locals₂, get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hj)]
  · simp [tf_fin, tf₃, setFrameLocalIndirect]
  · dsimp only [tf_fin, tf₃, setFrameLocalIndirect]
    rw [Array.getElem?_set_ne _ hwu]
    dsimp only [topFrame₁, cacheFrameLocalLayout]
    rw [Array.getElem?_set_self, hmls_u₀]

/-- Concrete `#[repr(C)] union PU { z: [(); 4], a: u8, b: u32, void: VoidZst }`
(`S = 4`, `N = 4`, `n = 4`). -/
def lm24ZstArr4Layout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .array ⟨0⟩ 4, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def lm24VoidZstLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .empty,
    isUninhabited := true, fieldLayouts := [] }

def lm24PULayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .union 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0, 1, 3] }

def lm24PULayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lm24U8Layout, lm24U32Layout, lm24ZstArr4Layout, lm24VoidZstLayout, lm24PULayout] }

def lm24UnitTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def lm24ZstArr4Ty : Ty := { kind := .array (.tuple []) 4, layoutIdx := 2 }
def lm24VoidZstTy : Ty := { kind := .adt "VoidZst" [], layoutIdx := 3 }
def lm24PUTy : Ty := { kind := .adt "PU" [], layoutIdx := 4 }

theorem lm24_wt_PU : WellTypedPaddedZstUnionTy lm24PULayouts lm24PUTy 4 4 0 2 where
  size_valid := Or.inr (Or.inr (Or.inl rfl))
  count_pos := by decide
  fields_union := ⟨4, rfl, by decide⟩
  size_eq := rfl
  sized := rfl
  align_le := by decide
  adt_spec := ⟨"PU", [], lm24PULayout, 4, lm24ZstArr4Layout,
    rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The Anneal `LocalSlot` of `PU` initialized via its `[(); 4]` ZST arm (`f_z = 0`):
all 4 union field slots hold `.unit`, whose `encodeByLayoutIdxAux` byte image is
4 `.uninit` bytes (`replicateUninitBytes 4`). -/
def lm24PUZstSlot : LocalSlot := .init (.aggregate 0 [.unit, .unit, .unit, .unit])

/-- The Anneal `LocalSlot` of `PU` initialized via its `u8` arm (`f = 1`) with `0x55_u8`. -/
def lm24PUU8Slot (n : Nat) : LocalSlot :=
  .init (.aggregate 0 [.unit, .scalar ⟨n, 1⟩, .unit, .unit])

/-- The Anneal `LocalSlot` of `PU` initialized via its `u32` arm (`f = 2`) with `n_u32`. -/
def lm24PUU32Slot (n : Nat) : LocalSlot :=
  .init (.aggregate 0 [.unit, .unit, .scalar ⟨n, 4⟩, .unit])

/-- The Anneal `LocalSlot` of `PU` after `_1 = PU { a: 0x55_u8 }` is overwritten
by `_1.0 = copy _5` (`[(); 4]` ZST arm): all 4 typed slots become `.unit` and the
`D13a` raw-byte overlay retains `0x55` at byte `0` and `.uninit` at bytes `[1, 4)`. -/
def lm24PUZstOverU8Slot (n : Nat) : LocalSlot :=
  .init (.aggregate 0
    ([.unit, .unit, .unit, .unit] ++
      [.aggregate 0
        (encodeRawAbstractByteVals
          (encodeLittleEndianBytes n 1 none ++ replicateUninitBytes 3))]))

/-- Locals of `lm24PUBody`:
- `_0: u32`
- `_1: PU`
- `_2: u8`
- `_3: u32`
- `_4: PU`
- `_5: [(); 4]`
- `_6: [(); 4]`
- `_7: ()`
- `_8: VoidZst` -/
def lm24PUBody : CapturedMir where
  defPath := "lm_2_4_witness::padded_zst_unions"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    lm24Decl lm24U32Ty,
    lm24Decl lm24PUTy,
    lm24Decl lm24U8Ty,
    lm24Decl lm24U32Ty,
    lm24Decl lm24PUTy,
    lm24Decl lm24ZstArr4Ty,
    lm24Decl lm24ZstArr4Ty,
    lm24Decl lm24UnitTy,
    lm24Decl lm24VoidZstTy]
  basicBlocks := [
    -- `bb0`: `_1 = PU { z: copy _5 }; _4 = copy _1; _6 = copy (_4.0: [(); 4]); _2 = copy (_4.1: u8)` (UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 0)) [.copy (local_ 5)])),
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨4, [.field 0 lm24ZstArr4Ty]⟩))),
        mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb1`: `_1.0 = copy _5; _4 = move _1; _3 = copy (_4.2: u32)` (UB)
    { statements := [
        mkStmt (.assign ⟨1, [.field 0 lm24ZstArr4Ty]⟩ (.use (.copy (local_ 5)))),
        mkStmt (.assign (local_ 4) (.use (.move (local_ 1)))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb2`: `_1 = PU { a: 0x55_u8 }; _1.0 = copy _5; _6 = copy (_1.0: [(); 4]); _2 = copy (_1.1: u8); _3 = copy (_1.2: u32)` (UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 1)) [.constant (lm24ConstU8 0x55)])),
        mkStmt (.assign ⟨1, [.field 0 lm24ZstArr4Ty]⟩ (.use (.copy (local_ 5)))),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty]⟩))),
        mkStmt (.assign (local_ 2) (.use (.copy ⟨1, [.field 1 lm24U8Ty]⟩))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨1, [.field 2 lm24U32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb3`: `_1 = PU { z: copy _5 }; _7 = copy (_1.0[2 of 4]: ()); _7 = copy (_1.0[4 of 4]: ())` (OOB UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 0)) [.copy (local_ 5)])),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty, .constantIndex 2 4 false]⟩))),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty, .constantIndex 4 4 false]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb4`: `_1 = PU { b: 0x01020304_u32 }; _8 = copy (_1.3: VoidZst)` (Uninhabited 0-byte arm UB, `kani#5159`)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 2)) [.constant (lm24ConstU32 0x01020304)])),
        mkStmt (.assign (local_ 8) (.use (.copy ⟨1, [.field 3 lm24VoidZstTy]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb5`: `_1 = PU { z: copy _5 }; StorageDead(_1); StorageLive(_1); _6 = copy (_1.0: [(); 4])` (Uninit union local UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 0)) [.copy (local_ 5)])),
        mkStmt (.storageDead 1),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨1, [.field 0 lm24ZstArr4Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    -- `bb6`: `_1 = PU { a: 0x55_u8 }; _4 = copy _1; _7 = copy (_4.0[2 of 4]: ()); _2 = copy (_4.1: u8); _3 = copy (_4.2: u32)` (UB)
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.adt "PU" 0 (some 1)) [.constant (lm24ConstU8 0x55)])),
        mkStmt (.assign (local_ 4) (.use (.copy (local_ 1)))),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨4, [.field 0 lm24ZstArr4Ty, .constantIndex 2 4 false]⟩))),
        mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))),
        mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm24FnAbi
  layouts := lm24PULayouts
  allocations := []

def lm24PUAnnealState (b k : Nat) (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := k, locals := locals }
    memory := (initMachineState lm24PUBody []).memory }

/-- Initial Anneal state of block `b` in `lm24PUBody` with `_5 : [(); 4]`
initialized to `zstArrayVal 4` and all other locals `.uninit`. -/
def lm24PUInitAnneal (b : Nat) : MachineState :=
  lm24PUAnnealState b 0
    [.uninit, .uninit, .uninit, .uninit, .uninit,
     .init (zstArrayVal 4), .uninit, .uninit, .uninit]

/-- Zero-byte mutable allocation backing `_5 : [(); 4]` in `lean-miri`. -/
def lm24ZstArr4Alloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[] (translateAlignBytes 1) .Mut)
    (by with_unfolding_all rfl)).withExtra none

def lm24ThirdAllocId : Miri.Memory.AllocId := ⟨3, by decide⟩
def lm24ThirdBaseAddr : UInt64 := 0x3000

def lm24ThirdMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes lm24ThirdBaseAddr,
            some (.concrete lm24ThirdAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm24FourthAllocId : Miri.Memory.AllocId := ⟨4, by decide⟩
def lm24FourthBaseAddr : UInt64 := 0x4000

def lm24FourthMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes lm24FourthBaseAddr,
            some (.concrete lm24FourthAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm24PUUninitAlloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.tryNew (Prov := AnnealProv)
      (translateSizeBytes 4) (translateAlignBytes 4) .Uninit
      (fun _ _ => some #[0, 0, 0, 0]))
    (by with_unfolding_all rfl)).withExtra none

private theorem allocation_eq_of_parts {P E : Type}
    {a b : Miri.Memory.Allocation P E}
    (hraw : unionAllocRaw a = unionAllocRaw b)
    (hsz : a.byteSize = b.byteSize)
    (hprov : a.provenanceMap = b.provenanceMap)
    (hmask : a.initializationMask = b.initializationMask)
    (hal : a.align = b.align)
    (hmut : a.mutability = b.mutability)
    (hex : a.extra = b.extra)
    (hnat : a.nativeBuffer = b.nativeBuffer) :
    a = b := by
  induction a using Miri.Memory.Allocation.casesOn
  induction b using Miri.Memory.Allocation.casesOn
  cases hraw; cases hsz; cases hprov; cases hmask; cases hal; cases hmut; cases hex; cases hnat
  rfl

private theorem lm24PU_copy_uninitAlloc4_eq :
    Miri.Memory.Allocation.copy lm24PUUninitAlloc4
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true lm24PUUninitAlloc4 =
    .ok () lm24PUUninitAlloc4 := by
  obtain ⟨dest', hcopy, hsz, _, hal, hmut, hprov, hmask, hex, hnat, hraw⟩ :=
    union_copy_uninit_alloc_spec (src := lm24PUUninitAlloc4) (dest := lm24PUUninitAlloc4)
      (S := 4) (Or.inr (Or.inr (Or.inl rfl))) false
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  rw [hcopy]
  congr 1
  exact allocation_eq_of_parts hraw
    (hsz.trans (by with_unfolding_all rfl))
    (hprov.trans (by with_unfolding_all rfl))
    (hmask.trans (by with_unfolding_all rfl))
    hal
    (hmut.trans (by with_unfolding_all rfl))
    hex hnat

def lm24PUMachine : AnnealMachine :=
  { memory :=
      { (Miri.Memory.MemoryState.empty : AnnealMemory) with
        nextAllocId := 5
        live := #[(witnessAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }),
                  (lm24ThirdAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc }),
                  (lm24FourthAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc })] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[{ allocId := witnessAllocId, address := witnessBaseAddr },
                      { allocId := lm24SecondAllocId, address := lm24SecondBaseAddr },
                      { allocId := lm24ThirdAllocId, address := lm24ThirdBaseAddr },
                      { allocId := lm24FourthAllocId, address := lm24FourthBaseAddr }]
        intToPtrMap := #[{ address := witnessBaseAddr, allocId := witnessAllocId },
                         { address := lm24SecondBaseAddr, allocId := lm24SecondAllocId },
                         { address := lm24ThirdBaseAddr, allocId := lm24ThirdAllocId },
                         { address := lm24FourthBaseAddr, allocId := lm24FourthAllocId }] }
    borrowTracker := none }

def lm24PUInitMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm24PUBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm24U32Ty lm24PULayouts) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := some (translateTy lm24U32Ty lm24PULayouts) },
      { value := .live (.indirect lm24BaseMemPlace), layout := some (translateTy lm24PUTy lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24U8Ty lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24U32Ty lm24PULayouts) },
      { value := .live (.indirect lm24Arr2MemPlace), layout := some (translateTy lm24PUTy lm24PULayouts) },
      { value := .live (.indirect lm24ThirdMemPlace), layout := some (translateTy lm24ZstArr4Ty lm24PULayouts) },
      { value := .live (.indirect lm24FourthMemPlace), layout := some (translateTy lm24ZstArr4Ty lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24UnitTy lm24PULayouts) },
      { value := .live (.immediate .uninit), layout := some (translateTy lm24VoidZstTy lm24PULayouts) }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨b, 0⟩ }

def lm24PUInitMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24PUInitMiriFrame b]⟩, machine := lm24PUMachine }

def lm24PUMiriAt (b k : Nat) : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame b with location := .mir ⟨b, k⟩ }]⟩, machine := lm24PUMachine }

private theorem lm24PU_memCopyOp_eq
    (f : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hf4 : annealForceUnionAllocation lm24PUBody.localDecls lm24PUBody.layouts
      ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
      { stack := ⟨#[f]⟩, machine := lm24PUMachine } =
      .ok ⟨lm24Arr2MemPlace, translateTy lm24PUTy lm24PULayouts⟩
        { stack := ⟨#[f]⟩, machine := lm24PUMachine }) :
    annealMemCopyOp lm24PUBody.localDecls lm24PUBody.layouts
      ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
      { stack := ⟨#[f]⟩, machine := lm24PUMachine } =
    .ok () { stack := ⟨#[f]⟩, machine := lm24PUMachine } := by
  have hfind_src : lm24PUMachine.memory.live.find? (fun (k, _) => k == witnessAllocId) =
      some (witnessAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }) := by
    with_unfolding_all rfl
  have hfind_dst : lm24PUMachine.memory.live.findIdx? (fun (k, _) => k == lm24SecondAllocId) =
      some 1 := by
    with_unfolding_all rfl
  have hbase_src : lm24PUMachine.lookupBaseAddr witnessAllocId = some witnessBaseAddr := by
    with_unfolding_all rfl
  have hbase_dst : lm24PUMachine.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
    with_unfolding_all rfl
  have hneq : (witnessAllocId == lm24SecondAllocId) = false := by decide
  unfold annealMemCopyOp
  dsimp only []
  rw [EStateM.bind_eq_ok hf4]
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    lm24BaseMemPlace, lm24Arr2MemPlace, Option.bind, Miri.Memory.Provenance.getAllocId]
  rw [hbase_src, hfind_src, hbase_dst, hfind_dst]
  dsimp only []
  have hget1 : lm24PUMachine.memory.live[1]? =
      some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }) := rfl
  rw [hget1]
  dsimp only []
  have hoff1 :
      Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes witnessBaseAddr).bytes - witnessBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
  have hoff2 :
      Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
  have hlay_sz : (translateTy lm24PUTy lm24PULayouts).layout.size = translateSizeBytes 4 := rfl
  simp only [hoff1, hoff2, hlay_sz, hneq, lm24PU_copy_uninitAlloc4_eq]
  rfl

private theorem lm24PU_bb0_step1 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 0 1) = (lm24PUMiriAt 0 2, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 0 1)).2 = .ok true := by
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 0 1) = .ok destPlace (lm24PUMiriAt 0 1) := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 0 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMiriAt 0 1) := by with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 0 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMiriAt 0 1) := by with_unfolding_all rfl
  have hmc := lm24PU_memCopyOp_eq { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ }
    (by with_unfolding_all rfl)
  have huse : usesMemCopy ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ = true := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 0 1) =
    .ok () (lm24PUMiriAt 0 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 0 1) =
    .ok () (lm24PUMiriAt 0 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 0 1) = .ok destPlace (lm24PUMiriAt 0 1) from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨4, #[]⟩
      (translateRvalue (.use (.copy (local_ 1)))) = true := rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      (lm24PUMiriAt 0 1) = (lm24PUMiriAt 0 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) (lm24PUMiriAt 0 1) = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      (lm24PUMiriAt 0 1) = (lm24PUMiriAt 0 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) (lm24PUMiriAt 0 1) = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      (topFrame' := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      rfl rfl rfl (blockIdx := 0) (stmtIdx := 1) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      (topFrame' := { lm24PUInitMiriFrame 0 with location := .mir ⟨0, 1⟩ })
      rfl rfl rfl (blockIdx := 0) (stmtIdx := 1) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

def lm24PUMovedFrame1 (k : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { lm24PUInitMiriFrame 1 with
    locals := (lm24PUInitMiriFrame 1).locals.set! 1
      { value := .live (.immediate .uninit), layout := some (translateTy lm24PUTy lm24PULayouts) },
    location := .mir ⟨1, k⟩ }

def lm24PUMovedMiri1 (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm24PUMovedFrame1 k]⟩, machine := lm24PUMachine }

private theorem lm24PU_bb1_step1 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 1 1) = (lm24PUMovedMiri1 2, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUMiriAt 1 1)).2 = .ok true := by
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 1 1) = .ok destPlace (lm24PUMiriAt 1 1) := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.move (local_ 1)))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 1 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMovedMiri1 1) := by with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.move (local_ 1)))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUMiriAt 1 1) =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      (lm24PUMovedMiri1 1) := by with_unfolding_all rfl
  have hmc := lm24PU_memCopyOp_eq (lm24PUMovedFrame1 1) (by with_unfolding_all rfl)
  have huse : usesMemCopy ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ = true := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.move (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 1 1) =
    .ok () (lm24PUMovedMiri1 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.move (local_ 1)))) ⟨4, #[]⟩ (lm24PUMiriAt 1 1) =
    .ok () (lm24PUMovedMiri1 1) := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true (lm24PUMiriAt 1 1) = .ok destPlace (lm24PUMiriAt 1 1) from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨4, #[]⟩
      (translateRvalue (.use (.move (local_ 1)))) = true := rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.move (local_ 1))))))
      (lm24PUMiriAt 1 1) = (lm24PUMovedMiri1 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.move (local_ 1)))) (lm24PUMiriAt 1 1) = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.move (local_ 1))))))
      (lm24PUMiriAt 1 1) = (lm24PUMovedMiri1 1, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.move (local_ 1)))) (lm24PUMiriAt 1 1) = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      rfl rfl rfl (blockIdx := 1) (stmtIdx := 1) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      rfl rfl rfl (blockIdx := 1) (stmtIdx := 1) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

private theorem miri_step_eq
    (hooks :
      Miri.Interpreter.StepHooks
        AnnealProv
        Miri.Interpreter.LocalLayout
        Unit
        AnnealMachine
        Unit
        (Miri.Interpreter.RuntimePlace AnnealProv))
    (m : AnnealStepState) (r : Except Miri.Interpreter.StepError Bool)
    (h : (Miri.Interpreter.Step.step hooks () m).2 = r) :
    Miri.Interpreter.Step.step hooks () m =
      ((Miri.Interpreter.Step.step hooks () m).1, r) :=
  Prod.ext rfl h

/-- Kernel-checked multi-step execution of `bb0` in `lm24PUBody` (`kani#5176`):
1. `_1 = PU { z: copy _5 }` constructs `PU` via its `[(); 4]` ZST array arm:
   Anneal stores `lm24PUZstSlot` (`[.unit, .unit, .unit, .unit]`, whose
   `encodeByLayoutIdxAux` byte image is `replicateUninitBytes 4`) and `lean-miri`
   preserves `InitMask.new (translateSizeBytes 4) false` on `_1`'s 4-byte allocation;
2. `_4 = copy _1` copies the `[(); 4]`-initialized union in lockstep, preserving
   `lm24PUZstSlot` in Anneal and `InitMask.new (translateSizeBytes 4) false` in
   `_4`'s allocation in `lean-miri`;
3. `_6 = copy (_4.0: [(); 4])` reads the inhabited `[(); 4]` ZST arm from `_4`,
   succeeding in both Anneal (`zstArrayVal 4`) and `lean-miri`
   even though all 4 bytes of `_4` are uninitialized;
4. `_2 = copy (_4.1: u8)` reads the uninitialized `u8` payload arm of `_4`,
   faulting with `.ub` in both Anneal and `lean-miri`. -/
theorem lm24_padded_zst_agg_copy_read_zst_and_payload_ub_steps :
    let s₀ := lm24PUInitAnneal 0
    let s₁ := lm24PUAnnealState 0 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₂ := lm24PUAnnealState 0 2
      [.uninit, lm24PUZstSlot, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₃ := lm24PUAnnealState 0 3
      [.uninit, lm24PUZstSlot, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .step s₃ ∧
    stepMirFn lm24PUBody s₃ = .fail .ub ∧
    encodeByLayoutIdxAux 8 lm24PULayouts lm24PUTy.layoutIdx
      (.aggregate 0 [.unit, .unit, .unit, .unit]) = some (replicateUninitBytes 4) ∧
    ∃ m₁ m₂ m₃ m₄ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 0) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₂).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₃ =
        (m₄, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₃).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, lm24PUMiriAt 0 1, lm24PUMiriAt 0 2, lm24PUMiriAt 0 3, _,
    ?_, lm24PU_bb0_step1.1, lm24PU_bb0_step1.2, ?_, ?_, Prod.ext rfl ?_, ?_⟩
  all_goals with_unfolding_all rfl

/-- Kernel-checked multi-step execution of `bb1` in `lm24PUBody` under BOTH
unmodified `annealStepHooksLM2_4` and `annealStepHooksLM2_4PaddedZst`:
1. `_1.0 = copy _5` writes the `[(); 4]` ZST arm into uninitialized `_1` via
   `uninitFieldWriteShell?` + `writeProjectedForLocal` in Anneal (`lm24PUZstSlot`)
   and `annealEvalUnionFieldPlace` + 0-byte `annealMemCopyOp` in `lean-miri`;
2. `_4 = move _1` moves the `[(); 4]`-initialized union into `_4`, deinitializing
   `_1` and copying `InitMask.new (translateSizeBytes 4) false` into `_4`;
3. `_3 = copy (_4.2: u32)` reads the uninitialized `u32` payload arm of `_4`,
   faulting with `.ub` in both Anneal and `lean-miri`. -/
theorem lm24_padded_zst_field_write_move_and_u32_ub_steps :
    let s₀ := lm24PUInitAnneal 1
    let s₁ := lm24PUAnnealState 1 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₂ := lm24PUAnnealState 1 2
      [.uninit, .uninit, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .fail .ub ∧
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 1) = (m₁, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 1)).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₂).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨rfl, rfl, rfl, lm24PUMiriAt 1 1, lm24PUMovedMiri1 2, _,
    ?_, ?_, lm24PU_bb1_step1.1, lm24PU_bb1_step1.2, Prod.ext rfl ?_, ?_⟩
  all_goals with_unfolding_all rfl

/-- Kernel-checked 5-step execution of `bb2` in `lm24PUBody` under BOTH
`annealStepHooksLM2_4` and `annealStepHooksLM2_4PaddedZst`:
1. `_1 = PU { a: 0x55_u8 }` initializes byte `0` to `0x55` and leaves trailing
   padding bytes `[1, 4)` uninitialized;
2. `_1.0 = copy _5` overwrites `_1` with the 0-byte `[(); 4]` ZST arm, setting
   typed slots to `[.unit, .unit, .unit, .unit]` and attaching the raw-byte
   overlay `lm24PUZstOverU8Slot 0x55` in Anneal while preserving byte `0 = 0x55`
   and `[1, 4)` uninitialized in `lean-miri`;
3. `_6 = copy (_1.0: [(); 4])` reads the `[(); 4]` ZST arm, succeeding in both;
4. `_2 = copy (_1.1: u8)` reads back `0x55_u8` from the retained byte `0` in both;
5. `_3 = copy (_1.2: u32)` reads the wider `u32` arm whose trailing bytes `[1, 4)`
   are uninitialized, faulting with `.ub` in both machines. -/
theorem lm24_padded_zst_overwrite_payload_retains_bytes_steps :
    let s₀ := lm24PUInitAnneal 2
    let s₁ := lm24PUAnnealState 2 1
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₂ := lm24PUAnnealState 2 2
      [.uninit, lm24PUZstOverU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₃ := lm24PUAnnealState 2 3
      [.uninit, lm24PUZstOverU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let s₄ := lm24PUAnnealState 2 4
      [.uninit, lm24PUZstOverU8Slot 0x55, .init (.scalar ⟨0x55, 1⟩), .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .step s₃ ∧
    stepMirFn lm24PUBody s₃ = .step s₄ ∧
    stepMirFn lm24PUBody s₄ = .fail .ub ∧
    ∃ m₁ m₂ m₃ m₄ m₅ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 2) = (m₁, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 2)).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₂).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₃).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₄ =
        (m₅, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₄).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, _, _, _, _, _,
    Prod.ext rfl ?_, ?_, Prod.ext rfl ?_, ?_, Prod.ext rfl ?_, ?_,
    Prod.ext rfl ?_, ?_, Prod.ext rfl ?_, ?_⟩
  all_goals with_unfolding_all rfl

set_option maxRecDepth 200000 in
/-- Kernel-checked 3-step execution of `bb3` in `lm24PUBody` under
`annealStepHooksLM2_4PaddedZst` (the pinned `annealStepHooksLM2_4` supports
neither the `[(); 4]` aggregate nor the `ConstantIndex` read):
1. `_1 = PU { z: copy _5 }` constructs `PU` via its `[(); 4]` ZST arm;
2. `_7 = copy (_1.0[2 of 4]: ())` reads in-bounds ZST element `2 < 4`, succeeding
   in both Anneal (`zstUnitVal`) and `lean-miri` (the union's place at the
   zero-sized `()` layout);
3. `_7 = copy (_1.0[4 of 4]: ())` faults with `.ub` in both Anneal and
   `lean-miri`. Its projection has `offset = min_length`, which rustc never
   emits, so this step checks agreement on an ill-formed projection only. -/
theorem lm24_padded_zst_elem_index_and_oob_ub_steps :
    let s₀ := lm24PUInitAnneal 3
    let s₁ := lm24PUAnnealState 3 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₂ := lm24PUAnnealState 3 2
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .init zstUnitVal, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .fail .ub ∧
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 3) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "out-of-bounds union ZST array index")) := by
  let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
  let m₁ := lm24PUMiriAt 3 1
  let m₂ := lm24PUMiriAt 3 2
  let m₃ := (Miri.Interpreter.Step.step hooks () m₂).1
  exact ⟨rfl, rfl, rfl, m₁, m₂, m₃,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    miri_step_eq hooks m₂ _ (by with_unfolding_all rfl)⟩

set_option maxRecDepth 200000 in
/-- Kernel-checked negative control (`bb4` in `lm24PUBody`, `kani#5159`) and
storage lifecycle (`bb5` in `lm24PUBody`):
1. In `bb4`, `_1 = PU { b: 0x01020304_u32 }` initializes all 4 bytes of `_1`,
   and reading the uninhabited 0-byte field `_8 = copy (_1.3: VoidZst)` faults
   with `.ub` in Anneal (`tyIsUninhabited = true`) and in `lean-miri` under
   `annealStepHooksLM2_4PaddedZst`. The fault comes from that adapter's
   `isUninhabitedEncodedTyId` check: the pinned `annealStepHooksLM2_4` accepts
   the same read (`lm24_padded_zst_uninhabited_arm_base_adapter_accepts`);
2. In `bb5`, `_1 = PU { z: copy _5 }`, `StorageDead(_1)`, and `StorageLive(_1)`
   step in lockstep (freeing `_1`'s 4-byte allocation and re-activating `_1` as
   an uninitialized immediate), after which `_6 = copy (_1.0: [(); 4])` on the
   uninitialized union `_1` faults with `.ub` in both machines. -/
theorem lm24_padded_zst_uninhabited_arm_ub_and_lifecycle_steps :
    let s4₀ := lm24PUInitAnneal 4
    let s4₁ := lm24PUAnnealState 4 1
      [.uninit, lm24PUU32Slot 0x01020304, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s5₀ := lm24PUInitAnneal 5
    let s5₁ := lm24PUAnnealState 5 1
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s5₂ := lm24PUAnnealState 5 2
      [.uninit, .dead, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s5₃ := lm24PUAnnealState 5 3
      [.uninit, .uninit, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    stepMirFn lm24PUBody s4₀ = .step s4₁ ∧
    stepMirFn lm24PUBody s4₁ = .fail .ub ∧
    stepMirFn lm24PUBody s5₀ = .step s5₁ ∧
    stepMirFn lm24PUBody s5₁ = .step s5₂ ∧
    stepMirFn lm24PUBody s5₂ = .step s5₃ ∧
    stepMirFn lm24PUBody s5₃ = .fail .ub ∧
    ∃ m4₁ m4₂ m5₁ m5₂ m5₃ m5₄ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 4) = (m4₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m4₁ =
        (m4₂, .error (.undefinedBehavior "read of uninhabited union field")) ∧
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 5) = (m5₁, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m5₁ = (m5₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m5₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m5₂ = (m5₃, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m5₂).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m5₃ =
        (m5₄, .error (.undefinedBehavior "field read of uninitialized union")) ∧
      (Miri.Interpreter.Step.step hooks_base () m5₃).2 =
        .error (.undefinedBehavior "field read of uninitialized union") := by
  let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
  let m4₁ := (Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 4)).1
  let m4₂ := (Miri.Interpreter.Step.step hooks () m4₁).1
  let m5₁ := lm24PUMiriAt 5 1
  let m5₂ : AnnealStepState :=
    { stack := ⟨#[{ lm24PUInitMiriFrame 5 with
        locals := (lm24PUInitMiriFrame 5).locals.set! 1
          { value := .dead, layout := some (translateTy lm24PUTy lm24PULayouts) },
        location := .mir ⟨5, 2⟩ }]⟩
      machine := { lm24PUMachine with memory := deallocLocalMemory lm24PUMachine.memory (.live (.indirect lm24BaseMemPlace)) } }
  let m5₃ : AnnealStepState :=
    { stack := ⟨#[{ lm24PUInitMiriFrame 5 with
        locals := (lm24PUInitMiriFrame 5).locals.set! 1
          { value := .live (.immediate .uninit), layout := some (translateTy lm24PUTy lm24PULayouts) },
        location := .mir ⟨5, 3⟩ }]⟩
      machine := { lm24PUMachine with memory := deallocLocalMemory lm24PUMachine.memory (.live (.indirect lm24BaseMemPlace)) } }
  let m5₄ := (Miri.Interpreter.Step.step hooks () m5₃).1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, m4₁, m4₂, m5₁, m5₂, m5₃, m5₄,
    miri_step_eq hooks (lm24PUInitMiri 4) _ (by with_unfolding_all rfl),
    miri_step_eq hooks m4₁ _ (by with_unfolding_all rfl),
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    miri_step_eq hooks m5₃ _ (by with_unfolding_all rfl),
    by with_unfolding_all rfl⟩

/-- The pinned adapter `annealStepHooksLM2_4` accepts the read of the
uninhabited field `_8 = copy (_1.3: VoidZst)` in `bb4`: it copies the 0-byte
field without validation, and the step succeeds. Anneal faults there
(`lm24_padded_zst_uninhabited_arm_ub_and_lifecycle_steps`), and so does rustc's
validated typed copy, which rejects a value of a type without variants
("zero-variant enum value" in the vendored `ValidityVisitor.lean`). The
`lean-miri` fault in that witness therefore comes from
`annealStepHooksLM2_4PaddedZst`'s `isUninhabitedEncodedTyId` check, not from
the pinned adapter. -/
theorem lm24_padded_zst_uninhabited_arm_base_adapter_accepts :
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 4)).2 = .ok true ∧
    (Miri.Interpreter.Step.step hooks_base ()
        (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 4)).1).2 = .ok true :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-! ### `lm24PUInit_stateRel`, Partially Initialized Whole-Copy Witness (`bb6`), and General Step Theorems (`G3`) -/

theorem lm24PU_uninitMem1 :
    PaddedZstUnionUninitMemRel lm24PUMachine lm24PUTy lm24PULayouts 4 lm24BaseMemPlace :=
  .mk witnessAllocId witnessTag witnessBaseAddr
    { kind := .stack, allocation := lm24PUUninitAlloc4 }
    rfl rfl rfl (List.Mem.head _) (by with_unfolding_all rfl) rfl (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem lm24PU_uninitMem4 :
    PaddedZstUnionUninitMemRel lm24PUMachine lm24PUTy lm24PULayouts 4 lm24Arr2MemPlace :=
  .mk lm24SecondAllocId witnessTag lm24SecondBaseAddr
    { kind := .stack, allocation := lm24PUUninitAlloc4 }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.head _)) (by with_unfolding_all rfl) rfl (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem lm24PU_zstMem5 : ZstZeroMemRel lm24PUMachine lm24ThirdMemPlace :=
  .mk lm24ThirdAllocId witnessTag lm24ThirdBaseAddr
    { kind := .stack, allocation := lm24ZstArr4Alloc }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (by with_unfolding_all rfl) rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem lm24PU_zstMem6 : ZstZeroMemRel lm24PUMachine lm24FourthMemPlace :=
  .mk lm24FourthAllocId witnessTag lm24FourthBaseAddr
    { kind := .stack, allocation := lm24ZstArr4Alloc }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    (by with_unfolding_all rfl) rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

/-- **Initial state relation (`G3`)**: for every block `b`, `lm24PUInitAnneal b`
and `lm24PUInitMiri b` satisfy `StateRelLM2_4PaddedZst lm24PUBody`. -/
theorem lm24PUInit_stateRel (b : Nat) :
    StateRelLM2_4PaddedZst lm24PUBody (lm24PUInitAnneal b) (lm24PUInitMiri b) := by
  refine .mk (lm24PUInitMiriFrame b) rfl rfl ⟨_, rfl⟩
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
    rfl rfl rfl rfl rfl ?_
  · intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 | 7 | 8 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .ofUnionLocalRel _ _ (.base _ _
        (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm) (.inl ⟨rfl, rfl⟩)))
    | 1 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .uninitIndirect 4 4 4 0 2 lm24BaseMemPlace _
        (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl lm24PU_uninitMem1
    | 4 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .uninitIndirect 4 4 4 0 2 lm24Arr2MemPlace _
        (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl lm24PU_uninitMem4
    | 5 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .zstArrayIndirect 4 (.init (zstArrayVal 4)) lm24ThirdMemPlace _
        (fun l hl => (Option.some.inj hl).symm) rfl rfl (.inr rfl) lm24PU_zstMem5
    | 6 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .zstArrayIndirect 4 .uninit lm24FourthMemPlace _
        (fun l hl => (Option.some.inj hl).symm) rfl rfl (.inl rfl) lm24PU_zstMem6
    | k + 9 =>
      change (none : Option LocalDecl) = some decl at hdecl
      cases hdecl
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    match i, j with
    | 1, 1 | 4, 4 | 5, 5 | 6, 6 => exact absurd rfl hij
    | 1, 4 | 1, 5 | 1, 6 | 4, 1 | 4, 5 | 4, 6 | 5, 1 | 5, 4 | 5, 6 | 6, 1 | 6, 4 | 6, 5 =>
      injection hi with hi; injection hi with hvi _; injection hvi with hvi; injection hvi with hvi
      injection hj with hj; injection hj with hvj _; injection hvj with hvj; injection hvj with hvj
      subst hvi hvj
      decide
    | 0, _ | 2, _ | 3, _ | 7, _ | 8, _ => cases hi
    | _, 0 | _, 2 | _, 3 | _, 7 | _, 8 => cases hj
    | k + 9, _ =>
      have hsz : (lm24PUInitMiriFrame b).locals.size = 9 := rfl
      have hlt := (Array.getElem?_eq_some_iff.mp hi).1
      rw [hsz] at hlt; omega
    | _, k + 9 =>
      have hsz : (lm24PUInitMiriFrame b).locals.size = 9 := rfl
      have hlt := (Array.getElem?_eq_some_iff.mp hj).1
      rw [hsz] at hlt; omega

/-- Partially initialized `4`-byte `PU` allocation after `_1 = PU { a: 0x55_u8 }`
in `bb6`: byte `0` holds `0x55` (initialized) and bytes `[1, 4)` are uninitialized. -/
def lm24PUU8Alloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeBytes Miri.ABI.Size.ZERO #[0x55]
      (Miri.ABI.Size.ofBytes 8) lm24PUUninitAlloc4 with
  | .ok () a => a
  | .error _ a => a

/-- Destination `4`-byte `PU` allocation after `_4 = copy _1` copies
`lm24PUU8Alloc4` into `lm24PUUninitAlloc4` (`union_copy_freshAlloc_spec`). -/
def lm24PUU8CopiedAlloc4 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeUninit
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 1) (Miri.ABI.Size.ofBytes 3))
      (Miri.ABI.Size.ofBytes 8)
      ((extractExceptOk
        (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[0x55, 0, 0, 0]
          (translateAlignBytes 4) .Mut)
        (by with_unfolding_all rfl)).withExtra none) with
  | .ok () a => a
  | .error _ a => a

private theorem lm24PU_copy_u8Alloc4_eq :
    Miri.Memory.Allocation.copy lm24PUU8Alloc4
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true lm24PUUninitAlloc4 =
    .ok () lm24PUU8CopiedAlloc4 := by
  obtain ⟨dest', hcopy, hsz, _, hal, hmut, hprov, hmask, _, hex, hnat, hraw⟩ :=
    union_copy_freshAlloc_spec (src := lm24PUU8Alloc4) (dest := lm24PUUninitAlloc4)
      (S := 4) (k := 1) (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (by decide)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (Or.inl (by with_unfolding_all rfl)) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  rw [hcopy]
  congr 1
  exact allocation_eq_of_parts
    (hraw.trans (by with_unfolding_all rfl))
    (hsz.trans (by with_unfolding_all rfl))
    (hprov.trans (by with_unfolding_all rfl))
    (hmask.trans (by with_unfolding_all rfl))
    (hal.trans (by with_unfolding_all rfl))
    (hmut.trans (by with_unfolding_all rfl))
    (hex.trans (by with_unfolding_all rfl))
    (hnat.trans (by with_unfolding_all rfl))

def lm24PUBb6Machine1 : AnnealMachine :=
  { lm24PUMachine with
    memory :=
      { lm24PUMachine.memory with
        live := #[(witnessAllocId, { kind := .stack, allocation := lm24PUU8Alloc4 }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }),
                  (lm24ThirdAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc }),
                  (lm24FourthAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc })] } }

def lm24PUBb6Machine2 : AnnealMachine :=
  { lm24PUMachine with
    memory :=
      { lm24PUMachine.memory with
        live := #[(witnessAllocId, { kind := .stack, allocation := lm24PUU8Alloc4 }),
                  (lm24SecondAllocId, { kind := .stack, allocation := lm24PUU8CopiedAlloc4 }),
                  (lm24ThirdAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc }),
                  (lm24FourthAllocId, { kind := .stack, allocation := lm24ZstArr4Alloc })] } }

def lm24PUBb6Miri1 : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame 6 with location := .mir ⟨6, 1⟩ }]⟩,
    machine := lm24PUBb6Machine1 }

def lm24PUBb6Miri2 (k : Nat) : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame 6 with location := .mir ⟨6, k⟩ }]⟩,
    machine := lm24PUBb6Machine2 }

private theorem lm24PU_bb6_step1 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri1 = (lm24PUBb6Miri2 2, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri1).2 = .ok true := by
  let f1 := { lm24PUInitMiriFrame 6 with location := .mir ⟨6, 1⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 4 none (.ofAllocationToken 0), translateTy lm24PUTy lm24PULayouts⟩
  have hf4 : annealForceUnionAllocation lm24PUBody.localDecls lm24PUBody.layouts destPlace
      lm24PUBb6Miri1 =
      .ok ⟨lm24Arr2MemPlace, translateTy lm24PUTy lm24PULayouts⟩ lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have hfind_src : lm24PUBb6Machine1.memory.live.find? (fun (k, _) => k == witnessAllocId) =
      some (witnessAllocId, { kind := .stack, allocation := lm24PUU8Alloc4 }) := by
    with_unfolding_all rfl
  have hfind_dst : lm24PUBb6Machine1.memory.live.findIdx? (fun (k, _) => k == lm24SecondAllocId) =
      some 1 := by
    with_unfolding_all rfl
  have hbase_src : lm24PUBb6Machine1.lookupBaseAddr witnessAllocId = some witnessBaseAddr := by
    with_unfolding_all rfl
  have hbase_dst : lm24PUBb6Machine1.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
    with_unfolding_all rfl
  have hneq : (witnessAllocId == lm24SecondAllocId) = false := by decide
  have hmc : annealMemCopyOp lm24PUBody.localDecls lm24PUBody.layouts
      ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩
      destPlace lm24PUBb6Miri1 =
    .ok () { stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 } := by
    unfold annealMemCopyOp
    dsimp only []
    rw [EStateM.bind_eq_ok hf4]
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      lm24BaseMemPlace, lm24Arr2MemPlace, Option.bind, Miri.Memory.Provenance.getAllocId,
      lm24PUBb6Miri1]
    rw [hbase_src, hfind_src, hbase_dst, hfind_dst]
    dsimp only []
    have hget1 : lm24PUBb6Machine1.memory.live[1]? =
        some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUUninitAlloc4 }) := rfl
    rw [hget1]
    dsimp only []
    have hoff1 :
        Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes witnessBaseAddr).bytes - witnessBaseAddr) =
          Miri.ABI.Size.ZERO := rfl
    have hoff2 :
        Miri.ABI.Size.ofBytes
          ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
          Miri.ABI.Size.ZERO := rfl
    have hlay_sz : (translateTy lm24PUTy lm24PULayouts).layout.size = translateSizeBytes 4 := rfl
    dsimp only [destPlace]
    simp only [hoff1, hoff2, hlay_sz, hneq, lm24PU_copy_u8Alloc4_eq]
    rfl
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true lm24PUBb6Miri1 = .ok destPlace lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri1 =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand") (translateOperand (.copy (local_ 1)))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri1 =
    .ok ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ lm24PUBb6Miri1 := by
    with_unfolding_all rfl
  have huse : usesMemCopy ⟨.indirect lm24BaseMemPlace, translateTy lm24PUTy lm24PULayouts⟩ = true := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ lm24PUBb6Miri1 =
    .ok () { stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 } := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy (local_ 1)))) ⟨4, #[]⟩ lm24PUBb6Miri1 =
    .ok () { stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 } := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨4, #[]⟩ true lm24PUBb6Miri1 = .ok destPlace lm24PUBb6Miri1 from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, huse, ↓reduceIte]
    exact hmc
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨4, #[]⟩
      (translateRvalue (.use (.copy (local_ 1)))) = true := rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      lm24PUBb6Miri1 = ({ stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 }, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) lm24PUBb6Miri1 = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 4) (.use (.copy (local_ 1))))))
      lm24PUBb6Miri1 = ({ stack := ⟨#[f1]⟩, machine := lm24PUBb6Machine2 }, .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨4, #[]⟩ (translateRvalue (.use (.copy (local_ 1)))) lm24PUBb6Miri1 = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f1) (topFrame' := f1)
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 1) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f1) (topFrame' := f1)
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 1) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

def lm24PUU8Msc55 : Miri.Memory.ScalarInt :=
  extractExceptOk (translateScalarInt ⟨0x55, 1⟩) (by with_unfolding_all rfl)

private theorem lm24PUU8CopiedAlloc4_readScalar_u8 :
    lm24PUU8CopiedAlloc4.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) false =
    .ok (.fromScalarInt lm24PUU8Msc55) := by
  have hmask : lm24PUU8CopiedAlloc4.initializationMask = unionCopiedPrefixMask 4 1 := by
    with_unfolding_all rfl
  have hinit : lm24PUU8CopiedAlloc4.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) = .ok (.ok ()) := by
    rw [hmask]
    exact (IsUnionPrefixMask.of_copied 4 1).init (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inl rfl) (by decide) (by decide)
  exact union_readScalar_prefix (sc := ⟨0x55, 1⟩)
    ⟨Or.inl rfl, by decide, by decide, by with_unfolding_all rfl⟩
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by decide) (by decide)
    hinit (by with_unfolding_all rfl)

private theorem lm24PUU8CopiedAlloc4_readScalar_u32 :
    ∃ bad, lm24PUU8CopiedAlloc4.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) false =
    .error (.invalidUninitBytes (some ⟨Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4), bad⟩)) := by
  have hmask : lm24PUU8CopiedAlloc4.initializationMask = unionCopiedPrefixMask 4 1 := by
    with_unfolding_all rfl
  obtain ⟨bad, hbad⟩ : ∃ bad, lm24PUU8CopiedAlloc4.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) = .ok (.error bad) := by
    rw [hmask]
    exact (IsUnionPrefixMask.of_copied 4 1).uninit (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
  exact ⟨bad, union_readScalar_uninit hbad⟩

def lm24PUBb6Miri4 : AnnealStepState :=
  { stack := ⟨#[{ lm24PUInitMiriFrame 6 with
      locals := (lm24PUInitMiriFrame 6).locals.set! 2
        { value := .live (.immediate (.scalar (.fromScalarInt lm24PUU8Msc55))),
          layout := some (translateTy lm24U8Ty lm24PULayouts) },
      location := .mir ⟨6, 4⟩ }]⟩,
    machine := lm24PUBb6Machine2 }

private theorem lm24PU_bb6_step3 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUBb6Miri2 3) = (lm24PUBb6Miri4, .ok true) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUBb6Miri2 3)).2 = .ok true := by
  let f3 := { lm24PUInitMiriFrame 6 with location := .mir ⟨6, 3⟩ }
  let f3' := { lm24PUInitMiriFrame 6 with
      locals := (lm24PUInitMiriFrame 6).locals.set! 2
        { value := .live (.immediate (.scalar (.fromScalarInt lm24PUU8Msc55))),
          layout := some (translateTy lm24U8Ty lm24PULayouts) },
      location := .mir ⟨6, 3⟩ }
  let m3' : AnnealStepState := { stack := ⟨#[f3']⟩, machine := lm24PUBb6Machine2 }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 2 none (.ofAllocationToken 0), translateTy lm24U8Ty lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨2, #[]⟩ true (lm24PUBb6Miri2 3) = .ok destPlace (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 1 lm24U8Ty]⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUBb6Miri2 3) =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 1 lm24U8Ty]⟩))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      (lm24PUBb6Miri2 3) =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) := by
    with_unfolding_all rfl
  have hread : annealReadImmediateLM2_2
      ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ (lm24PUBb6Miri2 3) =
    .ok ⟨.scalar (.fromScalarInt lm24PUU8Msc55), translateTy lm24U8Ty lm24PULayouts⟩
      (lm24PUBb6Miri2 3) := by
    have hfind : lm24PUBb6Machine2.memory.live.find? (fun (k, _) => k == lm24SecondAllocId) =
        some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUU8CopiedAlloc4 }) := by
      with_unfolding_all rfl
    have hbase : lm24PUBb6Machine2.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
      with_unfolding_all rfl
    have hrel0 : Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
    have hsz0 : ((translateTy lm24U8Ty lm24PULayouts).layout.size == Miri.ABI.Size.ZERO) = false := rfl
    have hfields_sc : (translateTy lm24U8Ty lm24PULayouts).layout.fields = .Primitive := rfl
    have hsz_sc : (translateTy lm24U8Ty lm24PULayouts).layout.size = translateSizeBytes 1 := rfl
    have hrepr : (translateTy lm24U8Ty lm24PULayouts).layout.backendRepr =
        .Scalar (.Initialized (value := .Int (translateAbiIntegerBytes 1) false)
          (validRange := { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * 1)) - 1) })) := rfl
    change annealReadIndirectImmediate lm24Arr2MemPlace
      (translateTy lm24U8Ty lm24PULayouts) (lm24PUBb6Miri2 3) = _
    unfold annealReadIndirectImmediate
    rw [show lm24Arr2MemPlace.ptr.provenance = some (.concrete lm24SecondAllocId witnessTag) from rfl,
      hfields_sc, hsz0, hrepr, hsz_sc]
    simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId,
      lm24PUBb6Miri2, hbase, hfind, lm24Arr2MemPlace, hrel0, lm24PUU8CopiedAlloc4_readScalar_u8,
      pure, EStateM.pure]
  have hwrite : annealWriteImmediateLM2_2 (.scalar (.fromScalarInt lm24PUU8Msc55))
      destPlace (lm24PUBb6Miri2 3) = .ok () m3' := by
    with_unfolding_all rfl
  have huse : usesMemCopy ⟨.indirect lm24Arr2MemPlace, translateTy lm24U8Ty lm24PULayouts⟩ = false := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) ⟨2, #[]⟩ (lm24PUBb6Miri2 3) =
    .ok () m3' := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      huse, Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok hread]
    exact hwrite
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) ⟨2, #[]⟩ (lm24PUBb6Miri2 3) =
    .ok () m3' := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨2, #[]⟩ true (lm24PUBb6Miri2 3) = .ok destPlace (lm24PUBb6Miri2 3) from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      huse, Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_eq_ok hread]
    exact hwrite
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨2, #[]⟩
      (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) = true := by
    with_unfolding_all rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩)))))
      (lm24PUBb6Miri2 3) = (m3', .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨2, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) (lm24PUBb6Miri2 3) = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 2) (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩)))))
      (lm24PUBb6Miri2 3) = (m3', .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨2, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 1 lm24U8Ty]⟩))) (lm24PUBb6Miri2 3) = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_ok
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f3) (topFrame' := f3')
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 3) rfl rfl hstmt rfl rfl
  · have h := miri_step_at_statement_ok
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f3) (topFrame' := f3')
      rfl rfl rfl (blockIdx := 6) (stmtIdx := 3) rfl rfl hstmt_base rfl rfl
    exact congrArg Prod.snd h

private theorem lm24PU_bb6_step4 :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri4 =
      (lm24PUBb6Miri4, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      lm24PUBb6Miri4).2 = .error (.undefinedBehavior "read of uninitialized memory field") := by
  let f4 := { lm24PUInitMiriFrame 6 with
      locals := (lm24PUInitMiriFrame 6).locals.set! 2
        { value := .live (.immediate (.scalar (.fromScalarInt lm24PUU8Msc55))),
          layout := some (translateTy lm24U8Ty lm24PULayouts) },
      location := .mir ⟨6, 4⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 3 none (.ofAllocationToken 0), translateTy lm24U32Ty lm24PULayouts⟩
  have hplace : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨3, #[]⟩ true lm24PUBb6Miri4 = .ok destPlace lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  have hop : (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 2 lm24U32Ty]⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri4 =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  have hop_base : (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨4, [.field 2 lm24U32Ty]⟩))
      (some ((annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).placeLayout destPlace))
      lm24PUBb6Miri4 =
    .ok ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 := by
    with_unfolding_all rfl
  obtain ⟨bad, hread_sc⟩ := lm24PUU8CopiedAlloc4_readScalar_u32
  have hread : annealReadImmediateLM2_2
      ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ lm24PUBb6Miri4 =
    .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    have hfind : lm24PUBb6Machine2.memory.live.find? (fun (k, _) => k == lm24SecondAllocId) =
        some (lm24SecondAllocId, { kind := .stack, allocation := lm24PUU8CopiedAlloc4 }) := by
      with_unfolding_all rfl
    have hbase : lm24PUBb6Machine2.lookupBaseAddr lm24SecondAllocId = some lm24SecondBaseAddr := by
      with_unfolding_all rfl
    have hrel0 : Miri.ABI.Size.ofBytes
        ((Miri.ABI.Size.ofBytes lm24SecondBaseAddr).bytes - lm24SecondBaseAddr) =
        Miri.ABI.Size.ZERO := rfl
    have hsz0 : ((translateTy lm24U32Ty lm24PULayouts).layout.size == Miri.ABI.Size.ZERO) = false := rfl
    have hfields_sc : (translateTy lm24U32Ty lm24PULayouts).layout.fields = .Primitive := rfl
    have hsz_sc : (translateTy lm24U32Ty lm24PULayouts).layout.size = translateSizeBytes 4 := rfl
    have hrepr : (translateTy lm24U32Ty lm24PULayouts).layout.backendRepr =
        .Scalar (.Initialized (value := .Int (translateAbiIntegerBytes 4) false)
          (validRange := { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * 4)) - 1) })) := rfl
    change annealReadIndirectImmediate lm24Arr2MemPlace
      (translateTy lm24U32Ty lm24PULayouts) lm24PUBb6Miri4 = _
    unfold annealReadIndirectImmediate
    rw [show lm24Arr2MemPlace.ptr.provenance = some (.concrete lm24SecondAllocId witnessTag) from rfl,
      hfields_sc, hsz0, hrepr, hsz_sc]
    simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId,
      lm24PUBb6Miri4, hbase, hfind, lm24Arr2MemPlace, hrel0, hread_sc,
      throw, throwThe]
    rfl
  have huse : usesMemCopy ⟨.indirect lm24Arr2MemPlace, translateTy lm24U32Ty lm24PULayouts⟩ = false := rfl
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) ⟨3, #[]⟩ lm24PUBb6Miri4 =
    .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hplace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    simp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      huse, Bool.false_eq_true, ↓reduceIte]
    exact EStateM.bind_eq_error hread
  have hrv_base : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) ⟨3, #[]⟩ lm24PUBb6Miri4 =
    .error (.undefinedBehavior "read of uninitialized memory field") lm24PUBb6Miri4 := by
    unfold Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok (show (annealRvalueHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).evalPlace ()
      ⟨3, #[]⟩ true lm24PUBb6Miri4 = .ok destPlace lm24PUBb6Miri4 from hplace)]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop_base]
    simp only [annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      huse, Bool.false_eq_true, ↓reduceIte]
    exact EStateM.bind_eq_error hread
  have hlm24 : lm24Assign lm24PUBody.localDecls lm24PUBody.layouts ⟨3, #[]⟩
      (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) = true := by
    with_unfolding_all rfl
  have hstmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))))
      lm24PUBb6Miri4 =
      (lm24PUBb6Miri4, .error (.undefinedBehavior "read of uninitialized memory field")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨3, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) lm24PUBb6Miri4 = _
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv]
  have hstmt_base : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts) ()
      (translateStmt (mkStmt (.assign (local_ 3) (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩)))))
      lm24PUBb6Miri4 =
      (lm24PUBb6Miri4, .error (.undefinedBehavior "read of uninitialized memory field")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [mkStmt, translateStmtKind]
    change (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts).assign ()
      ⟨3, #[]⟩ (translateRvalue (.use (.copy ⟨4, [.field 2 lm24U32Ty]⟩))) lm24PUBb6Miri4 = _
    simp only [annealStepHooksLM2_4, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue
    rw [hrv_base]
  refine ⟨?_, ?_⟩
  · exact miri_step_at_statement_error
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f4) rfl rfl rfl (blockIdx := 6) (stmtIdx := 4) rfl rfl hstmt
  · have h := miri_step_at_statement_error
      (annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts)
      (topFrame := f4) rfl rfl rfl (blockIdx := 6) (stmtIdx := 4) rfl rfl hstmt_base
    exact congrArg Prod.snd h
/-- **Kernel-checked 5-step execution of `bb6` in `lm24PUBody` (`G3`: partially
initialized padded-union whole copy + `[(); 4][2 of 4]` read on partially
initialized storage + `u8` read + `u32` read UB)**:
1. `_1 = PU { a: 0x55_u8 }` initializes byte `0` of `_1` to `0x55`, leaving
   bytes `[1, 4)` uninitialized;
2. `_4 = copy _1` copies the partially initialized `PU` into `_4`
   (`lm24PU_copy_u8Alloc4_eq`, preserving byte `0 = 0x55` and bytes `[1, 4)`
   uninitialized in `lean-miri`'s `InitMask`);
3. `_7 = copy (_4.0[2 of 4]: ())` reads element `2 < 4` of the `[(); 4]` ZST arm
   on partially initialized `_4`, succeeding in both Anneal (`zstUnitVal`) and
   `lean-miri`;
4. `_2 = copy (_4.1: u8)` reads back `0x55_u8` from byte `0` of `_4` in both;
5. `_3 = copy (_4.2: u32)` reads the wider `u32` arm of `_4` across uninitialized
   bytes `[1, 4)`, faulting with `.ub` in both machines. -/
theorem lm24_padded_zst_partial_init_whole_copy_and_elem_index_steps :
    let s₀ := lm24PUInitAnneal 6
    let s₁ := lm24PUAnnealState 6 1
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₂ := lm24PUAnnealState 6 2
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, lm24PUU8Slot 0x55,
       .init (zstArrayVal 4), .uninit, .uninit, .uninit]
    let s₃ := lm24PUAnnealState 6 3
      [.uninit, lm24PUU8Slot 0x55, .uninit, .uninit, lm24PUU8Slot 0x55,
       .init (zstArrayVal 4), .uninit, .init zstUnitVal, .uninit]
    let s₄ := lm24PUAnnealState 6 4
      [.uninit, lm24PUU8Slot 0x55, .init (.scalar ⟨0x55, 1⟩), .uninit, lm24PUU8Slot 0x55,
       .init (zstArrayVal 4), .uninit, .init zstUnitVal, .uninit]
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    StateRelLM2_4PaddedZst lm24PUBody s₀ (lm24PUInitMiri 6) ∧
    stepMirFn lm24PUBody s₀ = .step s₁ ∧
    stepMirFn lm24PUBody s₁ = .step s₂ ∧
    stepMirFn lm24PUBody s₂ = .step s₃ ∧
    stepMirFn lm24PUBody s₃ = .step s₄ ∧
    stepMirFn lm24PUBody s₄ = .fail .ub ∧
    ∃ m₁ m₂ m₃ m₄ m₅ : AnnealStepState,
      Miri.Interpreter.Step.step hooks () (lm24PUInitMiri 6) = (m₁, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () (lm24PUInitMiri 6)).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₁).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      (Miri.Interpreter.Step.step hooks_base () m₃).2 = .ok true ∧
      Miri.Interpreter.Step.step hooks () m₄ =
        (m₅, .error (.undefinedBehavior "read of uninitialized memory field")) ∧
      (Miri.Interpreter.Step.step hooks_base () m₄).2 =
        .error (.undefinedBehavior "read of uninitialized memory field") := by
  refine ⟨lm24PUInit_stateRel 6, rfl, rfl, rfl, rfl, rfl,
    lm24PUBb6Miri1, lm24PUBb6Miri2 2, lm24PUBb6Miri2 3, lm24PUBb6Miri4, lm24PUBb6Miri4,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    lm24PU_bb6_step1.1,
    lm24PU_bb6_step1.2,
    by with_unfolding_all rfl,
    lm24PU_bb6_step3.1,
    lm24PU_bb6_step3.2,
    lm24PU_bb6_step4.1,
    lm24PU_bb6_step4.2⟩

/-! ### General Step Simulation Theorems for Padded ZST Unions (`G3`) -/

/-- **`lean-miri` side of an uninhabited union field read (`G3`, `kani#5159`)**:
For any `StateRelLM2_4PaddedZst body s m` and statement
`⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩` whose field
type encodes as uninhabited (`isUninhabitedEncodedTyId (encodeTyId voidTy)`),
with `r ≠ u` and the union local `u` memory-backed (`.live (.indirect mp_u)`),
`Step.step (annealStepHooksLM2_4PaddedZst ..) () m` faults with
"read of uninhabited union field". Anneal's fault is the hypothesis `hstep_a`,
not a conclusion; the concrete witness
`lm24_padded_zst_uninhabited_arm_ub_and_lifecycle_steps` evaluates it on
`lm24PUBody`. Given `hstep_a`, the two steps are related by
`StepRelLM2_4PaddedZst.ub`. -/
theorem step_padded_zst_union_uninhabited_field_read_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    {bb : BasicBlockData} {r u j : Nat} {voidTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hun_u : isUnionLocal body.localDecls body.layouts u = true)
    (huninh_m : annealEvalOperandLM2_4PaddedZst.isUninhabitedEncodedTyId
      (encodeTyId voidTy) body.layouts = true)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hstep_a : stepMirFn body s = MirStepNode.fail .ub) :
    StepRelLM2_4PaddedZst body m (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _, _⟩
  obtain ⟨_, mls_r, _, hlt_r, _, _, hmls_r_eq, hloc_r⟩ := hframe.lookup_local hdecl_r
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
  obtain ⟨uC, hmls_u⟩ := hu_ind topFrame hframes
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_r := hloc_r.layout_eq
  have hcache_u := hloc_u.layout_eq
  let layR := translateTy rDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame r hlt_r layR
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, layR⟩
  have hevalPlace : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
      ⟨r, #[]⟩ true m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r hdecl_r (by rw [hmls_r_eq]; exact hcache_r)
  have hframes₀ : m₀.stack.frames = #[topFrame₀] := rfl
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), uC⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hru] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₀' : AnnealStepState := { m₀ with stack := ⟨#[topFrame₁]⟩ }
  have hres_u : annealResolveAndCacheLocalLayout body.localDecls body.layouts u none m₀ =
      .ok (topFrame₁, layU) m₀' :=
    annealResolveAndCacheLocalLayout_eq hframes₀ hlt_u₀ hdecl_u
      (by rw [hmls_u₀]; exact hcache_u)
  have hget_u₁ : topFrame₁.getLocalOperand u = .ok (.indirect mp_u) :=
    frame_getLocalOperand_live topFrame₁
      (by rw [cacheFrameLocalLayout_getLocal, hmls_u₀])
  have hop_err : ∀ known,
      annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
        (translateOperand (.copy ⟨u, [.field j voidTy]⟩)) known m₀ =
      .error (.undefinedBehavior "read of uninhabited union field") m₀' := by
    intro known
    unfold annealEvalOperandLM2_4PaddedZst
    dsimp only [translateOperand]
    rw [show (translatePlace ⟨u, [.field j voidTy]⟩).localId = u from rfl,
        show (translatePlace ⟨u, [.field j voidTy]⟩).projection.toList =
          [.Field j (encodeTyId voidTy)] from rfl]
    simp only [hun_u, ↓reduceIte, huninh_m, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, stack_currentFrame?_singleton m₀.stack topFrame₀ hframes₀,
      Option.isNone_some, Bool.false_eq_true, hres_u, hget_u₁]
    rfl
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
      (translateRvalue (.use (.copy ⟨u, [.field j voidTy]⟩))) = true := by
    simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
      translatePlace, hun_u]
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩) m =
      (m₀', .error (.undefinedBehavior "read of uninhabited union field")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace]
    dsimp only [translateRvalue, annealRvalueHooksLM2_4PaddedZst]
    rw [EStateM.bind_eq_error (hop_err _)]
  have hstep_m := miri_step_at_statement_error
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt
  rw [hstep_a, hstep_m]
  exact .ub m₀' "read of uninhabited union field"

/-- **`lean-miri` side of `[(); N][offset of minLen]` element reads (`G3`)**. As
in `step_padded_zst_union_uninhabited_field_read_ub`, Anneal's fault in item 1
is the hypothesis `hstep_a`, and item 2 states only the `lean-miri` operand
read:
For any `StateRelLM2_4PaddedZst body s m` (with `LiveAllocsNodup m.machine`) and
statement `⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩`
where `_u` is a memory-backed padded ZST union (`WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx`,
`unionZstArrayElemCount? body.layouts (encodeTyId zstArrTy) = some N`):
1. **Out-of-bounds (`(minLen ≤ N && offset < N) = false`)**:
   `Step.step (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m`
   returns `(m', .error (.undefinedBehavior "out-of-bounds union ZST array index"))`,
   and when `stepMirFn body s = MirStepNode.fail .ub`, satisfies `StepRelLM2_4PaddedZst.ub`;
2. **In-bounds (`(minLen ≤ N && offset < N) = true`)**:
   `annealEvalOperandLM2_4PaddedZst` evaluates the element read to
   `⟨.indirect mp_u, { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩`,
   and `annealReadImmediate_zstLayoutData` reads `Immediate.uninit` in 0 bytes
   without inspecting `mp_u`'s initialization mask! -/
theorem step_padded_zst_union_elem_index_read_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : BasicBlockData} {r u S n N f_z zstFlIdx offset minLen : Nat}
    {zstArrTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩
        (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hfz_lt : f_z < n)
    (hcnt : annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount?
      body.layouts (encodeTyId zstArrTy) = some N)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp_u.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) :
    ((decide (minLen ≤ N) && decide (offset < N)) = false →
      stepMirFn body s = MirStepNode.fail .ub →
      StepRelLM2_4PaddedZst body m (stepMirFn body s)
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m)) ∧
    ((decide (minLen ≤ N) && decide (offset < N)) = true →
      ∀ known,
        ∃ m',
          (do
            let opTy ← annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
              (translateOperand (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))
              known
            annealReadImmediateLM2_2 opTy) m =
          .ok ⟨.uninit,
            { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩ m') := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _, _⟩
  have hun_u : isUnionLocal body.localDecls body.layouts u = true :=
    isUnionLocal_of_wellTypedPaddedZst hdecl_u hwt
  obtain ⟨_, mls_r, _, hlt_r, _, _, hmls_r_eq, hloc_r⟩ := hframe.lookup_local hdecl_r
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
  obtain ⟨uC, hmls_u⟩ := hu_ind topFrame hframes
  rw [hmls_u] at hmls_u'
  injection hmls_u' with hmls_u'
  subst hmls_u'
  have hcache_r := hloc_r.layout_eq
  have hcache_u := hloc_u.layout_eq
  let layR := translateTy rDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame r hlt_r layR
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, layR⟩
  have hevalPlace : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
      ⟨r, #[]⟩ true m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r hdecl_r (by rw [hmls_r_eq]; exact hcache_r)
  have hframes₀ : m₀.stack.frames = #[topFrame₀] := rfl
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), uC⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hru] at h
    rw [hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₀' : AnnealStepState := { m₀ with stack := ⟨#[topFrame₁]⟩ }
  have hres_u : annealResolveAndCacheLocalLayout body.localDecls body.layouts u none m₀ =
      .ok (topFrame₁, layU) m₀' :=
    annealResolveAndCacheLocalLayout_eq hframes₀ hlt_u₀ hdecl_u
      (by rw [hmls_u₀]; exact hcache_u)
  have hget_u₁ : topFrame₁.getLocalOperand u = .ok (.indirect mp_u) :=
    frame_getLocalOperand_live topFrame₁
      (by rw [cacheFrameLocalLayout_getLocal, hmls_u₀])
  refine ⟨fun hoob hstep_a => ?_, fun hinb known => ?_⟩
  · have hop_err : ∀ known,
        annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
          (translateOperand (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))
          known m₀ =
        .error (.undefinedBehavior "out-of-bounds union ZST array index") m₀' := by
      intro known
      unfold annealEvalOperandLM2_4PaddedZst
      dsimp only [translateOperand]
      rw [show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).localId = u from rfl,
          show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).projection.toList =
            [.Field f_z (encodeTyId zstArrTy), .ConstantIndex offset minLen false] from rfl]
      simp only [hun_u, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, stack_currentFrame?_singleton m₀.stack topFrame₀ hframes₀,
        Option.isNone_some, Bool.false_eq_true, hres_u, hget_u₁,
        layU, hfields, hfz_lt, hcnt, hoob]
      rfl
    have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
        (translateRvalue
          (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))) = true := by
      simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
        translatePlace, hun_u]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨r, .nil⟩
          (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩) m =
        (m₀', .error (.undefinedBehavior "out-of-bounds union ZST array index")) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
      simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
      unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
      rw [EStateM.bind_eq_ok hevalPlace]
      dsimp only [translateRvalue, annealRvalueHooksLM2_4PaddedZst]
      rw [EStateM.bind_eq_error (hop_err _)]
    have hstep_m := miri_step_at_statement_error
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
      hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt
    rw [hstep_a, hstep_m]
    exact .ub m₀' "out-of-bounds union ZST array index"
  · have hmls_u_eq : topFrame.locals[u]'hlt_u = ⟨.live (.indirect mp_u), uC⟩ := by
      have h0 := Array.getElem?_eq_getElem hlt_u
      rw [hmls_u] at h0; exact (Option.some.inj h0).symm
    let tf_u := cacheFrameLocalLayout topFrame u hlt_u layU
    let m_u : AnnealStepState := { m with stack := ⟨#[tf_u]⟩ }
    have hres_m : annealResolveAndCacheLocalLayout body.localDecls body.layouts u none m =
        .ok (tf_u, layU) m_u :=
      annealResolveAndCacheLocalLayout_eq hframes hlt_u hdecl_u
        (by rw [hmls_u_eq]; exact hcache_u)
    have hget_u : tf_u.getLocalOperand u = .ok (.indirect mp_u) :=
      frame_getLocalOperand_live tf_u
        (by rw [cacheFrameLocalLayout_getLocal, hmls_u_eq])
    have hop_ok : annealEvalOperandLM2_4PaddedZst body.localDecls body.layouts
        (translateOperand (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩))
        known m =
      .ok ⟨.indirect mp_u,
        { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 }, layout := zstLayoutData }⟩ m_u := by
      unfold annealEvalOperandLM2_4PaddedZst
      dsimp only [translateOperand]
      rw [show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).localId = u from rfl,
          show (translatePlace ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩).projection.toList =
            [.Field f_z (encodeTyId zstArrTy), .ConstantIndex offset minLen false] from rfl]
      simp only [hun_u, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, stack_currentFrame?_singleton m.stack topFrame hframes,
        Option.isNone_some, Bool.false_eq_true, hres_m, hget_u,
        layU, hfields, hfz_lt, hcnt, hinb, pure]
      rfl
    have hread := annealReadImmediate_zstLayoutData (m := m_u) hnodup
      (tyId := encodeTyId { kind := .tuple [], layoutIdx := 0 }) hprov hlive hbase
    refine ⟨m_u, ?_⟩
    simp only [bind, EStateM.bind]
    rw [hop_ok]
    exact hread

/-- **`lean-miri` side of a 0-byte `[(); N]` field write (`G3`)**: the memory
copy is a no-op, and the given Anneal slots relate to the unchanged memory
under `PaddedZstUnionLocalRel`. That Anneal's step produces those slots is not
proved here; the concrete witnesses `lm24_padded_zst_field_write_move_and_u32_ub_steps`
and `lm24_padded_zst_overwrite_payload_retains_bytes_steps` evaluate it:
Writing a 0-byte `[(); N]` ZST local `z` (`ZstZeroMemRel m.machine mp_z`,
`zLay.layout.size = Miri.ABI.Size.ZERO`) into field `f_z` (`fLay.layout.size = Miri.ABI.Size.ZERO`)
of a memory-backed union `u` (`ValidScalarBytes S`, either `PaddedZstUnionUninitMemRel`
for an uninitialized union `_u.f_z = copy _z`, or `UnionMemRel` for an initialized
union `_u.f_z = copy _z` producing the `D13a` raw-byte overlay `zstOverlay`)
via `annealMemCopyOp`:
1. In `lean-miri`, `annealMemCopyOp` succeeds in-place (`.ok () m`), preserving
   both `PaddedZstUnionUninitMemRel` (establishing `PaddedZstUnionLocalRel.zstUninit`)
   and `UnionMemRel` (establishing `PaddedZstUnionLocalRel.zstOverlay`);
2. In Anneal, when `_u` holds `.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))`
   (`UnionLocalRel.union`) or `.uninit` (`PaddedZstUnionLocalRel.uninitIndirect`),
   updating `_u`'s slot to `.init (.aggregate 0 (List.replicate n .unit))` (from `.uninit`)
   or `.init (.aggregate 0 (List.replicate n .unit ++ [.aggregate 0 (encodeRawAbstractByteVals (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++ replicateUninitBytes (S - sc.sizeBytes)))]))` (from `.init`)
   establishes `PaddedZstUnionLocalRel` (`zstUninit` and `zstOverlay`). -/
theorem step_padded_zst_union_field_write_and_overlay_rel
    {body : CapturedMir} {m : AnnealStepState}
    (hnodup : LiveAllocsNodup m.machine)
    {uDecl : LocalDecl} {S n N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    {mp_u mp_z : Miri.Interpreter.MemPlace AnnealProv}
    {cachedLayout : Option Miri.Interpreter.LocalLayout}
    (hc : ∀ l ∈ cachedLayout, l = translateTy uDecl.ty body.layouts)
    (hz : ZstZeroMemRel m.machine mp_z)
    {zLay fLay : Miri.Interpreter.LocalLayout}
    (hf0 : fLay.layout.size = Miri.ABI.Size.ZERO) :
    (PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u →
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_z, zLay⟩ ⟨.memory mp_u, fLay⟩ m =
        .ok () m ∧
      PaddedZstUnionLocalRel m.machine uDecl body.layouts
        (.init (.aggregate 0 (List.replicate n .unit)))
        ⟨.live (.indirect mp_u), cachedLayout⟩) ∧
    (∀ f0Ty sc,
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_z, zLay⟩ ⟨.memory mp_u, fLay⟩ m =
        .ok () m ∧
      PaddedZstUnionLocalRel m.machine uDecl body.layouts
        (.init (.aggregate 0
          (List.replicate n .unit ++
            [.aggregate 0
              (encodeRawAbstractByteVals
                (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
                  replicateUninitBytes (S - sc.sizeBytes)))])))
        ⟨.live (.indirect mp_u), cachedLayout⟩) := by
  cases hz with
  | mk srcAllocId srcTag srcBaseAddr srcLa hprov_z _ _ hlive_z hbase_z hptr_z hsz_z hlen_z _ =>
    have hlen_src : srcLa.allocation.len = srcLa.allocation.byteSize.bytes.toNat := by
      rw [hlen_z, hsz_z]; rfl
    refine ⟨fun hun => ?_, fun f0Ty sc hmem => ?_⟩
    · cases hun with
      | mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
        exact ⟨annealMemCopyOp_zero_into_union_field body.localDecls body.layouts hnodup
            hwt.size_valid hprov hlive hbase hptr hsz hlen hmut hprov_z hlive_z hbase_z hptr_z
            hlen_src hf0,
          .zstUninit S n N f_z zstFlIdx mp_u cachedLayout hc hwt hfields
            (.mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
              hp hal hex hnat hmask)⟩
    · cases hmem with
      | mk allocId tag baseAddr la msc hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
          hp hal hex hnat hkle hmask hsc hprim hf0imm hraw =>
        exact ⟨annealMemCopyOp_zero_into_union_field body.localDecls body.layouts hnodup
            hwt.size_valid hprov hlive hbase hptr hsz hlen hmut hprov_z hlive_z hbase_z hptr_z
            hlen_src hf0,
          .zstOverlay S n N f_z zstFlIdx f0Ty sc mp_u cachedLayout hc hwt hfields
            (.mk allocId tag baseAddr la msc hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
              hp hal hex hnat hkle hmask hsc hprim hf0imm hraw)⟩

/-- **`lean-miri` side of a 0-byte `[(); N]` aggregate field copy (`G3`)**: a
lemma about `annealAggregateHooksLM2_4PaddedZst.copyOpNoValidate`, with no
Anneal side:
For any memory-backed union `mp_u` satisfying `PaddedZstUnionUninitMemRel`
(and `LiveAllocsNodup m.machine`), writing a zero-sized `[(); N]` source operand
`src` (`src.layout.layout.size.bytes == 0`) into the zero-sized union field
destination `⟨.memory mp_u, fLay⟩` (`fLay.layout.size.bytes == 0`) via
`(annealAggregateHooksLM2_4PaddedZst body.localDecls body.layouts).copyOpNoValidate`
succeeds in-place (`.ok () m`) and establishes `PaddedZstUnionLocalRel.zstUninit`. -/
theorem step_padded_zst_union_aggregate_copyOpNoValidate_spec
    {body : CapturedMir} {m : AnnealStepState}
    (hnodup : LiveAllocsNodup m.machine)
    {uDecl : LocalDecl} {S n N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {cachedLayout : Option Miri.Interpreter.LocalLayout}
    (hc : ∀ l ∈ cachedLayout, l = translateTy uDecl.ty body.layouts)
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u)
    {src : Miri.Interpreter.OpTy AnnealProv} {fLay : Miri.Interpreter.LocalLayout}
    (hsrc0 : (src.layout.layout.size.bytes == 0) = true)
    (hdst0 : (fLay.layout.size.bytes == 0) = true) (b : Bool) :
    (annealAggregateHooksLM2_4PaddedZst body.localDecls body.layouts).copyOpNoValidate ()
      src ⟨.memory mp_u, fLay⟩ b m = .ok () m ∧
    PaddedZstUnionLocalRel m.machine uDecl body.layouts
      (.init (.aggregate 0 (List.replicate n .unit)))
      ⟨.live (.indirect mp_u), cachedLayout⟩ := by
  cases hmem with
  | mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    refine ⟨?_, .zstUninit S n N f_z zstFlIdx mp_u cachedLayout hc hwt hfields
      (.mk allocId tag baseAddr la hprov hmis hmeta hlive hbase hptr hovf hsz hlen hmut
        hp hal hex hnat hmask)⟩
    unfold annealAggregateHooksLM2_4PaddedZst
    dsimp only
    simp [hsrc0, hdst0, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      hprov, Option.bind, Miri.Memory.Provenance.getAllocId, hfind, pure, EStateM.pure]

/-- **`lean-miri` side of an uninitialized scalar payload read (`G3`)**: a
lemma about `annealReadImmediateLM2_2` on all-uninit union storage, together
with the all-uninit encoding of Anneal's ZST-initialized union value; it does
not state Anneal's read:
For any memory-backed union `mp_u` in `PaddedZstUnionUninitMemRel`
(and `LiveAllocsNodup m.machine`) and any primitive scalar field layout `fLay`
of width `w` (`ValidScalarBytes w`, `w ≤ S`,
`fLay.layout = scalarLayoutData (translateSizeBytes w) (translateAlignBytes w)`),
reading `⟨.indirect mp_u, fLay⟩` via `annealReadImmediateLM2_2` fails with
`.error (.undefinedBehavior "read of uninitialized memory field")`, while
encoding `.aggregate 0 (List.replicate n .unit)` in Anneal produces
`some (replicateUninitBytes S)`. -/
theorem step_padded_zst_union_uninit_payload_read_ub
    {body : CapturedMir} {m : AnnealStepState}
    (hnodup : LiveAllocsNodup m.machine)
    {uDecl : LocalDecl} {S n N f_z zstFlIdx w : Nat} {signed : Bool}
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hw : ValidScalarBytes w) (hwS : w ≤ S)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u)
    {tyId : Miri.MIR.TyId} :
    encodeByLayoutIdxAux 8 body.layouts uDecl.ty.layoutIdx
      (.aggregate 0 (List.replicate n .unit)) = some (replicateUninitBytes S) ∧
    annealReadImmediateLM2_2
      ⟨.indirect mp_u,
        { ty := tyId, layout := scalarLayoutData w signed }⟩
      m = .error (.undefinedBehavior "read of uninitialized memory field") m := by
  refine ⟨encodeByLayoutIdxAux_union_allUnits hwt hfields 7, ?_⟩
  cases hmem with
  | mk allocId tag baseAddr la hprov _ _ hlive hbase hptr _ _ _ _ _ _ _ _ hmask =>
    have hfind := array_find?_of_nodup_fst hnodup hlive
    have hrel0 : Miri.ABI.Size.ofBytes (mp_u.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
      have hb : mp_u.ptr.offset.bytes = baseAddr := by rw [hptr]; rfl
      rw [hb, UInt64.sub_self]; rfl
    have hsz0 : ((scalarLayoutData w signed).size == Miri.ABI.Size.ZERO) = false := by
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hfields_sc : (scalarLayoutData w signed).fields = .Primitive := rfl
    have hsz_sc : (scalarLayoutData w signed).size = translateSizeBytes w := rfl
    have hrepr : (scalarLayoutData w signed).backendRepr =
        .Scalar (.Initialized (value := .Int (translateAbiIntegerBytes w) signed)
          (validRange := { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * w)) - 1) })) := rfl
    rcases la with ⟨kind, alloc⟩
    have hbad : alloc.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w))) := by
      rw [hmask]
      rcases hwt.size_valid with rfl | rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl | rfl <;>
        (try omega) <;>
        rfl
    have hread_err := union_readScalar_uninit hbad
    change annealReadIndirectImmediate mp_u
      { ty := tyId, layout := scalarLayoutData w signed } m = _
    unfold annealReadIndirectImmediate
    rw [hprov, hfields_sc, hsz0, hrepr, hsz_sc]
    simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, Option.bind_some, Miri.Memory.Provenance.getAllocId, hbase, hfind,
      hrel0, hread_err, throw, throwThe]
    rfl

end LeanMiriSpec.Correspondence.Witness
