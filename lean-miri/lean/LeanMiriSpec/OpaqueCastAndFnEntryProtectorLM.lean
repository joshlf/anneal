/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Trusted
import Miri.Interpreter.Projection
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.ValidityMachine
import Miri.Memory.Validity
import Miri.Memory.Access
import Miri.TreeBorrows.RetagPolicy
import LeanMiriSpec.HeapAllocAndWidePtrLM
import LeanMiriSpec.WideDstAndMaybeUninitLM
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.EnumLM2_3

/-!
# Episode 1 LeanMiri Authority: `ProjectionElem.opaqueCast` Phase Boundary, Callee-Only `FnEntry`
# Protectors (`rust#166253`), and Safe-Pointer Validity
# (`LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`)

The vendored LeanMiri (`lean-miri/vendor/`, unmodified) side of the frozen 22-case (`0..21`) ×
2-mode matrix shared with `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR`:

* `D1` (`0..9`): vendored `Miri.Interpreter.project` and `Miri.Interpreter.PlaceDynamic.project`
  reject `ProjectionElem.OpaqueCast` at the phase boundary (`OpaqueCast after borrowck`, never a UB
  verdict; `lm_opaqueCast_phase_boundary`), because rustc's validator forbids `OpaqueCast` at
  `MirPhase::Runtime`. The register-only cells (`0`–`3`, `9`) execute the cast-erased
  (post-`PostAnalysisNormalize`) image `ocEraseBody` of the shared fixture directly through
  vendored `Miri.Interpreter.Step.step` (`ocStepHooks`: the `annealStepHooksLM2_3` adapter with the
  `wdStepHooks` raw-pointer overlay). The memory-backed cells run on the vendored memory harness:
  `4` (field write into an uninitialized local), `6` (`SetDiscriminant` with the tag computed by
  vendored `Discriminant.tagForVariant`), and `8` (`*(&raw const x)` through a vendored pointer
  scalar round trip) — the adapter's local allocation runs vendored while-loop memory code that the
  kernel cannot evaluate without loop-unrolling twins — and `5` / `7`, which have no pinned
  `Step.step` path (`lm_step_adapter_boundaries`: `Deinit` was removed from pinned rustc MIR, and
  the adapter rejects `"drop terminator"`), run vendored `Allocation.writeUninit` followed by
  `Allocation.readScalar` — the `write_uninit` semantics of `Deinit` and Trusted's drop-as-deinit
  model.
* `D2` (`10..15`): callee-only `FnEntry` protectors through the vendored Tree Borrows retag
  pipeline (`RetagPipeline.retagPointerValue`, `MachineMemoryHooks.beforeMemoryWrite`,
  `BorrowTree.releaseProtector`), with the universal `RetagPolicy.create` protector law.
* `D3` (`16..21`): safe-pointer validity through vendored `Validity.checkScalar` (non-null valid
  range of `pointerLayoutData true`), `checkPtrAccess` (dereferenceability), and `checkPtrAlign`.

The memory harness (`lmAllocate`, `lmStore`, `lmLoad`, `lmRetag`, `lmEndCall`, `lmDeallocate`) is
the one of `LeanMiriSpec.HeapAllocAndWidePtrLM`: every state change is a vendored definition. The
`CapturedMir` fixtures of §0 are textually identical to those of
`MiniRustSpec.OpaqueCastAndFnEntryProtectorMR`, and every fixture is also executed through
unmodified Trusted `stepMirFn` (`lmOcTrustedObserve`).

Root isolation: zero `Anneal.*` and zero `MiniRustSpec.*` imports (trailing `run_cmd` audit).
-/

namespace LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM

set_option Elab.async false

/-! ## §0. Frozen Observation Interface, Kernel Helpers, and Shared `CapturedMir` Fixtures -/

/-- Frozen cross-authority observation domain (constructor order shared identically with
`MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.MrOcFpObs`). -/
inductive LmOcFpObs : Type where
  /-- Normal termination with a scalar result. -/
  | okScalar (val : Nat)
  /-- Normal return of a cross-frame call: `(callee result, caller referent after the call)`. -/
  | okRetagPair (retVal : Nat) (referentVal : Nat)
  /-- A safe pointer accepted by validity / dereferenceability. -/
  | okPtrValid
  /-- Undefined behavior. -/
  | ub
  /-- A phase-boundary rejection (`OpaqueCast after borrowck`). -/
  | phaseBoundary
  /-- Fail-closed unsupported construct or out-of-range case. -/
  | unsupported
  /-- Specification panic (unused on the LeanMiri side; kept for interface parity). -/
  | specPanic
  deriving DecidableEq, Repr

/-- Number of canonical cases (`0..21`, 44 mode cells). -/
def lmOcCaseCount : Nat := 22

/-- Close an equality goal via kernel definitional reduction (`Eq.refl`, zero `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Combine the halves of a multi-query case: agreement is required, otherwise fail closed. -/
def ocCombine (a b : LmOcFpObs) : LmOcFpObs := if a = b then a else .unsupported

/-! ### Shared `CapturedMir` fixtures

Every definition in this section is shared verbatim (same text, same opened namespaces) with
`MiniRustSpec.OpaqueCastAndFnEntryProtectorMR`, so Episode 2's cross-root bridge can lock each
fixture by `Eq.refl`. -/

section Fixtures

open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.Layout

/-- Number of canonical cases (`0..21`): `D1` `0..9`, `D2` `10..15`, `D3` `16..21`. -/
def ocFixtureCaseCount : Nat := 22

@[reducible] def ocSpan : String := "oc.rs:1:1"
@[reducible] def ocSt (k : StatementKind) : Statement := { kind := k, span := ocSpan }
@[reducible] def ocBb (stmts : List StatementKind) (term : TerminatorKind) : BasicBlockData :=
  { statements := stmts.map ocSt, terminator := { kind := term, span := ocSpan }, isCleanup := false }
@[reducible] def ocDecl (ty : Ty) : LocalDecl := { mutability := .mut, ty, debugName := none }
@[reducible] def ocLoc (i : Nat) (proj : List ProjectionElem := []) : Place :=
  { local_ := i, projection := proj }

/-- Layout table: `0 = u8`, `1 = u32`, `2 = ()`, `3 = thin pointer / reference`,
`4 = (u32, u32)`, `5 = TwoVar` (`#[repr(u8)] enum TwoVar { A(u32) = 0, B(u32) = 1 }`: `u8` tag at
offset `0`, payload at `4`), `6 = u64 / usize / isize`, `7 = (u8, u8)`. -/
def ocU8Layout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def ocU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def ocUnitLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
def ocPtrLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) { start := 0, end_ := 18446744073709551615 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def ocPairLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [1, 1] }
def ocTwoVarLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
      [.arbitrary [⟨4⟩] [0], .arbitrary [⟨4⟩] [0]],
    isUninhabited := false }
def ocU64Layout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def ocBytePairLayout : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 0] }

def ocLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [ocU8Layout, ocU32Layout, ocUnitLayout, ocPtrLayout, ocPairLayout, ocTwoVarLayout,
                ocU64Layout, ocBytePairLayout] }

@[reducible] def ocU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
@[reducible] def ocU32Ty : Ty := { kind := .uint .u32, layoutIdx := 1 }
@[reducible] def ocUnitTy : Ty := { kind := .tuple [], layoutIdx := 2 }
@[reducible] def ocUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 6 }
@[reducible] def ocIsizeTy : Ty := { kind := .int .isize, layoutIdx := 6 }
@[reducible] def ocU64Ty : Ty := { kind := .uint .u64, layoutIdx := 6 }
@[reducible] def ocPairTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 4 }
@[reducible] def ocTwoVarTy : Ty := { kind := .adt "oc::TwoVar" [], layoutIdx := 5 }
@[reducible] def ocBytePairTy : Ty := { kind := .tuple [.uint .u8, .uint .u8], layoutIdx := 7 }
@[reducible] def ocRawConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 3 }
@[reducible] def ocRawConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 3 }
@[reducible] def ocRawMutU8Ty : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 3 }
@[reducible] def ocMutRefU8Ty : Ty := { kind := .ref .mut (.uint .u8), layoutIdx := 3 }
@[reducible] def ocShrRefU8Ty : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 3 }
@[reducible] def ocShrRefU32Ty : Ty := { kind := .ref .not (.uint .u32), layoutIdx := 3 }
@[reducible] def ocShrRefUnitTy : Ty := { kind := .ref .not (.tuple []), layoutIdx := 3 }

@[reducible] def ocConstU8 (n : Nat) : Operand := .constant { ty := ocU8Ty, val := .scalar (.int ⟨n, 1⟩) }
@[reducible] def ocConstU32 (n : Nat) : Operand := .constant { ty := ocU32Ty, val := .scalar (.int ⟨n, 4⟩) }
@[reducible] def ocConstUsize (n : Nat) : Operand := .constant { ty := ocUsizeTy, val := .scalar (.int ⟨n, 8⟩) }
@[reducible] def ocConstU64 (n : Nat) : Operand := .constant { ty := ocU64Ty, val := .scalar (.int ⟨n, 8⟩) }
@[reducible] def ocConstIsize (n : Nat) : Operand := .constant { ty := ocIsizeTy, val := .scalar (.int ⟨n, 8⟩) }
@[reducible] def ocFnOp (path : String) : Operand :=
  .constant { ty := { kind := .fnDef path [], layoutIdx := 0 }, val := .zeroSized }

def ocFnAbi : FnAbi :=
  { args := [], ret := { layout := ocU32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def ocBody (name : String) (argCount : Nat) (decls : List Ty) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := name, phase := .runtimePostCleanup, role := .subject, argCount,
    localDecls := decls.map ocDecl, basicBlocks := blocks, fnAbi := ocFnAbi,
    layouts := ocLayouts, allocations := [] }

/-! #### `D1`: `ProjectionElem.opaqueCast` in every place context (`0..9`)

Every `D1` fixture is argument-free: `_1` is made live and initialized in the body. The cast type
of every chain equals the declared type of its local, so the cast-erased fixture
(`ocEraseBody`) is well typed. -/

@[reducible] def ocCastU32 : ProjectionElem := .opaqueCast ocU32Ty
@[reducible] def ocInit7 : List StatementKind := [.storageLive 1, .assign (ocLoc 1) (.use (ocConstU32 7))]

/-- Case 0: `_0 = copy (_1 as u32)`; `_2 = copy _1` (the copy leaves `_1` initialized). -/
def ocCase0Mir : CapturedMir :=
  ocBody "oc::case0_copy_through_cast" 0 [ocU32Ty, ocU32Ty, ocU32Ty]
    [ocBb (ocInit7 ++ [.storageLive 2, .assign (ocLoc 0) (.use (.copy (ocLoc 1 [ocCastU32]))),
           .assign (ocLoc 2) (.use (.copy (ocLoc 1)))]) .return_]
/-- Case 1: `_0 = move ((_1 as u32) as u32)` (pure cast chain move). -/
def ocCase1Mir : CapturedMir :=
  ocBody "oc::case1_move_through_cast_chain" 0 [ocU32Ty, ocU32Ty]
    [ocBb (ocInit7 ++ [.assign (ocLoc 0) (.use (.move (ocLoc 1 [ocCastU32, ocCastU32])))]) .return_]
/-- Case 2 (negative): `_2 = move (_1 as u32)`; `_0 = copy _1` (use after move). -/
def ocCase2Mir : CapturedMir :=
  ocBody "oc::case2_use_after_move_through_cast" 0 [ocU32Ty, ocU32Ty, ocU32Ty]
    [ocBb (ocInit7 ++ [.storageLive 2, .assign (ocLoc 2) (.use (.move (ocLoc 1 [ocCastU32]))),
           .assign (ocLoc 0) (.use (.copy (ocLoc 1)))]) .return_]
/-- Case 3: nested cast chain assignment `((_1 as u32) as u32) = 42`; `_0 = copy _1`. -/
def ocCase3Mir : CapturedMir :=
  ocBody "oc::case3_nested_cast_assign" 0 [ocU32Ty, ocU32Ty]
    [ocBb [.storageLive 1, .assign (ocLoc 1 [ocCastU32, ocCastU32]) (.use (ocConstU32 42)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 1)))] .return_]
/-- Case 4: cast-then-field into an UNINITIALIZED tuple local `(_1 as (u32, u32)).1 = 9`,
then `_0 = copy (_1 as (u32, u32)).1`. -/
def ocCase4Mir : CapturedMir :=
  ocBody "oc::case4_cast_then_field_uninit" 0 [ocU32Ty, ocPairTy]
    [ocBb [.storageLive 1,
           .assign (ocLoc 1 [.opaqueCast ocPairTy, .field 1 ocU32Ty]) (.use (ocConstU32 9)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 1 [.opaqueCast ocPairTy, .field 1 ocU32Ty])))] .return_]
/-- Case 5 (negative): `Deinit(_1 as u32)`; `_0 = copy _1`. -/
def ocCase5Mir : CapturedMir :=
  ocBody "oc::case5_deinit_through_cast" 0 [ocU32Ty, ocU32Ty]
    [ocBb (ocInit7 ++ [.deinit (ocLoc 1 [ocCastU32]), .assign (ocLoc 0) (.use (.copy (ocLoc 1)))]) .return_]
/-- Case 6: `_1 = TwoVar::A(7)`; `SetDiscriminant(_1 as TwoVar, 1)`;
`_0 = discriminant(_1 as TwoVar)`. -/
def ocCase6Mir : CapturedMir :=
  ocBody "oc::case6_set_discriminant_through_cast" 0 [ocIsizeTy, ocTwoVarTy]
    [ocBb [.storageLive 1, .assign (ocLoc 1) (.aggregate (.adt "oc::TwoVar" 0 none) [ocConstU32 7]),
           .setDiscriminant (ocLoc 1 [.opaqueCast ocTwoVarTy]) 1,
           .assign (ocLoc 0) (.discriminant (ocLoc 1 [.opaqueCast ocTwoVarTy]))] .return_]
/-- Case 7 (negative): `Drop(_1 as u32) -> bb1`; `bb1: _0 = copy _1` (use after drop). -/
def ocCase7Mir : CapturedMir :=
  ocBody "oc::case7_drop_through_cast" 0 [ocU32Ty, ocU32Ty]
    [ocBb ocInit7 (.drop (ocLoc 1 [ocCastU32]) 1 .continue_),
     ocBb [.assign (ocLoc 0) (.use (.copy (ocLoc 1)))] .return_]
/-- Case 8 (fail-closed boundary): `_2 = &raw const _1`; `_0 = copy (*(_2 as *const u32))`
(a dereference directly below a leading cast chain). -/
def ocCase8Mir : CapturedMir :=
  ocBody "oc::case8_deref_below_cast" 0 [ocU32Ty, ocU32Ty, ocRawConstU32Ty]
    [ocBb [.storageLive 1, .storageLive 2, .assign (ocLoc 1) (.use (ocConstU32 5)),
           .assign (ocLoc 2) (.rawPtr .not (ocLoc 1)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.opaqueCast ocRawConstU32Ty, .deref])))] .return_]
/-- Case 9 (negative, UB not masked): `_0 = copy (_1 as u32)` with `_1` live but uninitialized. -/
def ocCase9Mir : CapturedMir :=
  ocBody "oc::case9_uninit_read_through_cast" 0 [ocU32Ty, ocU32Ty]
    [ocBb [.storageLive 1, .assign (ocLoc 0) (.use (.copy (ocLoc 1 [ocCastU32])))] .return_]

/-! #### Cast erasure (the post-borrowck / `PostAnalysisNormalize` image)

`ocEraseBody` removes every `ProjectionElem.opaqueCast` from every place of every statement and
terminator (and leaves everything else untouched). -/

def ocEraseProj : List ProjectionElem → List ProjectionElem
  | [] => []
  | .opaqueCast _ :: rest => ocEraseProj rest
  | e :: rest => e :: ocEraseProj rest
def ocErasePlace (p : Place) : Place := { p with projection := ocEraseProj p.projection }
def ocEraseOperand : Operand → Operand
  | .copy p => .copy (ocErasePlace p)
  | .move p => .move (ocErasePlace p)
  | .constant c => .constant c
def ocEraseRvalue : Rvalue → Rvalue
  | .use op => .use (ocEraseOperand op)
  | .ref k p => .ref k (ocErasePlace p)
  | .rawPtr m p => .rawPtr m (ocErasePlace p)
  | .len p => .len (ocErasePlace p)
  | .discriminant p => .discriminant (ocErasePlace p)
  | .copyForDeref p => .copyForDeref (ocErasePlace p)
  | .cast k op t => .cast k (ocEraseOperand op) t
  | .binaryOp o a b => .binaryOp o (ocEraseOperand a) (ocEraseOperand b)
  | .unaryOp o a => .unaryOp o (ocEraseOperand a)
  | .aggregate k ops => .aggregate k (ops.map ocEraseOperand)
  | rv => rv
def ocEraseStmt : StatementKind → StatementKind
  | .assign p rv => .assign (ocErasePlace p) (ocEraseRvalue rv)
  | .setDiscriminant p v => .setDiscriminant (ocErasePlace p) v
  | .deinit p => .deinit (ocErasePlace p)
  | .retag k p => .retag k (ocErasePlace p)
  | .placeMention p => .placeMention (ocErasePlace p)
  | k => k
def ocEraseTerm : TerminatorKind → TerminatorKind
  | .drop p t u => .drop (ocErasePlace p) t u
  | .call f args d t u => .call (ocEraseOperand f) (args.map ocEraseOperand) (ocErasePlace d) t u
  | k => k
def ocEraseBody (b : CapturedMir) : CapturedMir :=
  { b with basicBlocks := b.basicBlocks.map fun bb =>
      { bb with statements := bb.statements.map fun s => { s with kind := ocEraseStmt s.kind },
                terminator := { bb.terminator with kind := ocEraseTerm bb.terminator.kind } } }

/-! #### `D2`: callee-only `FnEntry` protectors (`rust#166253`, `10..15`)

Every caller holds `x : u8 = 3` in `_1`, its raw pointer `_2 = &raw mut _1`, and a reference `_3`;
it calls the callee with arguments `args`, stores the result in `_4`, runs `post`, and returns
`(_4, _1)`. -/

def ocD2Main (name callee : String) (refRv : Rvalue) (refTy : Ty) (args : List Operand)
    (post : List StatementKind) : CapturedMir :=
  ocBody name 0 [ocBytePairTy, ocU8Ty, ocRawMutU8Ty, refTy, ocU8Ty]
    [ocBb [.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4,
           .assign (ocLoc 1) (.use (ocConstU8 3)),
           .assign (ocLoc 2) (.rawPtr .mut (ocLoc 1)),
           .assign (ocLoc 3) refRv]
       (.call (ocFnOp callee) args (ocLoc 4) (some 1) .continue_),
     ocBb (post ++ [.assign (ocLoc 0) (.aggregate .tuple [.copy (ocLoc 4), .copy (ocLoc 1)])]) .return_]

/-- Case 10 callee (`fn(*mut u8, *mut u8) -> u8`, the post-`#166253` callee-only view of a
transmuted `fn(&mut u8)`): no `FnEntry` retag; foreign write `*_2 = 5` through the parent pointer. -/
def ocCase10Callee : CapturedMir :=
  ocBody "oc::case10_callee" 2 [ocU8Ty, ocRawMutU8Ty, ocRawMutU8Ty]
    [ocBb [.assign (ocLoc 2 [.deref]) (.use (ocConstU8 5)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
def ocCase10Mir : CapturedMir :=
  ocD2Main "oc::case10_main" "oc::case10_callee" (.ref (.mut false) (ocLoc 2 [.deref])) ocMutRefU8Ty
    [.copy (ocLoc 2), .copy (ocLoc 2)] []
/-- Case 11 callee (pre-`#166253` caller-signature contrast): the SAME body as case `10`, but
retagged on entry at the caller's `&mut u8` signature (`RetagKind.fnEntry` on `_1`). -/
def ocCase11Callee : CapturedMir :=
  ocBody "oc::case11_callee" 2 [ocU8Ty, ocMutRefU8Ty, ocRawMutU8Ty]
    [ocBb [.retag .fnEntry (ocLoc 1),
           .assign (ocLoc 2 [.deref]) (.use (ocConstU8 5)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
def ocCase11Mir : CapturedMir :=
  ocD2Main "oc::case11_main" "oc::case11_callee" (.ref (.mut false) (ocLoc 2 [.deref])) ocMutRefU8Ty
    [.copy (ocLoc 3), .copy (ocLoc 2)] []
/-- Case 12 callee (`fn(&mut u8)`): `FnEntry` retag, write `*_1 = 4`, return `*_1`; the caller
writes `_1 = 9` after the protector is released. -/
def ocCase12Callee : CapturedMir :=
  ocBody "oc::case12_callee" 1 [ocU8Ty, ocMutRefU8Ty]
    [ocBb [.retag .fnEntry (ocLoc 1),
           .assign (ocLoc 1 [.deref]) (.use (ocConstU8 4)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 1 [.deref])))] .return_]
def ocCase12Mir : CapturedMir :=
  ocD2Main "oc::case12_main" "oc::case12_callee" (.ref (.mut false) (ocLoc 1)) ocMutRefU8Ty
    [.copy (ocLoc 3)] [.assign (ocLoc 1) (.use (ocConstU8 9))]
/-- Case 13 callee (`fn(&mut u8, *mut u8)`): `FnEntry` retag, local write `*_1 = 4`, then the
aliased foreign write `*_2 = 5` while the strong protector is active. -/
def ocCase13Callee : CapturedMir :=
  ocBody "oc::case13_callee" 2 [ocU8Ty, ocMutRefU8Ty, ocRawMutU8Ty]
    [ocBb [.retag .fnEntry (ocLoc 1),
           .assign (ocLoc 1 [.deref]) (.use (ocConstU8 4)),
           .assign (ocLoc 2 [.deref]) (.use (ocConstU8 5)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
def ocCase13Mir : CapturedMir :=
  ocD2Main "oc::case13_main" "oc::case13_callee" (.ref (.mut false) (ocLoc 2 [.deref])) ocMutRefU8Ty
    [.copy (ocLoc 3), .copy (ocLoc 2)] []
/-- Case 14 callee (`fn(&u8, *mut u8)`): `FnEntry` retag of the shared reference (`Frozen`),
then the foreign write `*_2 = 5` while the protector is active. -/
def ocCase14Callee : CapturedMir :=
  ocBody "oc::case14_callee" 2 [ocU8Ty, ocShrRefU8Ty, ocRawMutU8Ty]
    [ocBb [.retag .fnEntry (ocLoc 1),
           .assign (ocLoc 2 [.deref]) (.use (ocConstU8 5)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
def ocCase14Mir : CapturedMir :=
  ocD2Main "oc::case14_main" "oc::case14_callee" (.ref .shared (ocLoc 2 [.deref])) ocShrRefU8Ty
    [.copy (ocLoc 3), .copy (ocLoc 2)] []
/-- Case 15 callee (`fn(&u8)`): `FnEntry` retag, read `*_1`; the caller writes `_1 = 9` after
the protector is released. -/
def ocCase15Callee : CapturedMir :=
  ocBody "oc::case15_callee" 1 [ocU8Ty, ocShrRefU8Ty]
    [ocBb [.retag .fnEntry (ocLoc 1),
           .assign (ocLoc 0) (.use (.copy (ocLoc 1 [.deref])))] .return_]
def ocCase15Mir : CapturedMir :=
  ocD2Main "oc::case15_main" "oc::case15_callee" (.ref .shared (ocLoc 1)) ocShrRefU8Ty
    [.copy (ocLoc 3)] [.assign (ocLoc 1) (.use (ocConstU8 9))]

/-- The no-borrow-tracker image of a body: every `Retag` statement becomes `Nop` (exactly what
running without a borrow tracker does with retags). -/
def ocEraseRetags (b : CapturedMir) : CapturedMir :=
  { b with basicBlocks := b.basicBlocks.map fun bb =>
      { bb with statements := bb.statements.map fun s =>
          match s.kind with
          | .retag _ _ => { s with kind := .nop }
          | _ => s } }

/-! #### `D3`: safe-pointer validity (`16..21`), observed by a dereference through the pointer -/

/-- Case 16: valid live aligned `&u32`. -/
def ocCase16Mir : CapturedMir :=
  ocBody "oc::case16_valid_ref" 0 [ocU32Ty, ocU32Ty, ocShrRefU32Ty]
    [ocBb [.storageLive 1, .storageLive 2, .assign (ocLoc 1) (.use (ocConstU32 7)),
           .assign (ocLoc 2) (.ref .shared (ocLoc 1)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
/-- Case 17: zero-sized `&()`. -/
def ocCase17Mir : CapturedMir :=
  ocBody "oc::case17_zst_ref" 0 [ocUnitTy, ocUnitTy, ocShrRefUnitTy]
    [ocBb [.storageLive 1, .storageLive 2,
           .assign (ocLoc 1) (.aggregate .tuple []),
           .assign (ocLoc 2) (.ref .shared (ocLoc 1)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
/-- Case 18: null `&u32` (`transmute::<usize, &u32>(0)`). -/
def ocCase18Mir : CapturedMir :=
  ocBody "oc::case18_null_ref" 0 [ocU32Ty, ocUsizeTy, ocShrRefU32Ty]
    [ocBb [.storageLive 1, .storageLive 2, .assign (ocLoc 1) (.use (ocConstUsize 0)),
           .assign (ocLoc 2) (.cast .transmute (.copy (ocLoc 1)) ocShrRefU32Ty),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
/-- Case 19: unaligned `&u32` at `base + 2` inside a live 8-byte `u64` local. -/
def ocCase19Mir : CapturedMir :=
  ocBody "oc::case19_unaligned_ref" 0
    [ocU32Ty, ocU64Ty, ocRawConstU8Ty, ocRawConstU8Ty, ocRawConstU32Ty, ocShrRefU32Ty]
    [ocBb [.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
           .assign (ocLoc 1) (.use (ocConstU64 0)),
           .assign (ocLoc 2) (.rawPtr .not (ocLoc 1)),
           .assign (ocLoc 3) (.binaryOp .offset (.copy (ocLoc 2)) (ocConstIsize 2)),
           .assign (ocLoc 4) (.cast .ptrToPtr (.copy (ocLoc 3)) ocRawConstU32Ty),
           .assign (ocLoc 5) (.cast .transmute (.copy (ocLoc 4)) ocShrRefU32Ty),
           .assign (ocLoc 0) (.use (.copy (ocLoc 5 [.deref])))] .return_]
/-- Case 20: out-of-bounds `&u32` at `base + 4` of a live 4-byte `u32` local. -/
def ocCase20Mir : CapturedMir :=
  ocBody "oc::case20_oob_ref" 0
    [ocU32Ty, ocU32Ty, ocRawConstU8Ty, ocRawConstU8Ty, ocRawConstU32Ty, ocShrRefU32Ty]
    [ocBb [.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
           .assign (ocLoc 1) (.use (ocConstU32 7)),
           .assign (ocLoc 2) (.rawPtr .not (ocLoc 1)),
           .assign (ocLoc 3) (.binaryOp .offset (.copy (ocLoc 2)) (ocConstIsize 4)),
           .assign (ocLoc 4) (.cast .ptrToPtr (.copy (ocLoc 3)) ocRawConstU32Ty),
           .assign (ocLoc 5) (.cast .transmute (.copy (ocLoc 4)) ocShrRefU32Ty),
           .assign (ocLoc 0) (.use (.copy (ocLoc 5 [.deref])))] .return_]
/-- Case 21: `&u32` to a deallocated (`StorageDead`) local. -/
def ocCase21Mir : CapturedMir :=
  ocBody "oc::case21_freed_ref" 0 [ocU32Ty, ocU32Ty, ocShrRefU32Ty]
    [ocBb [.storageLive 1, .storageLive 2, .assign (ocLoc 1) (.use (ocConstU32 7)),
           .assign (ocLoc 2) (.ref .shared (ocLoc 1)),
           .storageDead 1,
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]

/-- The canonical fixture of each case: `(root body, callees)` (`none` for `idx ≥ 22`). -/
def ocCaseFixture? : Nat → Option (CapturedMir × List CapturedMir)
  | 0 => some (ocCase0Mir, [])
  | 1 => some (ocCase1Mir, [])
  | 2 => some (ocCase2Mir, [])
  | 3 => some (ocCase3Mir, [])
  | 4 => some (ocCase4Mir, [])
  | 5 => some (ocCase5Mir, [])
  | 6 => some (ocCase6Mir, [])
  | 7 => some (ocCase7Mir, [])
  | 8 => some (ocCase8Mir, [])
  | 9 => some (ocCase9Mir, [])
  | 10 => some (ocCase10Mir, [ocCase10Callee])
  | 11 => some (ocCase11Mir, [ocCase11Callee])
  | 12 => some (ocCase12Mir, [ocCase12Callee])
  | 13 => some (ocCase13Mir, [ocCase13Callee])
  | 14 => some (ocCase14Mir, [ocCase14Callee])
  | 15 => some (ocCase15Mir, [ocCase15Callee])
  | 16 => some (ocCase16Mir, [])
  | 17 => some (ocCase17Mir, [])
  | 18 => some (ocCase18Mir, [])
  | 19 => some (ocCase19Mir, [])
  | 20 => some (ocCase20Mir, [])
  | 21 => some (ocCase21Mir, [])
  | _ => none

/-! #### Shared bounded `stepMirFn` driver (no shadow evaluation: every transition is read off
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`'s own `MirStepNode`) -/

/-- Terminal outcome of a bounded Trusted run. -/
inductive OcTrustedOutcome : Type where
  /-- Normal return with the returned value. -/
  | ret (v : MirSemantics.Value)
  /-- Undefined behavior. -/
  | ub
  /-- Fail-closed unsupported construct (or any other terminal node). -/
  | unsupported
  /-- Fuel exhausted. -/
  | outOfFuel

/-- State of a bounded Trusted run. -/
inductive OcTrustedRun : Type where
  | running (s : MirSemantics.MachineState)
  | done (o : OcTrustedOutcome)

/-- One `stepMirFn` step. -/
def ocTrustedStep (body : CapturedMir) : OcTrustedRun → OcTrustedRun
  | .done o => .done o
  | .running s =>
    match MirSemantics.stepMirFn body s with
    | .tau (.running s') => .running s'
    | .tau (.halted (.normal r)) => .done (.ret r.1)
    | .tau (.faulted .ub) => .done .ub
    | .vis (.inr (.inl (.emit _))) cont =>
      match cont PUnit.unit with
      | .running s' => .running s'
      | _ => .done .unsupported
    | .ret (.normal r) => .done (.ret r.1)
    | .vis (.inl (.fail .ub)) _ => .done .ub
    | _ => .done .unsupported

/-- Step budget of every Trusted execution. -/
def ocTrustedFuel : Nat := 60

/-- Run `body` (with linked `callees`) from its entry state for `ocTrustedFuel` steps. -/
def ocRunTrustedRaw (body : CapturedMir) (callees : List CapturedMir) : OcTrustedOutcome :=
  match Nat.repeat (ocTrustedStep body) ocTrustedFuel
      (.running (MirSemantics.initMachineStateWithCallees body [] callees)) with
  | .done o => o
  | .running _ => .outOfFuel

end Fixtures

/-! ## §1. The LeanMiri Observer over Vendored Definitions -/

section Harness

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open LeanMiriSpec.HeapAllocAndWidePtrLM LeanMiriSpec.Correspondence
open LeanMiriSpec.WideDstAndMaybeUninitLM (wdStepHooks wdMkStepState)

/-! ### `D1`: vendored `Step.step` on the cast-erased fixtures -/

/-- `StepHooks` for the `D1` fixtures: `annealStepHooksLM2_3` (vendored
`Discriminant.writeDiscriminant` / `readDiscriminant` for `TwoVar`), with the `wdStepHooks`
assignment adapter (raw-pointer `toRef` overlay) for every assignment outside `lm23Assign`. -/
def ocStepHooks (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Miri.Interpreter.StepHooks
      AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealStepHooksLM2_3 body.localDecls body.layouts with
    assign := fun choice place rvalue state =>
      if lm23Assign body.localDecls body.layouts place rvalue then
        (annealStepHooksLM2_3 body.localDecls body.layouts).assign choice place rvalue state
      else
        (wdStepHooks body).assign choice place rvalue state }

/-- Entry locals of an argument-free fixture: `_0` live and uninitialized, every other local dead
(made live by the fixture's own `StorageLive`). -/
def ocStepLocals (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir) :
    Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :=
  (body.localDecls.zipIdx.map fun (d, idx) =>
    let l := some (translateTy d.ty body.layouts)
    if idx == 0 then ⟨.live (.immediate .uninit), l⟩ else ⟨.dead, l⟩).toArray

/-- Multi-step execution of unmodified vendored `Miri.Interpreter.Step.step` (returning the final
value of local `_0` when the root frame returns). -/
def ocRunMiriSteps
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit (Miri.Interpreter.RuntimePlace AnnealProv))
    (steps : Nat) (st : AnnealStepState) :
    Except StepError (Option (Miri.Interpreter.LocalValue AnnealProv)) :=
  match steps with
  | 0 => .error (.unsupported "out of fuel")
  | n + 1 =>
    let lastRet := st.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value))
    let (st', res) := Miri.Interpreter.Step.step hooks () st
    match res with
    | .error e => .error e
    | .ok true =>
      if st'.stack.frames.isEmpty then .ok lastRet
      else ocRunMiriSteps hooks n st'
    | .ok false => .ok (st'.stack.frames[0]?.bind (fun f => f.locals[0]?.map (·.value)))

/-- Run vendored `Miri.Interpreter.Step.step` on a fixture (returned local `_0`). -/
def ocRunStep (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (retTy : Trusted.Rustc.V2026_06_01.MirAst.Ty) :
    Except StepError (Option (Miri.Interpreter.LocalValue AnnealProv)) :=
  ocRunMiriSteps (ocStepHooks body) 24 (wdMkStepState body retTy (ocStepLocals body))

/-- Observe a `Step.step` result. -/
def lmOcStepObs (size : UInt64) :
    Except StepError (Option (Miri.Interpreter.LocalValue AnnealProv)) → LmOcFpObs
  | .ok (some (.live (.immediate (.scalar s)))) =>
    match s.toBits (Size.ofBytes size) with
    | .ok b => .okScalar b.toNat
    | .error _ => .unsupported
  | .error (.undefinedBehavior _) => .ub
  | _ => .unsupported

/-! ### Typed failures of the vendored memory harness -/

/-- A typed failure: the exact vendored error value that stopped a case. -/
inductive LmOcFail where
  /-- A memory-harness failure (`LeanMiriSpec.HeapAllocAndWidePtrLM.LmFailure`). -/
  | mem (f : LmFailure)
  /-- A vendored `checkPtrAccess` / `checkPtrAlign` failure. -/
  | access (e : AccessError)
  /-- A vendored `Validity.checkScalar` failure. -/
  | validity (e : ValidityError Unit)
  /-- The harness was used outside its domain. -/
  | harness (msg : String)

/-- The harness monad. -/
abbrev LmOcM := Except LmOcFail

/-- Lift a memory-harness result. -/
def lmOcMem {A : Type} (r : Except LmFailure A) : LmOcM A := r.mapError .mem

/-- Classify a typed failure as UB or fail-closed unsupported. -/
def lmOcObsOfFail : LmOcFail → LmOcFpObs
  | .mem f => match lmObsOfFailure f with
    | .ub => .ub
    | _ => .unsupported
  | .access e => match lmObsOfStep (MemoryErrors.access e) with
    | .ub => .ub
    | _ => .unsupported
  | .validity (.failure _) => .ub
  | .validity (.pathFailure _ _) => .ub
  | .validity _ => .unsupported
  | .harness _ => .unsupported

/-- Observe a harness result. -/
def lmOcRun (r : LmOcM LmOcFpObs) : LmOcFpObs :=
  match r with
  | .ok o => o
  | .error f => lmOcObsOfFail f

/-- Cases `5` / `7`: a live `u32` local holding `7`, de-initialized through vendored
`Allocation.writeUninit` (after the Tree Borrows write access), then read
(`Allocation.readScalar` on uninitialized bytes). -/
def lmOcDeinitThenRead (tb : Bool) : LmOcM LmOcFpObs := do
  let (p, st) ← lmOcMem (lmAllocate (lmInit tb) 4 4)
  let st ← lmOcMem (lmStore st p 4 7)
  let (id, off, prov, alloc) ← lmOcMem (lmAccessTarget st p 4)
  let range : AllocRange := ⟨off, Size.ofBytes 4⟩
  let st ← lmOcMem (lmTreeAccess st true alloc p id prov range)
  let st ← match st.mem.live.find? (fun e => e.1 == id) with
    | none => .error (.harness "dead local allocation")
    | some (_, entry) =>
      match Allocation.writeUninit range (Size.ofBytes 8) entry.allocation with
      | .error e _ => .error (.mem (.allocation e))
      | .ok () cleared =>
        match st.mem.setLiveAllocation id cleared with
        | .error e => .error (.mem (.access (.allocationLookup e)))
        | .ok mem => pure { st with mem := mem }
  let (v, _) ← lmOcMem (lmLoad st p 4)
  pure (.okScalar v)

/-- Case 4 (memory-backed): a fresh, UNINITIALIZED 8-byte `(u32, u32)` local; the field write
`.1 = 9` stores at the field offset `4` (`ocPairLayout`), then the field is read back. -/
def lmOcFieldWriteUninit (tb : Bool) : LmOcM LmOcFpObs := do
  let (p, st) ← lmOcMem (lmAllocate (lmInit tb) 8 4)
  let q := ⟨Size.ofBytes (p.offset.bytes + 4), p.provenance⟩
  let st ← lmOcMem (lmStore st q 4 9)
  let (v, _) ← lmOcMem (lmLoad st q 4)
  pure (.okScalar v)

/-- The direct tag that vendored `Discriminant.tagForVariant` (over the `annealDiscriminantHooksLM2_3`
compiler queries) assigns to variant `variant` of the shared `TwoVar` layout. -/
def lmOcTwoVarTag (variant : Nat) : LmOcM Nat :=
  let st := wdMkStepState ocCase6Mir ocIsizeTy (ocStepLocals ocCase6Mir)
  match Miri.Interpreter.Discriminant.tagForVariant
      (annealDiscriminantHooksLM2_3 ocCase6Mir.localDecls ocCase6Mir.layouts) ()
      (translateTy ocTwoVarTy ocLayouts) variant st with
  | .ok (some (tag, _)) _ =>
    match (Scalar.fromScalarInt (Prov := Provenance) tag).toBits (Size.ofBytes 1) with
    | .ok b => pure b.toNat
    | .error e => .error (.mem (.scalar e))
  | .ok none _ => .error (.harness "untagged variant")
  | .error e _ => .error (.mem (.step e))

/-- Case 6 (memory-backed): `TwoVar::A(7)` (tag of variant `0` at offset `0`, payload at `4`),
`SetDiscriminant(_, 1)` writes the vendored tag of variant `1`, and the discriminant is read back
from the (direct-encoded) tag byte. -/
def lmOcSetDiscriminant (tb : Bool) : LmOcM LmOcFpObs := do
  let (p, st) ← lmOcMem (lmAllocate (lmInit tb) 8 4)
  let t0 ← lmOcTwoVarTag 0
  let st ← lmOcMem (lmStore st p 1 t0)
  let st ← lmOcMem (lmStore st ⟨Size.ofBytes (p.offset.bytes + 4), p.provenance⟩ 4 7)
  let t1 ← lmOcTwoVarTag 1
  let st ← lmOcMem (lmStore st p 1 t1)
  let (d, _) ← lmOcMem (lmLoad st p 1)
  pure (.okScalar d)

/-- Case 8 (memory-backed): `x = 5` in a live `u32` allocation, `&raw const x` materialized as a
pointer scalar (vendored `Scalar.fromMaybePointer` / `Scalar.toPointer`), then `*p`. -/
def lmOcRawDeref (tb : Bool) : LmOcM LmOcFpObs := do
  let (p, st) ← lmOcMem (lmAllocate (lmInit tb) 4 4)
  let st ← lmOcMem (lmStore st p 4 5)
  let s ← (Scalar.fromMaybePointer lmLayout p).mapError (fun e => .mem (.scalar e))
  let q ← (s.toPointer lmLayout).mapError (fun e => .mem (.scalar e))
  let (v, _) ← lmOcMem (lmLoad st q 4)
  pure (.okScalar v)

/-! ### `D2`: callee-only `FnEntry` protectors (`x : u8 = 3` at `p`) -/

/-- The callee body of a `D2` case after the caller set up `x = 3` at the parent pointer `p`;
returns `(callee result, x after the call)`. `FnEntry` retags go through vendored
`RetagPipeline.retagPointerValue` (`lmRetag`), protector release through vendored
`BorrowTree.releaseProtector` / `GlobalState.endCall` (`lmEndCall`). -/
def lmOcD2 (tb : Bool) (k : Nat) : LmOcM LmOcFpObs := do
  let (p, st) ← lmOcMem (lmAllocate (lmInit tb) 1 1)
  let st ← lmOcMem (lmStore st p 1 3)
  let (r, st) ← match k with
    | 10 => do
      -- callee-only: `fn(*mut u8, *mut u8)`, no `FnEntry` retag; foreign write through `p`.
      let st ← lmOcMem (lmStore st p 1 5)
      lmOcMem (lmLoad st p 1)
    | 11 => do
      -- pre-`#166253` caller-signature retag at `&mut u8`, then the same foreign write.
      let (_, st) ← lmOcMem (lmRetag st p .reference lmFrozenFacts .Mutable .FnEntry true)
      let st ← lmOcMem (lmStore st p 1 5)
      lmOcMem (lmLoad st p 1)
    | 12 => do
      let (c, st) ← lmOcMem (lmRetag st p .reference lmFrozenFacts .Mutable .FnEntry true)
      let st ← lmOcMem (lmStore st c 1 4)
      lmOcMem (lmLoad st c 1)
    | 13 => do
      let (c, st) ← lmOcMem (lmRetag st p .reference lmFrozenFacts .Mutable .FnEntry true)
      let st ← lmOcMem (lmStore st c 1 4)
      let st ← lmOcMem (lmStore st p 1 5)
      lmOcMem (lmLoad st p 1)
    | 14 => do
      let (_, st) ← lmOcMem (lmRetag st p .reference lmFrozenFacts .Shared .FnEntry true)
      let st ← lmOcMem (lmStore st p 1 5)
      lmOcMem (lmLoad st p 1)
    | _ => do
      let (c, st) ← lmOcMem (lmRetag st p .reference lmFrozenFacts .Shared .FnEntry true)
      lmOcMem (lmLoad st c 1)
  let st ← lmOcMem (lmEndCall st)
  let st ← if k == 12 || k == 15 then lmOcMem (lmStore st p 1 9) else pure st
  let (v, _) ← lmOcMem (lmLoad st p 1)
  pure (.okRetagPair r v)

/-! ### `D3`: safe-pointer validity -/

/-- The scalar validity layout of a safe pointer (`pointerLayoutData true`: non-null). -/
def lmOcSafePtrValidity : LmOcM ScalarValidityLayout :=
  match (pointerLayoutData true).backendRepr with
  | .Scalar (.Initialized (validRange := vr) ..) => pure ⟨Size.ofBytes 8, vr⟩
  | _ => .error (.harness "pointer layout")

/-- Vendored safe-pointer validity of `p` at a pointee of `size` bytes and alignment `align`:
`Validity.checkScalar` (non-null), `checkPtrAccess` (dereferenceable), `checkPtrAlign`. -/
def lmOcPtrValidity (st : LmState) (p : Pointer (Option Provenance)) (size : Nat) (align : Align) :
    LmOcM LmOcFpObs := do
  let s ← (Scalar.fromMaybePointer lmLayout p).mapError (fun e => .mem (.scalar e))
  let lay ← lmOcSafePtrValidity
  match Validity.checkScalar (MachineError := Unit) (HookState := Unit) lay s
      (fun _ st => .error () st) () with
  | .error e _ => .error (.validity e)
  | .ok () _ =>
    (checkPtrAccess lmPtrArith p (Size.ofBytes (UInt64.ofNat size)) (.dereferenceable "pointer")
      lmResolvePure st.mem.getAllocInfo).mapError .access
    (checkPtrAlign p align true lmResolvePure st.mem.getAllocInfo (fun _ _ _ _ _ => none)).mapError .access
    pure .okPtrValid

/-- A live `size`-byte allocation holding `bits`. -/
def lmOcLive (tb : Bool) (size : Nat) (bits : Nat) : LmOcM (Pointer (Option Provenance) × LmState) := do
  let (p, st) ← lmOcMem (lmAllocate (lmInit tb) size size)
  let st ← lmOcMem (lmStore st p (UInt64.ofNat size) bits)
  pure (p, st)

/-- Add `k` bytes to a pointer's address (keeping its provenance). -/
def lmOcAddr (p : Pointer (Option Provenance)) (k : Nat) : Pointer (Option Provenance) :=
  ⟨Size.ofBytes (p.offset.bytes + UInt64.ofNat k), p.provenance⟩

def lmOcD3 (tb : Bool) (k : Nat) : LmOcM LmOcFpObs := do
  match k with
  | 16 => let (p, st) ← lmOcLive tb 4 7; lmOcPtrValidity st p 4 ⟨2⟩
  | 17 => lmOcPtrValidity (lmInit tb) ⟨Size.ofBytes 4, none⟩ 0 ⟨0⟩
  | 18 =>
    let a ← lmOcPtrValidity (lmInit tb) ⟨Size.ofBytes 0, none⟩ 4 ⟨2⟩
    let b ← lmOcPtrValidity (lmInit tb) ⟨Size.ofBytes 0, none⟩ 0 ⟨0⟩
    pure (ocCombine a b)
  | 19 => let (p, st) ← lmOcLive tb 8 0; lmOcPtrValidity st (lmOcAddr p 2) 4 ⟨2⟩
  | 20 => let (p, st) ← lmOcLive tb 4 7; lmOcPtrValidity st (lmOcAddr p 4) 4 ⟨2⟩
  | _ =>
    let (p, st) ← lmOcLive tb 4 7
    let st ← lmOcMem (lmDeallocate st p 4 4)
    lmOcPtrValidity st p 4 ⟨2⟩

/-! ### The observer -/

/-- The LeanMiri run of case `idx` (`none` for `idx ≥ 22`). -/
def lmOcCase (tb : Bool) : Nat → Option LmOcFpObs
  | 0 => some (lmOcStepObs 4 (ocRunStep (ocEraseBody ocCase0Mir) ocU32Ty))
  | 1 => some (lmOcStepObs 4 (ocRunStep (ocEraseBody ocCase1Mir) ocU32Ty))
  | 2 => some (lmOcStepObs 4 (ocRunStep (ocEraseBody ocCase2Mir) ocU32Ty))
  | 3 => some (lmOcStepObs 4 (ocRunStep (ocEraseBody ocCase3Mir) ocU32Ty))
  | 4 => some (lmOcRun (lmOcFieldWriteUninit tb))
  | 5 => some (lmOcRun (lmOcDeinitThenRead tb))
  | 6 => some (lmOcRun (lmOcSetDiscriminant tb))
  | 7 => some (lmOcRun (lmOcDeinitThenRead tb))
  | 8 => some (lmOcRun (lmOcRawDeref tb))
  | 9 => some (lmOcStepObs 4 (ocRunStep (ocEraseBody ocCase9Mir) ocU32Ty))
  | 10 => some (lmOcRun (lmOcD2 tb 10))
  | 11 => some (lmOcRun (lmOcD2 tb 11))
  | 12 => some (lmOcRun (lmOcD2 tb 12))
  | 13 => some (lmOcRun (lmOcD2 tb 13))
  | 14 => some (lmOcRun (lmOcD2 tb 14))
  | 15 => some (lmOcRun (lmOcD2 tb 15))
  | 16 => some (lmOcRun (lmOcD3 tb 16))
  | 17 => some (lmOcRun (lmOcD3 tb 17))
  | 18 => some (lmOcRun (lmOcD3 tb 18))
  | 19 => some (lmOcRun (lmOcD3 tb 19))
  | 20 => some (lmOcRun (lmOcD3 tb 20))
  | 21 => some (lmOcRun (lmOcD3 tb 21))
  | _ => none

/-- **Real LeanMiri observer** (fail-closed `.unsupported` for `idx ≥ 22`). -/
def lmOcObserve (tb : Bool) (idx : Nat) : LmOcFpObs :=
  match lmOcCase tb idx with
  | some o => o
  | none => .unsupported

end Harness

/-! ### Evaluable twins (while-loop unrolling of the vendored memory code) -/

section Twins
open LeanMiriSpec.HeapAllocAndWidePtrLM

unroll_loops lmOcDeinitThenReadU := lmOcDeinitThenRead fuel 0
  with lmAllocateU, lmStoreU, lmAccessTargetU, lmTreeAccessU, lmLoadU
unroll_loops lmOcD2U := lmOcD2 fuel 0 with lmAllocateU, lmStoreU, lmLoadU, lmRetagU, lmEndCallU
unroll_loops lmOcPtrValidityU := lmOcPtrValidity fuel 0 with getAllocInfoU
unroll_loops lmOcLiveU := lmOcLive fuel 0 with lmAllocateU, lmStoreU
unroll_loops lmOcD3U := lmOcD3 fuel 0 with lmOcLiveU, lmOcPtrValidityU, lmDeallocateU
unroll_loops lmOcFieldWriteUninitU := lmOcFieldWriteUninit fuel 0 with lmAllocateU, lmStoreU, lmLoadU
unroll_loops lmOcSetDiscriminantU := lmOcSetDiscriminant fuel 0 with lmAllocateU, lmStoreU, lmLoadU
unroll_loops lmOcRawDerefU := lmOcRawDeref fuel 0 with lmAllocateU, lmStoreU, lmLoadU
unroll_loops lmOcCaseU := lmOcCase fuel 0 with lmOcDeinitThenReadU, lmOcFieldWriteUninitU,
  lmOcSetDiscriminantU, lmOcRawDerefU, lmOcD2U, lmOcD3U
unroll_loops lmOcObserveU := lmOcObserve fuel 0 with lmOcCaseU

end Twins

/-- Frozen expected LeanMiri table for `tb = false` (no borrow tracker). -/
def lmOcExpectedBasic : List LmOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .okScalar 5, .ub,
   .okRetagPair 5 5, .okRetagPair 5 5, .okRetagPair 4 9, .okRetagPair 5 5, .okRetagPair 5 5,
   .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- Frozen expected LeanMiri table for `tb = true` (Tree Borrows; only `11`, `13`, `14` differ). -/
def lmOcExpectedTb : List LmOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .okScalar 5, .ub,
   .okRetagPair 5 5, .ub, .okRetagPair 4 9, .ub, .ub, .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- **Kernel-checked 44-cell LeanMiri table** (`22` cases × no borrow tracker / Tree Borrows),
every cell executed by vendored definitions (`Step.step` for `D1`, the vendored memory /
Tree Borrows / validity harness otherwise) and closed by `decide +kernel` on the loop-unrolled
twin (`lmOcObserveU.eq_src`, itself a kernel-checked theorem). -/
theorem lmOcObserve_table :
    (List.range lmOcCaseCount).map (lmOcObserve false) = lmOcExpectedBasic ∧
    (List.range lmOcCaseCount).map (lmOcObserve true) = lmOcExpectedTb := by
  rw [lmOcObserveU.eq_src]
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Out-of-range cases are fail-closed `.unsupported` in both modes. -/
theorem lmOcObserve_out_of_range (tb : Bool) (idx : Nat) (h : lmOcCaseCount ≤ idx) :
    lmOcObserve tb idx = .unsupported := by
  unfold lmOcCaseCount at h
  have hNone : lmOcCase tb idx = none := by
    unfold lmOcCase
    split <;> first | rfl | omega
  unfold lmOcObserve
  rw [hNone]

/-- Exact mode-sensitivity predicate: only the protected foreign-write cases `11`, `13`, `14`. -/
def lmOcCaseModeSensitive : Nat → Bool
  | 11 | 13 | 14 => true
  | _ => false

/-- **Exact LeanMiri Tree Borrows mode-sensitivity `↔`**. -/
theorem lmOcObserve_mode_sensitivity :
    ∀ idx, idx < lmOcCaseCount →
      (lmOcObserve false idx ≠ lmOcObserve true idx ↔ lmOcCaseModeSensitive idx = true) := by
  have hB := lmOcObserve_table.1
  have hT := lmOcObserve_table.2
  have hAll : ((List.range lmOcCaseCount).all fun idx =>
      decide ((lmOcExpectedBasic[idx]? ≠ lmOcExpectedTb[idx]?) ↔
        lmOcCaseModeSensitive idx = true)) = true := by decide
  intro idx hi
  have cellB : some (lmOcObserve false idx) = lmOcExpectedBasic[idx]? := by
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : some (lmOcObserve true idx) = lmOcExpectedTb[idx]? := by
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB, ← cellT] at hIff
  simpa [Option.some.injEq] using hIff

/-! ## §2. Direct Trusted `stepMirFn` Execution of the Shared Fixtures (`lmOcTrustedObserve`) -/

section TrustedRunner

open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics

/-- Observe a terminal Trusted outcome (`D1` scalar, `D2` pair, `D3` any normal return). -/
def lmOcTrustedObsOf (idx : Nat) : OcTrustedOutcome → LmOcFpObs
  | .ret (.scalar ⟨b, _⟩) => if idx < 10 then .okScalar b else if idx < 16 then .unsupported else .okPtrValid
  | .ret (.aggregate 0 [.scalar ⟨r, _⟩, .scalar ⟨v, _⟩]) =>
    if idx < 10 then .unsupported else if idx < 16 then .okRetagPair r v else .okPtrValid
  | .ret _ => if 16 ≤ idx then .okPtrValid else .unsupported
  | .ub => .ub
  | _ => .unsupported

/-- **Real Trusted observer** on the shared fixtures (`tb = false`: callees' no-borrow-tracker
image `ocEraseRetags`). -/
def lmOcTrustedObserve (tb : Bool) (idx : Nat) : LmOcFpObs :=
  match ocCaseFixture? idx with
  | none => .unsupported
  | some (body, callees) =>
    lmOcTrustedObsOf idx (ocRunTrustedRaw body (if tb then callees else callees.map ocEraseRetags))

end TrustedRunner

/-- Frozen expected Trusted table for `tb = false` (shared fixtures through `stepMirFn`). -/
def lmOcTrustedExpectedBasic : List LmOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .unsupported, .ub,
   .okRetagPair 5 5, .okRetagPair 5 5, .okRetagPair 4 9, .okRetagPair 5 5, .okRetagPair 5 5,
   .okRetagPair 3 9, .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- Frozen expected Trusted table for `tb = true`. -/
def lmOcTrustedExpectedTb : List LmOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .unsupported, .ub,
   .okRetagPair 5 5, .ub, .okRetagPair 4 9, .ub, .ub, .okRetagPair 3 9, .okPtrValid, .okPtrValid,
   .ub, .ub, .ub, .ub]

/-- **Kernel-checked 44-cell Trusted table on the shared fixtures** (constructive). -/
theorem lmOcTrustedObserve_table :
    (List.range lmOcCaseCount).map (lmOcTrustedObserve false) = lmOcTrustedExpectedBasic ∧
    (List.range lmOcCaseCount).map (lmOcTrustedObserve true) = lmOcTrustedExpectedTb := by
  constructor <;> kernel_rfl

/-- **`D1` (b) Step-vs-Trusted correspondence and 44-cell cross-authority agreement
(kernel-checked)**: the LeanMiri cells (vendored `Step.step` on the cast-erased fixtures `0`–`3`,
`9`, the vendored memory harness elsewhere) agree with Trusted `stepMirFn` on the `.opaqueCast`
fixtures on every case except the documented fail-closed boundary `8` (Trusted `.unsupported`;
LeanMiri reads `5`), in both modes. -/
theorem lmOc_trusted_agreement :
    ((List.range lmOcCaseCount).all fun idx =>
      idx == 8 || (lmOcObserve false idx == lmOcTrustedObserve false idx &&
        lmOcObserve true idx == lmOcTrustedObserve true idx)) = true := by
  rw [lmOcObserveU.eq_src]
  decide +kernel

/-! ## §3. `D1` Phase Boundary, `Step.step` Adapter Boundaries, and Universal Laws -/

section UniversalLaws

open Miri.ABI Miri.Memory Miri.Interpreter LeanMiriSpec.HeapAllocAndWidePtrLM

/-- `D1` (a) **vendored phase-boundary rejection (universal)**: for every projection context,
base, place, and cast type, vendored `Miri.Interpreter.project` rejects `OpaqueCast` with
`ProjectionError.invariant "OpaqueCast after borrowck"` and vendored
`Miri.Interpreter.PlaceDynamic.project` with `StepError.invalidProgram "OpaqueCast after borrowck"`
— neither is a UB verdict. -/
theorem lm_opaqueCast_phase_boundary {Prov : Type} [PointerProvenance Prov]
    (cx : ProjectionCx Prov) (base : OpTy Prov) (ty : Miri.MIR.TyId)
    {S C E : Type} (h : PlaceProjectionHooks Prov S C E) (choice : C) (place : RuntimePlace Prov) :
    project cx base (.OpaqueCast ty) = .error (.invariant "OpaqueCast after borrowck") ∧
    PlaceDynamic.project h choice place (.OpaqueCast ty) =
      throw (.invalidProgram "OpaqueCast after borrowck") ∧
    (StepError.invalidProgram "OpaqueCast after borrowck" ≠ .undefinedBehavior "OpaqueCast after borrowck") :=
  ⟨rfl, rfl, by simp⟩

/-- The phase-boundary observation of a `D1` fixture place: `phaseBoundary` when the
translated place projects through `OpaqueCast` (vendored `project` rejects it), otherwise the
fixture is outside the boundary. -/
def lmOcPhaseObs (proj : List Miri.MIR.ProjectionElem) : LmOcFpObs :=
  if proj.any (fun e => match e with | .OpaqueCast _ => true | _ => false) then .phaseBoundary
  else .unsupported

/-- `D1` **translated cast places hit the phase boundary**: the translated places of the cast
fixtures carry `Miri.MIR.ProjectionElem.OpaqueCast`. -/
theorem lm_translated_cast_places_phase_boundary :
    lmOcPhaseObs (LeanMiriSpec.Correspondence.translatePlace (ocLoc 1 [ocCastU32])).projection.toList =
      .phaseBoundary ∧
    lmOcPhaseObs (LeanMiriSpec.Correspondence.translatePlace
      (ocLoc 2 [.opaqueCast ocRawConstU32Ty, .deref])).projection.toList = .phaseBoundary ∧
    lmOcPhaseObs (LeanMiriSpec.Correspondence.translatePlace (ocErasePlace (ocLoc 1 [ocCastU32]))).projection.toList =
      .unsupported := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- `D1` **pinned `Step.step` adapter boundaries**: the `.opaqueCast` fixtures themselves never
reach a value through the adapter (`projected operand in scalar rvalue` /
`projected write to uninitialized local`), and the cast-erased `Deinit` (`5`, a statement absent
from pinned rustc MIR) and glue-free `Drop` (`7`) fixtures are `.unsupported`, which is why those
two cells rest on vendored `Allocation.writeUninit`. -/
theorem lm_step_adapter_boundaries :
    ocRunStep ocCase0Mir ocU32Ty = .error (.unsupported "projected operand in scalar rvalue") ∧
    ocRunStep ocCase3Mir ocU32Ty = .error (.undefinedBehavior "projected write to uninitialized local") ∧
    ocRunStep (ocEraseBody ocCase5Mir) ocU32Ty =
      .error (.unsupported "non-scalar constant in scalar rvalue evaluation") ∧
    ocRunStep (ocEraseBody ocCase7Mir) ocU32Ty = .error (.unsupported "drop terminator") ∧
    lmOcObserve false 5 = .ub ∧ lmOcObserve false 7 = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [lmOcObserveU.eq_src]; decide +kernel
  · rw [lmOcObserveU.eq_src]; decide +kernel

/-- `D2` **vendored `RetagPolicy.create` protector law (universal)**: an `FnEntry` retag attaches
a `StrongProtector` to references and a `WeakProtector` to `Box`; any other non-`None` mode
attaches no protector. -/
theorem lm_retagPolicy_protector (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
    (kind : Miri.TreeBorrows.RetagPolicy.ReferenceKind) (mode : Miri.TreeBorrows.RetagPolicy.RetagMode)
    (config : Miri.TreeBorrows.RetagPolicy.PolicyConfig) (p : Miri.TreeBorrows.RetagPolicy.NewPermission)
    (h : Miri.TreeBorrows.RetagPolicy.create facts kind mode config = some p) :
    p.protector = if mode = .FnEntry then
      some (if kind = .Box then .WeakProtector else .StrongProtector) else none := by
  unfold Miri.TreeBorrows.RetagPolicy.create at h
  simp only [Id.run, pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      by_cases hm : mode = .FnEntry <;> by_cases hk : kind = .Box <;> simp [hm, hk]

/-- `D2` **callee-only retag mode `None` never creates a permission (vendored, universal)**: a
parameter that the callee does not retag (`*mut u8`, `RetagMode.None`) gets no protector. -/
theorem lm_retagPolicy_none (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
    (kind : Miri.TreeBorrows.RetagPolicy.ReferenceKind) (config : Miri.TreeBorrows.RetagPolicy.PolicyConfig) :
    Miri.TreeBorrows.RetagPolicy.create facts kind .None config = none :=
  Miri.TreeBorrows.RetagPolicy.none_mode_never_creates_permission facts kind config

/-- `D2` non-vacuity: the `&mut u8` / `&u8` `FnEntry` policies of cases `11`–`15` carry strong
protectors and the `Default` policy carries none. -/
theorem lm_retagPolicy_fnEntry_witness :
    ((Miri.TreeBorrows.RetagPolicy.create lmFrozenFacts .Mutable .FnEntry ⟨true, false⟩).map
      (·.protector)) = some (some .StrongProtector) ∧
    ((Miri.TreeBorrows.RetagPolicy.create lmFrozenFacts .Shared .FnEntry ⟨true, false⟩).map
      (·.protector)) = some (some .StrongProtector) ∧
    ((Miri.TreeBorrows.RetagPolicy.create lmFrozenFacts .Mutable .Default ⟨true, false⟩).map
      (·.protector)) = some none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- `D3` **zero-sized accesses are always dereferenceable (vendored, universal)**. -/
theorem lm_checkPtrAccess_zero_size {Prov ProvExtra : Type} (t : PointerArithmetic)
    (ptr : Pointer (Option Prov)) (msg : CheckInAllocMsg) (r : PointerResolver Prov ProvExtra)
    (l : LiveAllocationLookup) :
    checkPtrAccess t ptr Size.ZERO msg r l = .ok () := by
  have hs : sizeAsI64 Size.ZERO = .ok 0 := by simp [sizeAsI64, Size.ZERO]
  simp only [checkPtrAccess, hs, bind, Except.bind, Miri.Memory.zero_sized_check_skips_resolution,
    pure, Except.pure]

/-- `D3` **the safe-pointer valid range excludes exactly null (universal)**. -/
theorem lm_safe_ptr_range_contains_iff (v : U128) :
    WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩ v = true ↔
      1 ≤ v.toNat ∧ v.toNat ≤ 2 ^ 64 - 1 := by
  simp [WrappingRange.contains]

/-- `D3` the safe-pointer validity layout is `pointerLayoutData true` (`[1, 2^64 - 1]`). -/
theorem lm_safe_ptr_validity_layout :
    lmOcSafePtrValidity = .ok ⟨Size.ofBytes 8, ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2 ^ 64 - 1)⟩⟩ :=
  rfl

/-- `D3` **vendored `scalarMayBeNull` on integers (universal)**. -/
theorem lm_scalarMayBeNull_int {K User : Type} (i : ScalarInt) :
    ValidityMachine.scalarMayBeNull (K := K) (User := User) (Scalar.fromScalarInt i) = pure i.isNull :=
  rfl

end UniversalLaws

/-! ## §4. Capstones -/

/-- **Episode 1 LeanMiri capstone**: the 44-cell table, fail-closed range, exact mode sensitivity,
the Trusted tables and cross-authority agreement outside the documented boundary `8`, the vendored
phase-boundary law, and the `D2` / `D3` universal laws. -/
theorem ep1_lean_miri_opaquecast_fnentry_capstone :
    ((List.range lmOcCaseCount).map (lmOcObserve false) = lmOcExpectedBasic ∧
      (List.range lmOcCaseCount).map (lmOcObserve true) = lmOcExpectedTb) ∧
    (∀ tb idx, lmOcCaseCount ≤ idx → lmOcObserve tb idx = .unsupported) ∧
    (∀ idx, idx < lmOcCaseCount →
      (lmOcObserve false idx ≠ lmOcObserve true idx ↔ lmOcCaseModeSensitive idx = true)) ∧
    type_of% lmOcTrustedObserve_table ∧
    type_of% lmOc_trusted_agreement ∧
    type_of% @lm_opaqueCast_phase_boundary ∧
    type_of% lm_translated_cast_places_phase_boundary ∧
    type_of% lm_step_adapter_boundaries ∧
    type_of% @lm_retagPolicy_protector ∧
    type_of% @lm_retagPolicy_none ∧
    type_of% lm_retagPolicy_fnEntry_witness ∧
    type_of% @lm_checkPtrAccess_zero_size ∧
    type_of% @lm_safe_ptr_range_contains_iff ∧
    type_of% lm_safe_ptr_validity_layout ∧
    type_of% @lm_scalarMayBeNull_int ∧
    lmOcCaseCount = ocFixtureCaseCount :=
  ⟨lmOcObserve_table, lmOcObserve_out_of_range, lmOcObserve_mode_sensitivity, lmOcTrustedObserve_table,
   lmOc_trusted_agreement,
   @lm_opaqueCast_phase_boundary, lm_translated_cast_places_phase_boundary, lm_step_adapter_boundaries,
   @lm_retagPolicy_protector, @lm_retagPolicy_none, lm_retagPolicy_fnEntry_witness,
   @lm_checkPtrAccess_zero_size, @lm_safe_ptr_range_contains_iff, lm_safe_ptr_validity_layout,
   @lm_scalarMayBeNull_int, rfl⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict root isolation: ZERO `MiniRustSpec.*` and ZERO `Anneal.*` imports, even transitively!
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM"
  let ns := `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM
  -- 2. Bridge-reality audit: our theorems transitively reach the real vendored Miri constants.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `lmOcObserve_table, `Miri.Interpreter.Step.step),
      (ns ++ `lmOcObserve_table, `Miri.Interpreter.Discriminant.tagForVariant),
      (ns ++ `lmOcObserve_table, `Miri.Memory.Allocation.writeUninit),
      (ns ++ `lmOcObserve_table, `Miri.Memory.Validity.checkScalar),
      (ns ++ `lmOcObserve_table, `Miri.Memory.checkPtrAccess),
      (ns ++ `lmOcObserve_table, `Miri.Memory.checkPtrAlign),
      (ns ++ `lmOcObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmRetag),
      (ns ++ `lmOcObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmEndCall),
      (ns ++ `lmOcObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmStore),
      (ns ++ `lmOcObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmLoad),
      (ns ++ `lmOcObserve_table, `LeanMiriSpec.HeapAllocAndWidePtrLM.lmDeallocate),
      (ns ++ `lmOcObserve_table, `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.ocEraseBody),
      (ns ++ `lmOcTrustedObserve_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `lm_opaqueCast_phase_boundary, `Miri.Interpreter.project),
      (ns ++ `lm_opaqueCast_phase_boundary, `Miri.Interpreter.PlaceDynamic.project),
      (ns ++ `lm_step_adapter_boundaries, `Miri.Interpreter.Step.step),
      (ns ++ `lm_retagPolicy_protector, `Miri.TreeBorrows.RetagPolicy.create),
      (ns ++ `lm_checkPtrAccess_zero_size, `Miri.Memory.checkPtrAccess),
      (ns ++ `lm_scalarMayBeNull_int, `Miri.Interpreter.ValidityMachine.scalarMayBeNull) ]
  for (thm, req) in bridgeReq do
    let some ci := env.find? thm | throwError "bridge audit: {thm} missing"
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := ci.type.getUsedConstants
    if let .defnInfo v := ci then
      todo := todo ++ v.value.getUsedConstants
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == req then break
      if ns.isPrefixOf n then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach real {req}"
  -- 3. Standard-3-axiom purity, constructive purity of the Trusted tables and phase-boundary laws,
  -- and a non-vacuous theorem count floor. (The vendored `ScalarInt` / loop-unrolling machinery
  -- behind `lmOcObserve_table`, `lm_step_adapter_boundaries`, and `lm_scalarMayBeNull_int` uses
  -- `Classical.choice` upstream, so those stay on the standard-3 allowlist.)
  let constructive : List Lean.Name :=
    [ ns ++ `lmOcTrustedObserve_table, ns ++ `lm_opaqueCast_phase_boundary,
      ns ++ `lm_translated_cast_places_phase_boundary,
      ns ++ `lm_retagPolicy_fnEntry_witness, ns ++ `lm_safe_ptr_validity_layout ]
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
      if constructive.contains c && a == ``Classical.choice then
        throwError "{c} must be constructive but depends on Classical.choice"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 15 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM
