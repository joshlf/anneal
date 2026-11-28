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
import MiniRustSpec.Interp
import MiniRustSpec.Correspondence.Translate
import MiniRustSpec.CrossFrameRefAndPanicMR
import MiniRustSpec.WideDstAndMaybeUninitMR

/-!
# Episode 1 MiniRust Authority: `ProjectionElem.opaqueCast`, Callee-Only `FnEntry` Protectors
# (`rust#166253`), and Machine-Backed Safe-Pointer Dereferenceability
# (`MiniRustSpec.OpaqueCastAndFnEntryProtectorMR`)

Operational correspondence between unmodified MiniRust `d821c6e3` (`MiniRustSpec.Interp` over
both `BasicMemory<x86_64>` `Mach` and `TreeBorrowsMemory<x86_64>` `MachTB`) and unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics` (`stepMirFn`) on the frozen 22-case (`0..21`) × 2-mode
matrix shared with `LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`:

* `D1` (`0..9`): `ProjectionElem.opaqueCast` in every place context — `copy` / `move` through a
  (nested) cast chain, use after move, nested cast-chain assignment, cast-then-field into an
  uninitialized local, `Deinit`, `SetDiscriminant` + `Rvalue.discriminant`, `Drop`, the
  fail-closed dereference directly below a leading cast (`8`), and the uninitialized-read UB
  non-masking control (`9`). Every Trusted cell runs the `.opaqueCast` fixture; every MiniRust
  cell runs the cast-erased program (MiniRust has no `OpaqueCast`, and upstream `minimize` aborts
  on it). `mrOcTrusted_cast_erasure` proves that Trusted on the `.opaqueCast` fixture agrees with
  Trusted on its cast-erased image (`ocEraseBody`) on every `D1` case except the documented
  boundary `8`, where the cast fixture fails closed (`.unsupported`) and the erased one reads `5`.
* `D2` (`10..15`): callee-only `FnEntry` protectors across transmuted function pointers in BOTH
  directions. Case `10` is the post-`#166253` callee-only view (caller passes its `&mut u8` and
  parent `*mut u8` into a `fn(*mut u8, *mut u8)` callee: no protector, the aliased foreign write
  succeeds in both modes); case `11` is the pre-`#166253` caller-signature contrast (the EXACT SAME
  caller and arguments retagged at the caller's `&mut u8` signature: OK without a borrow tracker, UB
  under Tree Borrows); case `12` is the direct `&mut u8` positive return/release case; case `13` is
  the reverse transmutation (`fn(*mut u8, *mut u8)` caller view calling a `fn(&mut u8, *mut u8)`
  callee: callee attaches `FnEntry` strong protector -> TB UB on foreign write); cases `14`–`15` are
  the `&u8` (`Frozen`) protected-foreign-write negative and positive scenarios. The MiniRust callers
  of `10`, `11`, and `13` invoke the callee through a transmuted function pointer.
* `D3` (`16..21`): `checkPtr` / `checkPtrM (m := some mach)` (`CM.dereferenceable` /
  `ConcurrentMemory.dereferenceable`) on safe pointers (`&T`, `Box<T>`) over both machines: valid,
  zero-sized, null (sized & ZST), unaligned, out-of-bounds, and deallocated, with complete `Ref` and
  `Box` `some mach` vs `none` contrasts on both `Mach` and `MachTB`, plus the universal
  `mr_checkPtr_sized_never_unsupported` and `mr_checkPtrM_sized_never_unsupported_bm_tbm` laws.

Trusted has no borrow-tracker switch: its `tb = false` cells run the callees' no-borrow-tracker
image (`ocEraseRetags`, every `Retag` replaced by `Nop`), mirroring MiniRust's universally no-op
`BasicMemory` retag (`mr_basic_retag_fnEntry_irrelevant`).

Root isolation: imports strictly `Lean`, `Trusted`, and `MiniRustSpec.*` (zero `Anneal.*`,
`Miri.*`, or `LeanMiriSpec.*`; verified by the trailing `run_cmd` audit).
-/

namespace MiniRustSpec.OpaqueCastAndFnEntryProtectorMR

set_option Elab.async false

/-! ## §0. Frozen Observation Interface, Kernel Helpers, and Shared `CapturedMir` Fixtures -/

/-- Frozen cross-authority observation domain (constructor order shared identically with
`LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM.LmOcFpObs`). -/
inductive MrOcFpObs : Type where
  /-- Normal termination with a scalar result. -/
  | okScalar (val : Nat)
  /-- Normal return of a cross-frame call: `(callee result, caller referent after the call)`. -/
  | okRetagPair (retVal : Nat) (referentVal : Nat)
  /-- A safe pointer accepted by validity / dereferenceability. -/
  | okPtrValid
  /-- Undefined behavior. -/
  | ub
  /-- A phase-boundary rejection (`OpaqueCast after borrowck`); never produced by MiniRust. -/
  | phaseBoundary
  /-- Fail-closed unsupported construct or out-of-range case. -/
  | unsupported
  /-- MiniRust well-formedness specification panic. -/
  | specPanic
  deriving DecidableEq, Repr

/-- Number of canonical cases (`0..21`, 44 mode cells). -/
def mrOcCaseCount : Nat := 22

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
def ocCombine (a b : MrOcFpObs) : MrOcFpObs := if a = b then a else .unsupported

/-! ### Shared `CapturedMir` fixtures

Every definition in this section is shared verbatim (same text, same opened namespaces) with
`LeanMiriSpec.OpaqueCastAndFnEntryProtectorLM`, so Episode 2's cross-root bridge can lock each
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
transmuted `fn(&mut u8, *mut u8)`): caller passes its `&mut u8` (`_3`) and parent `*mut u8` (`_2`),
callee takes `*mut u8` with no `FnEntry` retag, and foreign write `*_2 = 5` disables unprotected
`_3` without UB in either mode. -/
def ocCase10Callee : CapturedMir :=
  ocBody "oc::case10_callee" 2 [ocU8Ty, ocRawMutU8Ty, ocRawMutU8Ty]
    [ocBb [.assign (ocLoc 2 [.deref]) (.use (ocConstU8 5)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
def ocCase10Mir : CapturedMir :=
  ocD2Main "oc::case10_main" "oc::case10_callee" (.ref (.mut false) (ocLoc 2 [.deref])) ocMutRefU8Ty
    [.copy (ocLoc 3), .copy (ocLoc 2)] []
/-- Case 11 callee (pre-`#166253` caller-signature contrast): the SAME caller, arguments `(_3, _2)`,
and body as case `10`, but retagged on entry at the caller's `&mut u8` signature (`RetagKind.fnEntry`
on `_1`). -/
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
/-- Case 13 callee (`fn(&mut u8, *mut u8)`, reverse transmutation: caller invokes through a
`fn(*mut u8, *mut u8)` view passing `(_2, _2)`): callee's own `FnEntry` retag protects `_1`, local
write `*_1 = 4` activates it, then aliased foreign write `*_2 = 5` violates the strong protector. -/
def ocCase13Callee : CapturedMir :=
  ocBody "oc::case13_callee" 2 [ocU8Ty, ocMutRefU8Ty, ocRawMutU8Ty]
    [ocBb [.retag .fnEntry (ocLoc 1),
           .assign (ocLoc 1 [.deref]) (.use (ocConstU8 4)),
           .assign (ocLoc 2 [.deref]) (.use (ocConstU8 5)),
           .assign (ocLoc 0) (.use (.copy (ocLoc 2 [.deref])))] .return_]
def ocCase13Mir : CapturedMir :=
  ocD2Main "oc::case13_main" "oc::case13_callee" (.ref (.mut false) (ocLoc 2 [.deref])) ocMutRefU8Ty
    [.copy (ocLoc 2), .copy (ocLoc 2)] []
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

/-! ## §1. Direct Trusted `stepMirFn` Execution (`mrOcTrustedObserve`) -/

section TrustedRunner

open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics

/-- How the return value of a fixture is observed. -/
inductive OcRetKind : Type where
  /-- A scalar result (`D1`). -/
  | scalar
  /-- A `(callee result, caller referent)` pair (`D2`). -/
  | pair
  /-- Any normal return after a dereference through the safe pointer (`D3`). -/
  | ptrValid

/-- The return kind of each case. -/
def ocRetKindOf (idx : Nat) : OcRetKind :=
  if idx < 10 then .scalar else if idx < 16 then .pair else .ptrValid

/-- Observe a terminal Trusted outcome. -/
def mrOcTrustedObsOf : OcRetKind → OcTrustedOutcome → MrOcFpObs
  | .scalar, .ret (.scalar ⟨b, _⟩) => .okScalar b
  | .pair, .ret (.aggregate 0 [.scalar ⟨r, _⟩, .scalar ⟨v, _⟩]) => .okRetagPair r v
  | .ptrValid, .ret _ => .okPtrValid
  | _, .ub => .ub
  | _, _ => .unsupported

/-- **Real Trusted observer**: executes `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the
frozen `CapturedMir` fixture of each case (with its linked callees). In `tb = false` the callees
run their no-borrow-tracker image `ocEraseRetags`. Fail-closed `.unsupported` for `idx ≥ 22`. -/
def mrOcTrustedObserve (tb : Bool) (idx : Nat) : MrOcFpObs :=
  match ocCaseFixture? idx with
  | none => .unsupported
  | some (body, callees) =>
    mrOcTrustedObsOf (ocRetKindOf idx)
      (ocRunTrustedRaw body (if tb then callees else callees.map ocEraseRetags))

/-- The Trusted run of the cast-erased image (`ocEraseBody`) of each `D1` fixture. -/
def mrOcTrustedErasedObserve (idx : Nat) : MrOcFpObs :=
  match ocCaseFixture? idx with
  | none => .unsupported
  | some (body, callees) => mrOcTrustedObsOf (ocRetKindOf idx) (ocRunTrustedRaw (ocEraseBody body) callees)

end TrustedRunner

/-- Frozen expected Trusted table for `tb = false`. -/
def mrOcTrustedExpectedBasic : List MrOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .unsupported, .ub,
   .okRetagPair 5 5, .okRetagPair 5 5, .okRetagPair 4 9, .okRetagPair 5 5, .okRetagPair 5 5,
   .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- Frozen expected Trusted table for `tb = true` (only `11`, `13`, `14` differ). -/
def mrOcTrustedExpectedTb : List MrOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .unsupported, .ub,
   .okRetagPair 5 5, .ub, .okRetagPair 4 9, .ub, .ub, .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- **Kernel-checked 44-cell Trusted table**: every cell executes `stepMirFn` on its fixture. -/
theorem mrOcTrustedObserve_table :
    (List.range mrOcCaseCount).map (mrOcTrustedObserve false) = mrOcTrustedExpectedBasic ∧
    (List.range mrOcCaseCount).map (mrOcTrustedObserve true) = mrOcTrustedExpectedTb := by
  constructor <;> kernel_rfl

/-- **`D1` Trusted cast-erasure correspondence (kernel-checked)**: on every `D1` case, Trusted
`stepMirFn` on the `.opaqueCast` fixture and on its cast-erased image agree, except the documented
fail-closed boundary `8` (a dereference directly below a leading cast chain), where the cast
fixture is `.unsupported` while the erased fixture reads `5`. -/
theorem mrOcTrusted_cast_erasure :
    (List.range 10).map (fun idx => (mrOcTrustedObserve false idx, mrOcTrustedErasedObserve idx)) =
      [(.okScalar 7, .okScalar 7), (.okScalar 7, .okScalar 7), (.ub, .ub),
       (.okScalar 42, .okScalar 42), (.okScalar 9, .okScalar 9), (.ub, .ub),
       (.okScalar 1, .okScalar 1), (.ub, .ub), (.unsupported, .okScalar 5), (.ub, .ub)] := by
  kernel_rfl

/-- `D1` cast-erasure agreement as a quantified statement over `idx < 10`, `idx ≠ 8`. -/
theorem mrOcTrusted_cast_erasure_agree (idx : Nat) (hi : idx < 10) (h8 : idx ≠ 8) :
    mrOcTrustedObserve false idx = mrOcTrustedErasedObserve idx := by
  have h := congrArg (fun l => l[idx]?) mrOcTrusted_cast_erasure
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at h
  have hc : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨ idx = 7 ∨
      idx = 9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- Out-of-range Trusted cases are fail-closed `.unsupported`. -/
theorem mrOcTrustedObserve_out_of_range (tb : Bool) (idx : Nat) (h : mrOcCaseCount ≤ idx) :
    mrOcTrustedObserve tb idx = .unsupported := by
  unfold mrOcCaseCount at h
  have hNone : ocCaseFixture? idx = none := by
    unfold ocCaseFixture?
    split <;> first | rfl | omega
  unfold mrOcTrustedObserve
  rw [hNone]

/-- Exact mode-sensitivity predicate: only the protected foreign-write cases `11`, `13`, `14`
flip between the modes. -/
def ocCaseModeSensitive : Nat → Bool
  | 11 | 13 | 14 => true
  | _ => false

/-- **Exact Trusted mode-sensitivity `↔`**: `tb = false` and `tb = true` disagree on `idx < 22`
if and only if `idx ∈ {11, 13, 14}`. -/
theorem mrOcTrustedObserve_mode_sensitivity :
    ∀ idx, idx < mrOcCaseCount →
      (mrOcTrustedObserve false idx ≠ mrOcTrustedObserve true idx ↔ ocCaseModeSensitive idx = true) := by
  have hB := mrOcTrustedObserve_table.1
  have hT := mrOcTrustedObserve_table.2
  have hAll : ((List.range mrOcCaseCount).all fun idx =>
      decide ((mrOcTrustedExpectedBasic[idx]? ≠ mrOcTrustedExpectedTb[idx]?) ↔
        ocCaseModeSensitive idx = true)) = true := by decide
  intro idx hi
  have cellB : some (mrOcTrustedObserve false idx) = mrOcTrustedExpectedBasic[idx]? := by
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : some (mrOcTrustedObserve true idx) = mrOcTrustedExpectedTb[idx]? := by
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB, ← cellT] at hIff
  simpa [Option.some.injEq] using hIff

/-! ## §2. Canonical 22-Case MiniRust Program Suite on `Mach` and `MachTB` (`mrOcObserve`)

Root programs store `(kind, a, b)` in locals `(0, 1, 2)` before `Intrinsic.Exit`:
`kind = 0 ⇒ okScalar a`, `1 ⇒ okRetagPair a b`, and `2 ⇒` the pointer in `_4` is validated by
`checkPtrM _ ptrTy (some m)` (`CM.dereferenceable`) at every safe pointer type of the case. -/

section MiniRustPrograms

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.CrossFrameRefAndPanicMR MiniRustSpec.WideDstAndMaybeUninitMR

@[reducible] def ocMrU8Pointee : PointeeInfo :=
  { layout := .Sized ⟨1⟩ ⟨1⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true,
    unpin := true }
@[reducible] def ocMrUnitPointee : PointeeInfo :=
  { layout := .Sized ⟨0⟩ ⟨1⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true,
    unpin := true }
@[reducible] def ocMrMutRefU8Ty : «Type» := .Ptr (.Ref .Mutable ocMrU8Pointee)
@[reducible] def ocMrShrRefU8Ty : «Type» := .Ptr (.Ref .Immutable ocMrU8Pointee)
@[reducible] def ocMrPairTy : «Type» := .Tuple [(⟨0⟩, u32Ty), (⟨4⟩, u32Ty)] ⟨⟨8⟩, ⟨4⟩, none⟩ none
@[reducible] def ocMrTwoVarPayloadTy : «Type» := .Tuple [(⟨4⟩, u32Ty)] ⟨⟨8⟩, ⟨4⟩, none⟩ none

/-- Variant table of `TwoVar` (`#[repr(u8)] enum TwoVar { A(u32) = 0, B(u32) = 1 }`). -/
def ocMrTwoVarVariants : Map Int Variant :=
  ⟨[(0, ⟨ocMrTwoVarPayloadTy, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 0))]⟩⟩),
    (1, ⟨ocMrTwoVarPayloadTy, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩⟩)]⟩
/-- `TwoVar`: 8 bytes, align 4, direct `u8` tag at `0`, payload at `4`. -/
def ocMrTwoVarTy : «Type» :=
  .Enum ocMrTwoVarVariants ⟨.Unsigned, ⟨1⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩) ⟨8⟩ ⟨4⟩

@[reducible] def ocCU8 (n : Int) : ValueExpr := .Constant (.Int n) mrU8Ty

/-! ### `D1` (cast-erased programs; `x = _3`) -/

/-- Case 0: `_4 = _3` (copy), `_5 = _3` (still initialized). -/
def ocMrProg0 : Program :=
  wdProg [u32Ty, u32Ty, u32Ty]
    ([.Assign (wdLc 3) (cU32 7), .Assign (wdLc 4) (wdLd 3), .Assign (wdLc 5) (wdLd 3)] ++
     wdFinish 0 (wdToU64 (wdLd 4)) (wdCU64 0))
/-- Case 1: the move `_4 = move _3`, lowered as `Load` followed by `Deinit` (the Trusted
`evalOperand` / LeanMiri `annealEvalOperand` move-deinit slot transition). -/
def ocMrProg1 : Program :=
  wdProg [u32Ty, u32Ty]
    ([.Assign (wdLc 3) (cU32 7), .Assign (wdLc 4) (wdLd 3), .Deinit (wdLc 3)] ++
     wdFinish 0 (wdToU64 (wdLd 4)) (wdCU64 0))
/-- Case 2: use after the move of case `1`. -/
def ocMrProg2 : Program :=
  wdProg [u32Ty, u32Ty]
    ([.Assign (wdLc 3) (cU32 7), .Assign (wdLc 4) (wdLd 3), .Deinit (wdLc 3)] ++
     wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))
/-- Case 2 contrast: upstream `minimize` lowers `Operand::Move` to a plain `Load` (no
deinitialization), under which the use after move is NOT UB. -/
def ocMrProg2Minimize : Program :=
  wdProg [u32Ty, u32Ty]
    ([.Assign (wdLc 3) (cU32 7), .Assign (wdLc 4) (wdLd 3)] ++
     wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))
/-- Case 3: the erased nested cast assignment `_3 = 42`. -/
def ocMrProg3 : Program :=
  wdProg [u32Ty] ([.Assign (wdLc 3) (cU32 42)] ++ wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))
/-- Case 4: field write into an uninitialized tuple local `_3.1 = 9`, then `_3.1`. -/
def ocMrProg4 : Program :=
  wdProg [ocMrPairTy]
    ([.Assign (.Field (wdLc 3) 1) (cU32 9)] ++
     wdFinish 0 (wdToU64 (.Load (.Field (wdLc 3) 1))) (wdCU64 0))
/-- Case 5: `Deinit(_3)`, then `_3`. -/
def ocMrProg5 : Program :=
  wdProg [u32Ty]
    ([.Assign (wdLc 3) (cU32 7), .Deinit (wdLc 3)] ++ wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))
/-- Case 6: `_3 = TwoVar::A(7)`, `SetDiscriminant(_3, 1)`, `GetDiscriminant(_3)`. -/
def ocMrProg6 : Program :=
  wdProg [ocMrTwoVarTy]
    ([.Assign (wdLc 3) (.Variant 0 (.Tuple [cU32 7] ocMrTwoVarPayloadTy) ocMrTwoVarTy),
      .SetDiscriminant (wdLc 3) 1] ++
     wdFinish 0 (wdToU64 (.GetDiscriminant (wdLc 3))) (wdCU64 0))
/-- Case 7: the drop of a value without drop glue, lowered as `Deinit(_3)` (Trusted's
drop-elaboration model: the dropped place is de-initialized), then `_3`. -/
def ocMrProg7 : Program :=
  wdProg [u32Ty]
    ([.Assign (wdLc 3) (cU32 7), .Deinit (wdLc 3)] ++ wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))
/-- Case 7 contrast: upstream `minimize` lowers a glue-free `Drop` to a plain jump (no
de-initialization), under which the use after drop is NOT UB. -/
def ocMrProg7Minimize : Program :=
  wdProg [u32Ty] ([.Assign (wdLc 3) (cU32 7)] ++ wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))
/-- Case 8: the erased dereference `*_4` with `_4 = &raw const _3`. -/
def ocMrProg8 : Program :=
  wdProg [u32Ty, rawThinTy]
    ([.Assign (wdLc 3) (cU32 5), .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None))] ++
     wdFinish 0 (wdToU64 (.Load (.Deref (wdLd 4) u32Ty))) (wdCU64 0))
/-- Case 9: read of the live but uninitialized `_3`. -/
def ocMrProg9 : Program :=
  wdProg [u32Ty] (wdFinish 0 (wdToU64 (wdLd 3)) (wdCU64 0))

/-! ### `D2` (`x = _3`, `p = _4 = &raw mut x`, reference `_5`, result `_6`) -/

/-- The `D2` caller: `_7 = callee as fn`, `_8 = transmute(_7)`; calls the callee (through the
transmuted function pointer `_8` when `viaFnPtr`), then runs `post` and observes `(_6, x)`. -/
def ocMrD2Main (refExpr : ValueExpr) (refTy : «Type») (args : List ValueExpr)
    (post : List Statement) (viaFnPtr : Bool) : Function :=
  mkFn [(locId 0, u32Ty), (locId 1, mrU64Ty), (locId 2, mrU64Ty), (locId 3, mrU8Ty),
      (locId 4, rawThinTy), (locId 5, refTy), (locId 6, mrU8Ty), (locId 7, fnPtrTy),
      (locId 8, fnPtrTy)]
    [] (locId 0)
    [(bbId 0, ⟨[.StorageLive (locId 3), .StorageLive (locId 4), .StorageLive (locId 5),
        .StorageLive (locId 6), .StorageLive (locId 7), .StorageLive (locId 8),
        .Assign (wdLc 3) (ocCU8 3),
        .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
        .Assign (wdLc 5) refExpr,
        .Assign (wdLc 7) (cFn 1),
        .Assign (wdLc 8) (.UnOp (.Cast (.Transmute fnPtrTy)) (wdLd 7))],
       .Call (if viaFnPtr then wdLd 8 else cFn 1) .Rust (args.map .ByValue) (wdLc 6)
         (some (bbId 1)) none,
       .Regular⟩),
     (bbId 1, ⟨post ++ wdFinish 1 (wdToU64 (wdLd 6)) (wdToU64 (wdLd 3)), exitTerm, .Regular⟩)]

@[reducible] def ocMrDerefU8 (i : Nat) : PlaceExpr := .Deref (wdLd i) mrU8Ty

/-- Case 10: callee-only (`fn(*mut u8, *mut u8)` invoked through a transmuted `fn(&mut u8, *mut u8)`
pointer with the caller's actual `&mut u8` `_5` and parent `*mut u8` `_4`): `Validate(_1, true)` at
`*mut u8` is a no-op (no protector), so foreign write `*_2 = 5` succeeds in both modes. -/
def ocMrProg10 : Program :=
  let callee := mkFn [(locId 0, mrU8Ty), (locId 1, rawThinTy), (locId 2, rawThinTy)]
    [locId 1, locId 2] (locId 0)
    [(bbId 0, ⟨[.Validate (wdLc 1) true, .Assign (ocMrDerefU8 2) (ocCU8 5),
        .Assign (wdLc 0) (.Load (ocMrDerefU8 2))], .Return, .Regular⟩)]
  mkProg [(fnId 0, ocMrD2Main (.AddrOf (ocMrDerefU8 4) (.Ref .Mutable ocMrU8Pointee))
      ocMrMutRefU8Ty [wdLd 5, wdLd 4] [] true), (fnId 1, callee)]
/-- Case 11: the pre-`#166253` caller-signature contrast: the EXACT SAME caller and arguments
`(_5, _4)` as case `10`, but retagged on entry at the caller's `&mut u8` signature (`Validate(_1, true)`
on `&mut u8`). -/
def ocMrProg11 : Program :=
  let callee := mkFn [(locId 0, mrU8Ty), (locId 1, ocMrMutRefU8Ty), (locId 2, rawThinTy)]
    [locId 1, locId 2] (locId 0)
    [(bbId 0, ⟨[.Validate (wdLc 1) true, .Assign (ocMrDerefU8 2) (ocCU8 5),
        .Assign (wdLc 0) (.Load (ocMrDerefU8 2))], .Return, .Regular⟩)]
  mkProg [(fnId 0, ocMrD2Main (.AddrOf (ocMrDerefU8 4) (.Ref .Mutable ocMrU8Pointee))
      ocMrMutRefU8Ty [wdLd 5, wdLd 4] [] true), (fnId 1, callee)]
/-- Case 12: `&mut u8` callee writes `4`, returns; caller writes `9` afterwards. -/
def ocMrProg12 : Program :=
  let callee := mkFn [(locId 0, mrU8Ty), (locId 1, ocMrMutRefU8Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[.Validate (wdLc 1) true, .Assign (ocMrDerefU8 1) (ocCU8 4),
        .Assign (wdLc 0) (.Load (ocMrDerefU8 1))], .Return, .Regular⟩)]
  mkProg [(fnId 0, ocMrD2Main (.AddrOf (wdLc 3) (.Ref .Mutable ocMrU8Pointee)) ocMrMutRefU8Ty
      [wdLd 5] [.Assign (wdLc 3) (ocCU8 9)] false), (fnId 1, callee)]
/-- Case 13: reverse transmutation (`fn(*mut u8, *mut u8)` caller view passing `(_4, _4)` through a
transmuted fn pointer into a `fn(&mut u8, *mut u8)` callee): callee's `Validate(_1, true)` at `&mut u8`
attaches a strong protector, local write `*_1 = 4` succeeds, then foreign write `*_2 = 5` is TB UB. -/
def ocMrProg13 : Program :=
  let callee := mkFn [(locId 0, mrU8Ty), (locId 1, ocMrMutRefU8Ty), (locId 2, rawThinTy)]
    [locId 1, locId 2] (locId 0)
    [(bbId 0, ⟨[.Validate (wdLc 1) true, .Assign (ocMrDerefU8 1) (ocCU8 4),
        .Assign (ocMrDerefU8 2) (ocCU8 5), .Assign (wdLc 0) (.Load (ocMrDerefU8 2))],
       .Return, .Regular⟩)]
  mkProg [(fnId 0, ocMrD2Main (.AddrOf (ocMrDerefU8 4) (.Ref .Mutable ocMrU8Pointee))
      ocMrMutRefU8Ty [wdLd 4, wdLd 4] [] true), (fnId 1, callee)]
/-- Case 14: `&u8` callee (`Frozen` strong protector), foreign write `*_2 = 5`. -/
def ocMrProg14 : Program :=
  let callee := mkFn [(locId 0, mrU8Ty), (locId 1, ocMrShrRefU8Ty), (locId 2, rawThinTy)]
    [locId 1, locId 2] (locId 0)
    [(bbId 0, ⟨[.Validate (wdLc 1) true, .Assign (ocMrDerefU8 2) (ocCU8 5),
        .Assign (wdLc 0) (.Load (ocMrDerefU8 2))], .Return, .Regular⟩)]
  mkProg [(fnId 0, ocMrD2Main (.AddrOf (ocMrDerefU8 4) (.Ref .Immutable ocMrU8Pointee))
      ocMrShrRefU8Ty [wdLd 5, wdLd 4] [] false), (fnId 1, callee)]
/-- Case 15: `&u8` callee reads; caller writes `9` after the protector is released. -/
def ocMrProg15 : Program :=
  let callee := mkFn [(locId 0, mrU8Ty), (locId 1, ocMrShrRefU8Ty)] [locId 1] (locId 0)
    [(bbId 0, ⟨[.Validate (wdLc 1) true, .Assign (wdLc 0) (.Load (ocMrDerefU8 1))],
       .Return, .Regular⟩)]
  mkProg [(fnId 0, ocMrD2Main (.AddrOf (wdLc 3) (.Ref .Immutable ocMrU8Pointee)) ocMrShrRefU8Ty
      [wdLd 5] [.Assign (wdLc 3) (ocCU8 9)] false), (fnId 1, callee)]

/-! ### `D3` (the pointer under test is left in `_4`) -/

def ocMrProg16 : Program :=
  wdProg [u32Ty, rawThinTy]
    ([.Assign (wdLc 3) (cU32 7), .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None))] ++
     wdFinish 2 (wdCU64 0) (wdCU64 0))
def ocMrProg17 : Program :=
  wdProg [u32Ty, rawThinTy]
    ([.Assign (wdLc 4) (.Constant (.PointerWithoutProvenance 4) rawThinTy)] ++
     wdFinish 2 (wdCU64 0) (wdCU64 0))
def ocMrProg18 : Program :=
  wdProg [u32Ty, rawThinTy]
    ([.Assign (wdLc 4) (.Constant (.PointerWithoutProvenance 0) rawThinTy)] ++
     wdFinish 2 (wdCU64 0) (wdCU64 0))
def ocMrProg19 : Program :=
  wdProg [mrU64Ty, rawThinTy]
    ([.Assign (wdLc 3) (wdCU64 0),
      .Assign (wdLc 4) (ptrOff false (.AddrOf (wdLc 3) (.Raw .None)) 2)] ++
     wdFinish 2 (wdCU64 0) (wdCU64 0))
def ocMrProg20 : Program :=
  wdProg [u32Ty, rawThinTy]
    ([.Assign (wdLc 3) (cU32 7),
      .Assign (wdLc 4) (ptrOff false (.AddrOf (wdLc 3) (.Raw .None)) 4)] ++
     wdFinish 2 (wdCU64 0) (wdCU64 0))
def ocMrProg21 : Program :=
  wdProg [u32Ty, rawThinTy]
    ([.Assign (wdLc 3) (cU32 7), .Assign (wdLc 4) (.AddrOf (wdLc 3) (.Raw .None)),
      .StorageDead (locId 3)] ++
     wdFinish 2 (wdCU64 0) (wdCU64 0))

/-- `&u32` and `Box<u32>`. -/
def ocMrSizedPtrTys : List PtrType := [.Ref .Immutable u32Pointee, .Box u32Pointee]
/-- `&()` and `Box<()>`. -/
def ocMrZstPtrTys : List PtrType := [.Ref .Immutable ocMrUnitPointee, .Box ocMrUnitPointee]

/-! ### Observer -/

/-- Read local `loc` of the active frame through the real `evalPlaceM` / `placeLoadM`. -/
def ocReadLocalM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (loc : Nat) :
    Option (Value M) :=
  match evalPlaceM m (.Local (locId loc)) with
  | .ok ((place, ty), m1) =>
    match placeLoadM m1 place ty with
    | .ok (v, _) => some v
    | .error _ => none
  | .error _ => none

def ocReadNatM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (loc : Nat) : Option Nat :=
  match ocReadLocalM m loc with
  | some (.Int i) => if 0 ≤ i then some i.toNat else none
  | _ => none

def ocObsOfStop : Stop → MrOcFpObs
  | .ub _ => .ub
  | .specPanic _ => .specPanic
  | _ => .unsupported

/-- Observe a `check_ptr` result. -/
def ocCheckObs (r : Interp Unit) : MrOcFpObs :=
  match r with
  | .ok () => .okPtrValid
  | .error s => ocObsOfStop s

def ocDecodeObsM {M : Type} [Memory M] [MemoryOps M] (ptrTys : List PtrType) (m : Machine M) :
    MrOcFpObs :=
  match ocReadNatM m 0 with
  | some 0 => match ocReadNatM m 1 with | some a => .okScalar a | none => .unsupported
  | some 1 => match ocReadNatM m 1, ocReadNatM m 2 with
    | some a, some b => .okRetagPair a b
    | _, _ => .unsupported
  | some 2 => match ocReadLocalM m 4 with
    | some (.Ptr p) =>
      match ptrTys.map (fun t => ocCheckObs (checkPtrM p t (some m))) with
      | [] => .unsupported
      | o :: os => os.foldl ocCombine o
    | _ => .unsupported
  | _ => .unsupported

def ocRunM {M : Type} [Memory M] [MemoryOps M] (params : Memory.Params M) (ptrTys : List PtrType)
    (prog : Program) (fuel : Nat := 120) : MrOcFpObs :=
  match bootProgramM (M := M) params prog with
  | .error s => ocObsOfStop s
  | .ok m0 =>
    match runToStopM fuel m0 with
    | .error (.machineStop, mF) => ocDecodeObsM ptrTys mF
    | .error (s, _) => ocObsOfStop s
    | .ok _ => .unsupported

def ocRun (tb : Bool) (ptrTys : List PtrType) (prog : Program) : MrOcFpObs :=
  if tb then ocRunM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) ptrTys prog
  else ocRunM (M := BM) () ptrTys prog

/-- MiniRust program and validated safe pointer types of each case (`none` for `idx ≥ 22`). -/
def mrOcProg? : Nat → Option (Program × List PtrType)
  | 0 => some (ocMrProg0, [])
  | 1 => some (ocMrProg1, [])
  | 2 => some (ocMrProg2, [])
  | 3 => some (ocMrProg3, [])
  | 4 => some (ocMrProg4, [])
  | 5 => some (ocMrProg5, [])
  | 6 => some (ocMrProg6, [])
  | 7 => some (ocMrProg7, [])
  | 8 => some (ocMrProg8, [])
  | 9 => some (ocMrProg9, [])
  | 10 => some (ocMrProg10, [])
  | 11 => some (ocMrProg11, [])
  | 12 => some (ocMrProg12, [])
  | 13 => some (ocMrProg13, [])
  | 14 => some (ocMrProg14, [])
  | 15 => some (ocMrProg15, [])
  | 16 => some (ocMrProg16, ocMrSizedPtrTys)
  | 17 => some (ocMrProg17, ocMrZstPtrTys)
  | 18 => some (ocMrProg18, ocMrSizedPtrTys ++ ocMrZstPtrTys)
  | 19 => some (ocMrProg19, ocMrSizedPtrTys)
  | 20 => some (ocMrProg20, ocMrSizedPtrTys)
  | 21 => some (ocMrProg21, ocMrSizedPtrTys)
  | _ => none

/-- **Real MiniRust observer**: `tb = false` runs on `Mach` (`BasicMemory<x86_64>`), `tb = true`
on `MachTB` (`TreeBorrowsMemory<x86_64>`, `implicit_writes = true`); fail-closed `.unsupported`
for `idx ≥ 22`. -/
def mrOcObserve (tb : Bool) (idx : Nat) : MrOcFpObs :=
  match mrOcProg? idx with
  | none => .unsupported
  | some (p, tys) => ocRun tb tys p

/-- Frozen expected MiniRust table for `tb = false` (`Mach`). -/
def mrOcExpectedBasic : List MrOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .okScalar 5, .ub,
   .okRetagPair 5 5, .okRetagPair 5 5, .okRetagPair 4 9, .okRetagPair 5 5, .okRetagPair 5 5,
   .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- Frozen expected MiniRust table for `tb = true` (`MachTB`; only `11`, `13`, `14` differ). -/
def mrOcExpectedTb : List MrOcFpObs :=
  [.okScalar 7, .okScalar 7, .ub, .okScalar 42, .okScalar 9, .ub, .okScalar 1, .ub, .okScalar 5, .ub,
   .okRetagPair 5 5, .ub, .okRetagPair 4 9, .ub, .ub, .okRetagPair 3 9,
   .okPtrValid, .okPtrValid, .ub, .ub, .ub, .ub]

/-- **Kernel-checked 44-cell MiniRust table** (`22` cases × `Mach` / `MachTB`), every cell
executed by `bootProgramM` / `runToStopM` (`stepM`) and, for `D3`, `checkPtrM (some m)`. -/
theorem mrOcObserve_table :
    (List.range mrOcCaseCount).map (mrOcObserve false) = mrOcExpectedBasic ∧
    (List.range mrOcCaseCount).map (mrOcObserve true) = mrOcExpectedTb := by
  constructor <;> kernel_rfl

/-- Out-of-range cases are fail-closed `.unsupported` in both modes. -/
theorem mrOcObserve_out_of_range (tb : Bool) (idx : Nat) (h : mrOcCaseCount ≤ idx) :
    mrOcObserve tb idx = .unsupported := by
  unfold mrOcCaseCount at h
  have hNone : mrOcProg? idx = none := by
    unfold mrOcProg?
    split <;> first | rfl | omega
  unfold mrOcObserve
  rw [hNone]

/-- **Exact MiniRust Tree Borrows mode-sensitivity `↔`**: `Mach` and `MachTB` disagree on
`idx < 22` if and only if `idx ∈ {11, 13, 14}`. -/
theorem mrOcObserve_mode_sensitivity :
    ∀ idx, idx < mrOcCaseCount →
      (mrOcObserve false idx ≠ mrOcObserve true idx ↔ ocCaseModeSensitive idx = true) := by
  have hB := mrOcObserve_table.1
  have hT := mrOcObserve_table.2
  have hAll : ((List.range mrOcCaseCount).all fun idx =>
      decide ((mrOcExpectedBasic[idx]? ≠ mrOcExpectedTb[idx]?) ↔
        ocCaseModeSensitive idx = true)) = true := by decide
  intro idx hi
  have cellB : some (mrOcObserve false idx) = mrOcExpectedBasic[idx]? := by
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : some (mrOcObserve true idx) = mrOcExpectedTb[idx]? := by
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB, ← cellT] at hIff
  simpa [Option.some.injEq] using hIff

/-- **Cross-authority agreement (kernel-checked)**: MiniRust (`Mach` / `MachTB`) and Trusted
(`tb = false` / `true`) agree on every case except the documented `D1` boundary `8`. -/
theorem mrOc_trusted_agreement :
    ((List.range mrOcCaseCount).all fun idx =>
      idx == 8 || (mrOcObserve false idx == mrOcTrustedObserve false idx &&
        mrOcObserve true idx == mrOcTrustedObserve true idx)) = true := by
  decide +kernel

end MiniRustPrograms

/-! ## §3. Exact Diagnostics, `some mach` vs `none` Contrast, and Upstream-Lowering Contrasts -/

section Diagnostics

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.CrossFrameRefAndPanicMR MiniRustSpec.WideDstAndMaybeUninitMR

/-- **Exact UB diagnostics on `Mach` and `MachTB`**: the `D1` negative cells fault on the
uninitialized load, and on `MachTB` only the protected foreign accesses of `11`, `13`, `14` fault
(the `Mach` runs of the same programs are UB-free). -/
theorem mr_oc_exact_ub_diagnostics :
    runStopMsgBasic ocMrProg2 = some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgTB ocMrProg2 = some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgBasic ocMrProg5 = some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgBasic ocMrProg7 = some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgBasic ocMrProg9 = some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgTB ocMrProg9 = some "load at type but the data in memory violates the language invariant" ∧
    runStopMsgBasic ocMrProg11 = none ∧
    runStopMsgTB ocMrProg11 = some "Tree Borrows: foreign read of protected Unique reference" ∧
    runStopMsgBasic ocMrProg13 = none ∧
    runStopMsgTB ocMrProg13 = some "Tree Borrows: foreign read of protected Unique reference" ∧
    runStopMsgBasic ocMrProg14 = none ∧
    runStopMsgTB ocMrProg14 =
      some "Tree Borrows: foreign write of protected Frozen reference which had a local read" ∧
    runStopMsgTB ocMrProg10 = none ∧ runStopMsgTB ocMrProg12 = none ∧ runStopMsgTB ocMrProg15 = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- **Upstream-lowering contrasts (documented)**: upstream `minimize` lowers `Operand::Move` to a
plain `Load` and a glue-free `Drop` to a plain jump, so under those lowerings the uses after move
(`2`) and after drop (`7`) are NOT UB in MiniRust; the canonical cells instead lower the move and
the drop as Trusted models them (`Deinit`), matching Trusted's UB. -/
theorem mr_oc_minimize_lowering_contrasts :
    ocRun false [] ocMrProg2Minimize = .okScalar 7 ∧ ocRun true [] ocMrProg2Minimize = .okScalar 7 ∧
    ocRun false [] ocMrProg7Minimize = .okScalar 7 ∧ ocRun true [] ocMrProg7Minimize = .okScalar 7 ∧
    mrOcObserve false 2 = .ub ∧ mrOcObserve false 7 = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- The final `Mach` of a basic run (stopped at `Intrinsic.Exit`). -/
def ocFinalMachBasic (prog : Program) : Option Mach :=
  match bootProgramM (M := BM) () prog with
  | .ok m0 =>
    match runToStopM 120 m0 with
    | .error (.machineStop, mF) => some mF
    | _ => none
  | .error _ => none

/-- `(checkPtr p ty (some m), checkPtr p ty none)` for the pointer `p` in `_4` of the final
`Mach` `m` of a basic run. -/
def ocCheckPtrContrast (prog : Program) (ty : PtrType) : Option (Interp Unit × Interp Unit) :=
  (ocFinalMachBasic prog).bind fun m =>
    match ocReadLocalM m 4 with
    | some (.Ptr p) => some (checkPtr p ty (some m), checkPtr p ty none)
    | _ => none

/-- The final `MachTB` of a Tree Borrows run. -/
def ocFinalMachTB (prog : Program) : Option MachTB :=
  match bootProgramM (M := TBM) ({ implicit_writes := true } : TreeBorrowsParams) prog with
  | .ok m0 =>
    match runToStopM 120 m0 with
    | .error (.machineStop, mF) => some mF
    | _ => none
  | .error _ => none

/-- `(checkPtrM p ty (some m), checkPtrM p ty none)` on the final `MachTB`. -/
def ocCheckPtrMContrastTB (prog : Program) (ty : PtrType) : Option (Interp Unit × Interp Unit) :=
  (ocFinalMachTB prog).bind fun m =>
    match ocReadLocalM m 4 with
    | some (.Ptr p) => some (checkPtrM p ty (some m), checkPtrM p ty none)
    | _ => none

/-- **`D3` exact `some mach` vs `none` contrast on `Mach` (`checkPtr`) across BOTH `Ref` and
`Box` for all 6 `D3` cases (`16..21`)**: valid `&u32` / `Box<u32>` is `.ok ()` with the machine but
`.unsupported` without; ZST `&()` / `Box<()>` is `.ok ()` both ways; null (sized and ZST) and
unaligned (`Ref` and `Box`) are exact UB both ways (never `.unsupported`); out-of-bounds and
deallocated (`Ref` and `Box`) are exact `CM.dereferenceable` UB with the machine but `.unsupported`
without. -/
theorem mr_checkPtr_some_vs_none_contrast :
    ocCheckPtrContrast ocMrProg16 (.Ref .Immutable u32Pointee) =
      some (.ok (), unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg16 (.Box u32Pointee) =
      some (.ok (), unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg17 (.Ref .Immutable ocMrUnitPointee) = some (.ok (), .ok ()) ∧
    ocCheckPtrContrast ocMrProg17 (.Box ocMrUnitPointee) = some (.ok (), .ok ()) ∧
    ocCheckPtrContrast ocMrProg18 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrContrast ocMrProg18 (.Box u32Pointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrContrast ocMrProg18 (.Ref .Immutable ocMrUnitPointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrContrast ocMrProg18 (.Box ocMrUnitPointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrContrast ocMrProg19 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: unaligned safe pointer", ub "Value::Ptr: unaligned safe pointer") ∧
    ocCheckPtrContrast ocMrProg19 (.Box u32Pointee) =
      some (ub "Value::Ptr: unaligned safe pointer", ub "Value::Ptr: unaligned safe pointer") ∧
    ocCheckPtrContrast ocMrProg20 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg20 (.Box u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg21 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrContrast ocMrProg21 (.Box u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- **`D3` exact `some mach` vs `none` contrast on `MachTB` (`checkPtrM`) across BOTH `Ref` and
`Box` for all 6 `D3` cases (`16..21`)**. -/
theorem mr_checkPtrM_tb_some_vs_none_contrast :
    ocCheckPtrMContrastTB ocMrProg16 (.Ref .Immutable u32Pointee) =
      some (.ok (), unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg16 (.Box u32Pointee) =
      some (.ok (), unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg17 (.Ref .Immutable ocMrUnitPointee) = some (.ok (), .ok ()) ∧
    ocCheckPtrMContrastTB ocMrProg17 (.Box ocMrUnitPointee) = some (.ok (), .ok ()) ∧
    ocCheckPtrMContrastTB ocMrProg18 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg18 (.Box u32Pointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg18 (.Ref .Immutable ocMrUnitPointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg18 (.Box ocMrUnitPointee) =
      some (ub "Value::Ptr: null safe pointer", ub "Value::Ptr: null safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg19 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: unaligned safe pointer", ub "Value::Ptr: unaligned safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg19 (.Box u32Pointee) =
      some (ub "Value::Ptr: unaligned safe pointer", ub "Value::Ptr: unaligned safe pointer") ∧
    ocCheckPtrMContrastTB ocMrProg20 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg20 (.Box u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg21 (.Ref .Immutable u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    ocCheckPtrMContrastTB ocMrProg21 (.Box u32Pointee) =
      some (ub "Value::Ptr: non-dereferenceable safe pointer",
        unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

end Diagnostics

/-! ## §4. Universal Laws (`D1`–`D3`) -/

section UniversalLaws

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp

/-! ### `D1` -/

/-- `D1` **MiniRustSpec fail-closed boundary (universal)**: no place starting with
`ProjectionElem.opaqueCast` translates to MiniRust (upstream `minimize` has no `OpaqueCast`
lowering), so no assignment through one translates either, and it is not a `simpleProj`. -/
theorem mr_translate_opaqueCast_fail_closed (decls : List Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable) (i : Nat)
    (t : Trusted.Rustc.V2026_06_01.MirAst.Ty) (rest : List Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem)
    (rv : Trusted.Rustc.V2026_06_01.MirAst.Rvalue) (span : String) :
    MiniRustSpec.Correspondence.translatePlace decls ⟨i, .opaqueCast t :: rest⟩ = none ∧
    MiniRustSpec.Correspondence.translateStatement decls
      ⟨.assign ⟨i, .opaqueCast t :: rest⟩ rv, span⟩ layouts = none ∧
    MiniRustSpec.Correspondence.simpleProj (.opaqueCast t :: rest) = false := by
  refine ⟨rfl, ?_, rfl⟩
  simp [MiniRustSpec.Correspondence.translateStatement, MiniRustSpec.Correspondence.translatePlace]

section TrustedD1
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst Trusted.Rustc.V2026_06_01.MirSemantics

/-- `D1` **Trusted leading-cast stripping (universal)**: `stripLeadingOpaqueCast` drops exactly
the leading cast chain, and the full cast erasure `ocEraseProj` of a pure cast chain is empty. -/
theorem trusted_stripLeadingOpaqueCast_laws (t : Ty) (p : List ProjectionElem) :
    stripLeadingOpaqueCast (.opaqueCast t :: p) = stripLeadingOpaqueCast p ∧
    ocEraseProj (.opaqueCast t :: p) = ocEraseProj p ∧
    (stripLeadingOpaqueCast p = [] → ocEraseProj p = []) := by
  refine ⟨rfl, rfl, ?_⟩
  induction p with
  | nil => intro _; rfl
  | cons e rest ih =>
    cases e <;> simp_all [stripLeadingOpaqueCast, ocEraseProj]

set_option linter.unusedSimpArgs false in
/-- `D1` **Trusted value-transparency of the full erasure (universal)**: for every projection
path, reading through it equals reading through its full cast erasure `ocEraseProj`. -/
theorem trusted_readProjectedValue_ocErase (locals : List LocalSlot) :
    ∀ (p : List ProjectionElem) (v : Value),
      readProjectedValue locals v p = readProjectedValue locals v (ocEraseProj p)
  | [], _ => rfl
  | e :: rest, v => by
    have ih := trusted_readProjectedValue_ocErase locals rest
    cases e with
    | field f ty => cases f <;> cases v <;> simp only [readProjectedValue, ocEraseProj, ih]
    | index l =>
      cases v with
      | aggregate vi fs => cases vi <;> simp only [readProjectedValue, ocEraseProj, ih]
      | _ => simp only [readProjectedValue, ocEraseProj, ih]
    | constantIndex o m fe =>
      cases v with
      | aggregate vi fs =>
        cases vi
        · unfold readProjectedValue
          simp only [ocEraseProj, ih]
        · simp only [readProjectedValue, ocEraseProj]
      | _ => simp only [readProjectedValue, ocEraseProj]
    | subslice a b fe =>
      cases v with
      | aggregate vi fs => cases vi <;> simp only [readProjectedValue, ocEraseProj, ih]
      | _ => simp only [readProjectedValue, ocEraseProj, ih]
    | opaqueCast t => cases v <;> simp only [readProjectedValue, ocEraseProj, ih]
    | _ => cases v <;> simp only [readProjectedValue, ocEraseProj, ih]

/-- `D1` **Trusted one-step transparency (universal)**: `.opaqueCast` is value-transparent for
reads and writes of every value. -/
theorem trusted_projectedValue_opaqueCast (locals : List LocalSlot) (v nv : Value) (t : Ty)
    (rest : List ProjectionElem) :
    readProjectedValue locals v (.opaqueCast t :: rest) = readProjectedValue locals v rest ∧
    writeProjectedValue locals v (.opaqueCast t :: rest) nv = writeProjectedValue locals v rest nv := by
  refine ⟨?_, ?_⟩ <;> cases v <;> rfl

/-- `D1` **Trusted fail-closed deref-below-cast boundary (universal)**: reading
`*(_l as T)…` from any initialized local fails closed with `.unsupported` (never a silent value,
never a UB verdict), exactly the Trusted cell of case `8`. -/
theorem trusted_evalOperand_cast_deref_unsupported (locals : List LocalSlot) (l : Nat) (t : Ty)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) (decls : List LocalDecl) (v : Value) (r : List ProjectionElem)
    (hv : Trusted.Sequence.get? locals l = some (.init v))
    (hu : placeTouchesUnion decls layouts ⟨l, .opaqueCast t :: .deref :: r⟩ = false) :
    evalOperand locals (.copy ⟨l, .opaqueCast t :: .deref :: r⟩) borrows globals layouts
      callerLocals decls = .unsupported := by
  have hread : readProjectedValue locals v (.opaqueCast t :: .deref :: r) = .unsupported := by
    rw [(trusted_projectedValue_opaqueCast locals v v t (.deref :: r)).1]
    cases v <;> rfl
  simp only [evalOperand, hu, hv, hread]

/-- `D1` **Trusted leading-cast decl erasure (universal)**: `eraseLeadingOpaqueCastDecls` leaves
`localDecls` unchanged when there is no leading `.opaqueCast`, and when a leading cast chain
resolves to `effCastTy` it re-declares `loc` at `effCastTy` (regardless of `loc`'s original
declared type, e.g. an opaque ADT). -/
theorem trusted_eraseLeadingOpaqueCastDecls_laws (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (loc : Local) (t : Ty) (rest : List ProjectionElem) (f : Nat) (fty : Ty) (effCastTy : Ty)
    (hRes : placeTyResolved decls layouts
      { local_ := loc, projection := takeLeadingOpaqueCast (.opaqueCast t :: rest) } = some effCastTy) :
    eraseLeadingOpaqueCastDecls decls layouts loc [] = decls ∧
    eraseLeadingOpaqueCastDecls decls layouts loc (.field f fty :: rest) = decls ∧
    eraseLeadingOpaqueCastDecls decls layouts loc (.opaqueCast t :: rest) =
      setLocalDeclTy decls loc effCastTy := by
  refine ⟨rfl, rfl, ?_⟩
  simp [eraseLeadingOpaqueCastDecls, hRes]

/-- `D1` **non-vacuity witness for `eraseLeadingOpaqueCastDecls` / `uninitFieldWriteShell?`**:
even when local `_1` is declared at an **opaque** ADT type `oc::OpaquePair` (NOT `(u32, u32)`),
casting `(_1 as (u32, u32)).1` re-declares `_1` at `ocPairTy` and constructs the 2-field tuple
shell `[.uninit, .uninit]` so field-write into an uninitialized opaque local succeeds. -/
theorem trusted_uninitFieldWriteShell_opaque_witness :
    let opaqueTy : Ty := { kind := .adt "oc::OpaquePair" [], layoutIdx := 0 }
    let decls : List LocalDecl := [ocDecl ocU32Ty, ocDecl opaqueTy]
    eraseLeadingOpaqueCastDecls decls ocLayouts 1 [.opaqueCast ocPairTy, .field 1 ocU32Ty] =
      [ocDecl ocU32Ty, ocDecl ocPairTy] ∧
    uninitFieldWriteShell? decls ocLayouts 1 (.opaqueCast ocPairTy) [.field 1 ocU32Ty] =
      some (.aggregate 0 [.uninit, .uninit]) := by
  refine ⟨?_, ?_⟩ <;> kernel_rfl

/-- `D1` **Trusted move through pure cast chain de-initializes local (universal)**: moving
`move (_l as T₁ … as Tₙ)` (`stripLeadingOpaqueCast rest = []`) from an initialized local validates
the value at the effective cast type and overwrites `_l` with `.uninit`. -/
theorem trusted_evalOperand_move_pure_cast_deinit (locals locals' : List LocalSlot) (l : Nat)
    (t : Ty) (rest : List ProjectionElem) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : Layout.LayoutTable)
    (callerLocals : List LocalSlot) (decls : List LocalDecl) (callStack : List SavedCallerFrame)
    (v validVal : Value)
    (hPure : stripLeadingOpaqueCast rest = [])
    (hv : Trusted.Sequence.get? locals l = some (.init v))
    (hr : readProjectedValue locals v [] = .ok validVal)
    (hVal : (match decls with
      | [] => true
      | _ :: _ => validateValueForTy? layouts (placeTyResolved decls layouts ⟨l, .opaqueCast t :: rest⟩) validVal) = true)
    (hSet : Trusted.Sequence.set? locals l .uninit = some locals') :
    evalOperand locals (.move ⟨l, .opaqueCast t :: rest⟩) borrows globals layouts
      callerLocals decls callStack = .ok validVal locals' := by
  unfold evalOperand
  simp only [hPure, hv, hr]
  cases decls with
  | nil => simp only [hSet]
  | cons d ds =>
    dsimp only at hVal ⊢
    rw [hVal]
    simp only [hSet]

/-- `D1` **Trusted `writePlaceValue` through `.opaqueCast` (universal)**:
(a) writing to a pure cast chain updates the root local (after cast-type validation), and
(b) writing to `*(_l as T)…` (a dereference directly below a leading cast chain) fails closed
with `.unsupported`. -/
theorem trusted_writePlaceValue_opaqueCast_laws (locals locals' : List LocalSlot)
    (borrows : List BorrowEntry) (l : Nat) (t : Ty) (restPure restDeref r : List ProjectionElem)
    (val : Value) (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (callStack : List SavedCallerFrame) (slot : LocalSlot)
    (hPure : stripLeadingOpaqueCast restPure = [])
    (hDeref : stripLeadingOpaqueCast restDeref = .deref :: r)
    (hLive : Trusted.Sequence.get? locals l = some slot) (hNotDead : slot ≠ .dead)
    (hVal : (match decls with
      | [] => true
      | _ :: _ => validateValueForTy? layouts (placeTyResolved decls layouts ⟨l, .opaqueCast t :: restPure⟩) val) = true)
    (hSet : Trusted.Sequence.set? locals l (.init val) = some locals') :
    writePlaceValue locals borrows ⟨l, .opaqueCast t :: restPure⟩ val decls layouts callStack =
      .ok locals' ∧
    writePlaceValue locals borrows ⟨l, .opaqueCast t :: restDeref⟩ val decls layouts callStack =
      .unsupported := by
  constructor
  · unfold writePlaceValue
    simp only [hPure]
    cases decls with
    | nil =>
      cases slot with
      | dead => exact False.elim (hNotDead rfl)
      | uninit => simp only [hLive, hSet]
      | init _ => simp only [hLive, hSet]
    | cons d ds =>
      dsimp only at hVal ⊢
      rw [hVal]
      cases slot with
      | dead => exact False.elim (hNotDead rfl)
      | uninit => simp only [hLive, hSet]
      | init _ => simp only [hLive, hSet]
  · simp only [writePlaceValue, hDeref]

/-- `D1` **Trusted `evalStmt` on `Deinit` through a pure cast chain (universal)**:
(a) without active protectors, `Deinit (_l as T₁ … as Tₙ)` de-initializes `_l` and invalidates
conflicting borrows; (b) under an active protector conflict, it faults with `.ub`. -/
theorem trusted_evalStmt_deinit_opaqueCast (s : MachineState) (l : Nat) (t : Ty)
    (rest : List ProjectionElem) (span : String) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (slot : LocalSlot) (locals' : List LocalSlot)
    (hPure : stripLeadingOpaqueCast rest = [])
    (hLive : Trusted.Sequence.get? s.frame.locals l = some slot) (hNotDead : slot ≠ .dead)
    (hSet : Trusted.Sequence.set? s.frame.locals l .uninit = some locals') :
    (s.memory.activeProtectors = [] →
      evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: rest⟩, span⟩ decls layouts =
        MirStepNode.step (advanceStmt s locals'
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows l .none
              (Trusted.Sequence.length s.memory.callStack) })) ∧
    (∀ p ps, s.memory.activeProtectors = p :: ps →
      hasProtectedWriteConflict s.memory.borrows (p :: ps) l .none .nil 0 0
        (Trusted.Sequence.length s.memory.callStack) = true →
      evalStmt s ⟨.deinit ⟨l, .opaqueCast t :: rest⟩, span⟩ decls layouts =
        MirStepNode.fail .ub) := by
  constructor
  · intro hProt
    cases slot with
    | dead => exact False.elim (hNotDead rfl)
    | uninit => simp only [evalStmt, stripLeadingOpaqueCast, hPure, hLive, hSet, hProt]
    | init _ => simp only [evalStmt, stripLeadingOpaqueCast, hPure, hLive, hSet, hProt]
  · intro p ps hProt hConf
    cases slot with
    | dead => exact False.elim (hNotDead rfl)
    | uninit => simp only [evalStmt, stripLeadingOpaqueCast, hPure, hLive, hSet, hProt, hConf]
    | init _ => simp only [evalStmt, stripLeadingOpaqueCast, hPure, hLive, hSet, hProt, hConf]

/-- `D1` **Trusted `evalStmt` on `SetDiscriminant` through a pure cast chain (universal)**:
routes through `eraseLeadingOpaqueCastDecls` so variant padding uses the effective cast type. -/
theorem trusted_evalStmt_setDiscriminant_opaqueCast (s : MachineState) (l : Nat) (t : Ty)
    (rest : List ProjectionElem) (oldV v : Nat) (fields fields' : List Value) (span : String)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (hPure : stripLeadingOpaqueCast rest = [])
    (hInit : Trusted.Sequence.get? s.frame.locals l = some (.init (.aggregate oldV fields)))
    (hPad : padSetDiscriminantInitFields?
      (eraseLeadingOpaqueCastDecls decls layouts l (.opaqueCast t :: rest)) layouts
      { local_ := l, projection := .nil } v fields = some fields') :
    evalStmt s ⟨.setDiscriminant ⟨l, .opaqueCast t :: rest⟩ v, span⟩ decls layouts =
      evalSetDiscriminantLocal s l v fields' := by
  simp only [evalStmt, stripLeadingOpaqueCast, hPure, hInit, hPad]

/-- `D1` **Trusted `evalTerminator` on `Drop` through a pure cast chain (universal)**:
(a) without active protectors, `Drop (_l as T₁ … as Tₙ) -> target` de-initializes `_l` and jumps
to `target`; (b) under an active protector conflict, it faults with `.ub` (mode-sensitive UB!). -/
theorem trusted_evalTerminator_drop_opaqueCast (s : MachineState) (l : Nat) (t : Ty)
    (rest : List ProjectionElem) (target : BasicBlockIdx) (u : UnwindAction) (span : String)
    (curBody : Option CapturedMir) (slot : LocalSlot) (locals' : List LocalSlot)
    (hPure : stripLeadingOpaqueCast rest = [])
    (hLive : Trusted.Sequence.get? s.frame.locals l = some slot) (hNotDead : slot ≠ .dead)
    (hSet : Trusted.Sequence.set? s.frame.locals l .uninit = some locals') :
    (s.memory.activeProtectors = [] →
      evalTerminator s ⟨.drop ⟨l, .opaqueCast t :: rest⟩ target u, span⟩ curBody =
        MirStepNode.step { s with
          frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          memory := { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows l .none
              (Trusted.Sequence.length s.memory.callStack) } }) ∧
    (∀ p ps, s.memory.activeProtectors = p :: ps →
      hasProtectedWriteConflict s.memory.borrows (p :: ps) l .none .nil 0 0
        (Trusted.Sequence.length s.memory.callStack) = true →
      evalTerminator s ⟨.drop ⟨l, .opaqueCast t :: rest⟩ target u, span⟩ curBody =
        MirStepNode.fail .ub) := by
  constructor
  · intro hProt
    unfold MirSemantics.evalTerminator
    dsimp only
    rw [hLive]
    cases slot with
    | dead => exact False.elim (hNotDead rfl)
    | uninit => simp only [stripLeadingOpaqueCast, hPure, hSet, hProt]
    | init _ => simp only [stripLeadingOpaqueCast, hPure, hSet, hProt]
  · intro p ps hProt hConf
    unfold MirSemantics.evalTerminator
    dsimp only
    rw [hLive]
    cases slot with
    | dead => exact False.elim (hNotDead rfl)
    | uninit => simp only [stripLeadingOpaqueCast, hPure, hSet, hProt, hConf]
    | init _ => simp only [stripLeadingOpaqueCast, hPure, hSet, hProt, hConf]

/-- `D2` **Trusted `FnEntry` protector attachment on fallback unknown type (universal)**: when the
retagged place has no resolvable static type, `evalFnEntryRetag` attaches a fresh strong protector
`s.memory.nextProtector` to the argument's tag and registers it as active. -/
theorem trusted_evalFnEntryRetag_attach (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (place : Place) (ptrVal : ProvenancePtr) (sz : Nat)
    (parent : BorrowEntry) (locals' : List LocalSlot) (h : placeTy decls layouts place = none) :
    evalFnEntryRetag s decls layouts place ptrVal sz parent locals' =
      MirStepNode.step (advanceStmt s locals'
        { s.memory with
          borrows := attachBorrowProtector s.memory.borrows ptrVal.tag s.memory.nextProtector
          activeProtectors := s.memory.nextProtector :: s.memory.activeProtectors
          nextProtector := Nat.add s.memory.nextProtector 1 }) := by
  unfold evalFnEntryRetag
  rw [h]

/-- `D2` **Trusted `FnEntry` retag on the real reference branch (universal)**:
(a) a reference to an uninhabited pointee faults with `.ub`;
(b) for an inhabited reference parameter `place = ⟨l, []⟩` whose initial read is UB-free,
`evalFnEntryRetag` allocates fresh child tag `s.memory.nextTag` with permission
`fnEntryRetagPerm mutability pointee`, strong protector `some s.memory.nextProtector`, and parent
`some ptrVal.tag`, pushes `s.memory.nextProtector` onto `activeProtectors`, increments `nextTag`
and `nextProtector`, and stores the retagged pointer back in `l`. -/
theorem trusted_evalFnEntryRetag_ref_creates_protected_child (s : MachineState)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (l : Nat) (ptrVal : ProvenancePtr)
    (sz : Nat) (parent : BorrowEntry) (locals' : List LocalSlot)
    (mutability : MirAst.Mutability) (pointee : RigidTy) (li : Nat)
    (hTy : placeTy decls layouts ⟨l, []⟩ = some { kind := .ref mutability pointee, layoutIdx := li }) :
    (rigidTyIsUninhabited 16 pointee = true →
      evalFnEntryRetag s decls layouts ⟨l, []⟩ ptrVal sz parent locals' = MirStepNode.fail .ub) ∧
    (∀ (locals'' : List LocalSlot),
      rigidTyIsUninhabited 16 pointee = false →
      hasTreeReadUB s.memory.borrows s.memory.borrows s.memory.activeProtectors
        parent.targetLocal (.some ptrVal.tag) parent.targetProjection
        parent.rangeOffset parent.rangeLen parent.targetFrameDepth = false →
      Trusted.Sequence.set? locals' l
        (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := ptrVal.offsetBytes } sz)) =
        some locals'' →
      ∃ borrowsAfterRead,
        evalFnEntryRetag s decls layouts ⟨l, []⟩ ptrVal sz parent locals' =
          MirStepNode.step (advanceStmt s locals''
            { s.memory with
              borrows := {
                tag := s.memory.nextTag
                targetLocal := parent.targetLocal
                targetFrameDepth := parent.targetFrameDepth
                allocDead := parent.allocDead
                targetProjection := parent.targetProjection
                perm := fnEntryRetagPerm mutability pointee
                rangeOffset := parent.rangeOffset
                rangeLen := parent.rangeLen
                protector := .some s.memory.nextProtector
                parentTag := .some ptrVal.tag
              } :: borrowsAfterRead
              nextTag := Nat.add s.memory.nextTag 1
              activeProtectors := s.memory.nextProtector :: s.memory.activeProtectors
              nextProtector := Nat.add s.memory.nextProtector 1 })) := by
  constructor
  · intro hUninh
    unfold evalFnEntryRetag
    simp only [hTy, hUninh]
  · intro locals'' hInh hReadUB hSet
    unfold evalFnEntryRetag
    simp only [hTy, hInh]
    cases hPerm : fnEntryRetagPerm mutability pointee with
    | cell =>
      exact ⟨s.memory.borrows, by simp only [hSet]⟩
    | _ =>
      cases hZst : rigidTyIsZeroSized 16 pointee with
      | true =>
        exact ⟨s.memory.borrows, by simp only [hSet]⟩
      | false =>
        exact ⟨freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
          parent.targetLocal (.some ptrVal.tag) parent.targetProjection
          parent.rangeOffset parent.rangeLen s.memory.activeProtectors parent.targetFrameDepth,
          by simp only [hReadUB, hSet]⟩

/-- `D2` **Trusted protector restoration on return (universal)**: returning from a callee drops all
callee-allocated `FnEntry` protectors and restores solely the caller's saved protector list. -/
theorem trusted_restoreCallerProtectors_law (caller : SavedCallerFrame) :
    (∀ p, caller.callerProtector = some p →
      restoreCallerProtectors caller = p :: caller.calleeProtectors) ∧
    (caller.callerProtector = none →
      restoreCallerProtectors caller = caller.calleeProtectors) := by
  constructor
  · intro p hp; simp [restoreCallerProtectors, hp]
  · intro hn; simp [restoreCallerProtectors, hn]

/-- `D2` **Trusted `FnEntry` child permissions (universal)**: `&mut T` arguments get
`reservedFrz false`, `&T` arguments of `Freeze` pointees get `frozen`. -/
theorem trusted_fnEntryRetagPerm (p : RigidTy) (h : rigidTyIsFreeze 16 p = true) :
    fnEntryRetagPerm .mut p = .reservedFrz false ∧ fnEntryRetagPerm .not p = .frozen := by
  refine ⟨rfl, ?_⟩
  simp [fnEntryRetagPerm, h]

/-- `D2` **no-borrow-tracker image (universal)**: `ocEraseRetags` leaves no `Retag` statement. -/
theorem trusted_ocEraseRetags_retag_free (b : CapturedMir) :
    ∀ bb ∈ (ocEraseRetags b).basicBlocks, ∀ s ∈ bb.statements, ∀ k p, s.kind ≠ .retag k p := by
  intro bb hbb s hs k p
  simp only [ocEraseRetags, List.mem_map] at hbb
  obtain ⟨bb0, _, rfl⟩ := hbb
  simp only [List.mem_map] at hs
  obtain ⟨s0, _, rfl⟩ := hs
  split <;> simp_all

/-- `D1`/`D2` **non-vacuity witnesses for Trusted conditional universal laws**: instantiates the
hypotheses of `trusted_evalOperand_cast_deref_unsupported`, `trusted_evalOperand_move_pure_cast_deinit`,
`trusted_fnEntryRetagPerm`, and `trusted_evalFnEntryRetag_ref_creates_protected_child`. -/
theorem trusted_d1_d2_nonvacuity_witnesses :
    (evalOperand [.uninit, .init (.scalar ⟨5, 4⟩), .init (.ptr ⟨1, 0⟩ 8)]
      (.copy ⟨2, [.opaqueCast ocRawConstU32Ty, .deref]⟩) [] [] ocLayouts []
      ocCase8Mir.localDecls = .unsupported) ∧
    (evalOperand [.uninit, .init (.scalar ⟨7, 4⟩)]
      (.move ⟨1, [ocCastU32, ocCastU32]⟩) [] [] ocLayouts [] ocCase1Mir.localDecls [] =
      .ok (.scalar ⟨7, 4⟩) [.uninit, .uninit]) ∧
    (rigidTyIsFreeze 16 (.uint .u8) = true ∧
      fnEntryRetagPerm .mut (.uint .u8) = .reservedFrz false ∧
      fnEntryRetagPerm .not (.uint .u8) = .frozen) ∧
    (placeTy ocCase12Callee.localDecls ocLayouts ⟨1, []⟩ = some ocMutRefU8Ty ∧
      rigidTyIsUninhabited 16 (.uint .u8) = false) := by
  refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩ <;> kernel_rfl

end TrustedD1

/-! ### `D2` (MiniRust) -/

/-- `D2` **callee-only vs caller-signature retag is unobservable on `BasicMemory` (universal)**:
`MemoryOps.retag_ptr` on `BM` is the identity whatever `fnEntry` is. -/
theorem mr_basic_retag_fnEntry_irrelevant (m : BM) (fe : Memory.FrameExtra BM)
    (ptr : Pointer (Memory.Provenance BM)) (ptrTy : PtrType) (w : Bool)
    (vl : ThinPointer (Memory.Provenance BM) → Interp VTable) :
    MemoryOps.retag_ptr m fe ptr ptrTy true w vl = MemoryOps.retag_ptr m fe ptr ptrTy false w vl ∧
    MemoryOps.retag_ptr m fe ptr ptrTy true w vl = .ok (ptr, m, fe) := ⟨rfl, rfl⟩

/-- `D2` **callee-only semantics on Tree Borrows (universal)**: a parameter of raw-pointer type
(the post-`#166253` callee view `*mut u8`) is NEVER reborrowed or protected by
`TreeBorrowsMemory.retag_ptr`, whatever `fnEntry` is. -/
theorem mr_tb_retag_raw_noop (tbm : TBM) (fe : TreeBorrowsFrameExtra) (ptr : Pointer TreeBorrowsProvenance)
    (k : PointerMetaKind) (fnEntry w : Bool) (vl : ThinPointer TreeBorrowsProvenance → Interp VTable) :
    TreeBorrowsMemory.retag_ptr tbm fe ptr (.Raw k) fnEntry w vl = .ok (ptr, tbm, fe) := rfl

private theorem oc_bind_ok {α β : Type} {x : Interp α} {f : α → Interp β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

private theorem oc_ite_ok {α : Type} (c : Bool) (d : Interp (Option α)) (y : α)
    (h : (if c = true then pure none else d) = .ok (some y)) : d = .ok (some y) := by
  cases c
  · simpa using h
  · simp [pure, Except.pure] at h

/-- `D2` **`FnEntry` attaches a strong protector to reference parameters (universal)**: for every
reference type `&T` / `&mut T`, a successful `ReborrowSettings.new` yields a `Strong` protector
when `fnEntry = true` and no protector when `fnEntry = false`. -/
theorem mr_reborrowSettings_ref_protector {P : Type} (vl : ThinPointer P → Interp VTable)
    (ptr : Pointer P) (mu : Mutability) (pointee : PointeeInfo) (fnEntry : Bool) (params : TreeBorrowsParams) (w : Bool)
    (s : ReborrowSettings) (h : ReborrowSettings.new vl ptr (.Ref mu pointee) fnEntry params w = .ok (some s)) :
    s.protected = (if fnEntry then .Strong else .No) := by
  unfold ReborrowSettings.new at h
  simp only [PtrType.safe_pointee] at h
  have h1 := oc_ite_ok _ _ _ h
  obtain ⟨_, _, h2⟩ := oc_bind_ok h1
  obtain ⟨_, _, h3⟩ := oc_bind_ok h2
  obtain ⟨_, _, h4⟩ := oc_bind_ok h3
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h4
  subst h4
  cases fnEntry <;> rfl

/-- `D2` **`FnEntry` attaches a weak protector to `Box<T>` parameters (universal)**: contrasting
with references' `Strong` protector, a successful `ReborrowSettings.new` on `.Box pointee` yields
`.Weak` when `fnEntry = true` and `.No` when `fnEntry = false`. -/
theorem mr_reborrowSettings_box_weak_protector {P : Type} (vl : ThinPointer P → Interp VTable)
    (ptr : Pointer P) (pointee : PointeeInfo) (fnEntry : Bool) (params : TreeBorrowsParams) (w : Bool)
    (s : ReborrowSettings) (h : ReborrowSettings.new vl ptr (.Box pointee) fnEntry params w = .ok (some s)) :
    s.protected = (if fnEntry then .Weak else .No) := by
  unfold ReborrowSettings.new at h
  simp only [PtrType.safe_pointee] at h
  have h1 := oc_ite_ok _ _ _ h
  obtain ⟨_, _, h2⟩ := oc_bind_ok h1
  obtain ⟨_, _, h3⟩ := oc_bind_ok h2
  obtain ⟨_, _, h4⟩ := oc_bind_ok h3
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h4
  subst h4
  cases fnEntry <;> rfl

/-- `D2` **non-vacuity witnesses for `ReborrowSettings.new` (`Ref` and `Box`)**: confirms the
hypotheses of `mr_reborrowSettings_ref_protector` and `mr_reborrowSettings_box_weak_protector`
are concretely inhabited for `&mut u8`, `&u8`, and `Box<u8>` in both `fnEntry` modes. -/
theorem mr_reborrowSettings_nonvacuity :
    let vl : ThinPointer TreeBorrowsProvenance → Interp VTable := fun _ => unsupported "unused"
    let p : Pointer TreeBorrowsProvenance := ⟨⟨4, none⟩, none⟩
    let params : TreeBorrowsParams := { implicit_writes := true }
    (∃ s, ReborrowSettings.new vl p (.Ref .Mutable ocMrU8Pointee) true params true = .ok (some s) ∧
      s.protected = .Strong) ∧
    (∃ s, ReborrowSettings.new vl p (.Ref .Immutable ocMrU8Pointee) true params true = .ok (some s) ∧
      s.protected = .Strong) ∧
    (∃ s, ReborrowSettings.new vl p (.Box ocMrU8Pointee) true params true = .ok (some s) ∧
      s.protected = .Weak) ∧
    (∃ s, ReborrowSettings.new vl p (.Ref .Mutable ocMrU8Pointee) false params true = .ok (some s) ∧
      s.protected = .No) := by
  refine ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-! ### `D3` -/

private theorem listIndex_ne_unsupported {T : Type} (xs : List T) (i : Int) (w msg : String) :
    listIndex xs i w ≠ .error (.unsupported msg) := by
  unfold listIndex
  split
  · split <;> simp [pure, Except.pure, specPanic]
  · simp [specPanic]

/-- `D3` `BasicMemory.check_ptr` never reports `.unsupported` (universal, every provenance /
allocation extra): its only failures are `ub` (no provenance, dead, out of bounds) and the
`specPanic` of an allocation index outside the machine. -/
theorem mr_basicMemory_check_ptr_ne_unsupported {PE AE : Type} (mem : BasicMemory x86_64 PE AE)
    (ptr : ThinPointer (Provenance PE)) (len : Size) (msg : String) :
    BasicMemory.check_ptr mem ptr len ≠ .error (.unsupported msg) := by
  unfold BasicMemory.check_ptr
  split
  · simp [pure, Except.pure]
  · split
    · simp [ub]
    · rename_i id pe _
      simp only [bind, Except.bind]
      split
      · rename_i e he
        intro h
        cases h
        exact listIndex_ne_unsupported _ _ _ msg he
      · split
        · simp [ub]
        · split
          · simp [ub]
          · simp [pure, Except.pure]

/-- `D3` `BM.check_ptr` never reports `.unsupported` (universal). -/
theorem mr_bm_check_ptr_ne_unsupported (mem : BM) (ptr : Ptr) (len : Size) (msg : String) :
    BM.check_ptr mem ptr len ≠ .error (.unsupported msg) := by
  unfold BM.check_ptr
  split
  · simp [pure, Except.pure]
  · split
    · simp [ub]
    · simp only [bind, Except.bind]
      split
      · rename_i e he
        intro h
        cases h
        exact listIndex_ne_unsupported _ _ _ msg he
      · split
        · simp [ub]
        · split
          · simp [ub]
          · simp [pure, Except.pure]

/-- `D3` `MemoryOps.dereferenceable` on `BM` never reports `.unsupported` (universal). -/
theorem mr_bm_dereferenceable_ne_unsupported (mem : BM) (ptr : ThinPointer (Memory.Provenance BM))
    (len : Size) (msg : String) :
    MemoryOps.dereferenceable mem ptr len ≠ .error (.unsupported msg) := by
  show BM.dereferenceable mem ptr len ≠ _
  unfold BM.dereferenceable
  simp only [bind, Except.bind]
  split
  · rename_i e he
    intro h
    cases h
    exact mr_bm_check_ptr_ne_unsupported mem ptr len msg he
  · simp [pure, Except.pure]

/-- `D3` `CM.dereferenceable` never reports `.unsupported` (universal). -/
theorem mr_cm_dereferenceable_ne_unsupported (cm : ConcurrentMemory BM) (ptr : Ptr)
    (len : Size) (msg : String) :
    CM.dereferenceable cm ptr len ≠ .error (.unsupported msg) :=
  mr_bm_dereferenceable_ne_unsupported cm.memory ptr len msg

/-- `D3` `MemoryOps.dereferenceable` on `TBM` never reports `.unsupported` (universal). -/
theorem mr_tbm_dereferenceable_ne_unsupported (mem : TBM) (ptr : ThinPointer (Memory.Provenance TBM))
    (len : Size) (msg : String) :
    MemoryOps.dereferenceable mem ptr len ≠ .error (.unsupported msg) := by
  show TreeBorrowsMemory.dereferenceable mem ptr len ≠ _
  unfold TreeBorrowsMemory.dereferenceable
  simp only [bind, Except.bind]
  split
  · rename_i e he
    intro h
    cases h
    exact mr_basicMemory_check_ptr_ne_unsupported _ ptr len msg he
  · simp [pure, Except.pure]

private theorem ensureElseUb_bind_ne_unsupported {β : Type} (b : Bool) (m : String) (k : Unit → Interp β)
    (msg : String) (hk : k () ≠ .error (.unsupported msg)) :
    (ensureElseUb b m >>= k) ≠ .error (.unsupported msg) := by
  cases b
  · simp [ensureElseUb, ub, bind, Except.bind]
  · simpa [ensureElseUb, pure, Except.pure, bind, Except.bind] using hk

/-- `D3` **Universal `checkPtr` non-`unsupported` law on `Mach` (calls `CM.dereferenceable`)**:
for every sized thin safe pointer (`&T`, `&mut T`, `Box<T>`) and every `mach : Mach`,
`checkPtr ptr ptrTy (some mach)` NEVER returns `.error (.unsupported msg)`. -/
theorem mr_checkPtr_sized_never_unsupported (ptr : Pointer Prov) (ptrTy : PtrType)
    (pointee : PointeeInfo) (sz : Size) (al : Align) (mach : Mach) (msg : String)
    (hSafe : PtrType.safe_pointee ptrTy = some pointee) (hLay : pointee.layout = .Sized sz al)
    (hMeta : ptr.metadata = none) (hKind : PtrType.meta_kind ptrTy = .None) :
    checkPtr ptr ptrTy (some mach) ≠ .error (.unsupported msg) := by
  have hMetaOk : checkPtrMetadata ptr.metadata (PtrType.meta_kind ptrTy) (some mach) = pure () := by
    rw [hMeta, hKind]; rfl
  have hCs : ∀ (vt : Ptr → Interp VTable),
      LayoutStrategy.compute_size_and_align vt pointee.layout ptr.metadata = pure (sz, al) := by
    intro vt; rw [hLay, hMeta]; rfl
  unfold checkPtr
  refine ensureElseUb_bind_ne_unsupported
    (inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE) "Value::Ptr: pointer out-of-bounds" _ msg ?_
  dsimp only
  rw [hMetaOk, pure_bind]
  simp only [hSafe]
  rw [hCs, pure_bind]
  dsimp only
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  split
  · simp [pure, Except.pure]
  · simp [ub]
  · rename_i e _ heq
    intro h
    cases h
    exact mr_cm_dereferenceable_ne_unsupported mach.mem ptr.thin_pointer sz msg heq

/-- `D3` **Universal `checkPtrM` non-`unsupported` law (generic)**: on any memory model whose
`dereferenceable` never reports `.unsupported`, for every sized safe pointer (`&T`, `&mut T`,
`Box<T>` with `pointee.layout = .Sized sz al`, thin) and every machine, `checkPtrM _ _ (some mach)`
is never `.unsupported`. -/
theorem mr_checkPtrM_sized_never_unsupported {M : Type} [Memory M] [MemoryOps M]
    (hDeref : ∀ (mem : M) (p : ThinPointer (Memory.Provenance M)) (len : Size) (msg : String),
      MemoryOps.dereferenceable mem p len ≠ .error (.unsupported msg))
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo) (sz : Size)
    (al : Align) (mach : Machine M) (msg : String)
    (hSafe : PtrType.safe_pointee ptrTy = some pointee) (hLay : pointee.layout = .Sized sz al)
    (hMeta : ptr.metadata = none) (hKind : PtrType.meta_kind ptrTy = .None) :
    checkPtrM ptr ptrTy (some mach) ≠ .error (.unsupported msg) := by
  have hMetaOk : checkPtrMetadataM ptr.metadata (PtrType.meta_kind ptrTy)
      ((some mach).map (vtableFromPtrM ·)) = pure () := by
    rw [hMeta, hKind]; rfl
  have hCs : ∀ (vt : ThinPointer (Memory.Provenance M) → Interp VTable),
      LayoutStrategy.compute_size_and_align vt pointee.layout ptr.metadata = pure (sz, al) := by
    intro vt; rw [hLay, hMeta]; rfl
  unfold checkPtrM
  refine ensureElseUb_bind_ne_unsupported
    (inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE) "Value::Ptr: pointer out-of-bounds" _ msg ?_
  dsimp only
  rw [hMetaOk, pure_bind]
  simp only [hSafe]
  rw [hCs, pure_bind]
  dsimp only
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  refine ensureElseUb_bind_ne_unsupported _ _ _ msg ?_
  dsimp only [ConcurrentMemory.dereferenceable]
  split
  · simp [pure, Except.pure]
  · simp [ub]
  · rename_i e _ heq
    intro h
    cases h
    exact hDeref _ _ _ msg heq


/-- `D3` **Universal `checkPtrM` non-`unsupported` law on `Mach` and `MachTB`**. -/
theorem mr_checkPtrM_sized_never_unsupported_bm_tbm :
    (∀ (ptr : Pointer (Memory.Provenance BM)) (ptrTy : PtrType) (pointee : PointeeInfo) (sz : Size)
        (al : Align) (mach : Mach) (msg : String),
      PtrType.safe_pointee ptrTy = some pointee → pointee.layout = .Sized sz al →
      ptr.metadata = none → PtrType.meta_kind ptrTy = .None →
      checkPtrM ptr ptrTy (some mach) ≠ .error (.unsupported msg)) ∧
    (∀ (ptr : Pointer (Memory.Provenance TBM)) (ptrTy : PtrType) (pointee : PointeeInfo) (sz : Size)
        (al : Align) (mach : MachTB) (msg : String),
      PtrType.safe_pointee ptrTy = some pointee → pointee.layout = .Sized sz al →
      ptr.metadata = none → PtrType.meta_kind ptrTy = .None →
      checkPtrM ptr ptrTy (some mach) ≠ .error (.unsupported msg)) :=
  ⟨fun ptr ptrTy pointee sz al mach msg h1 h2 h3 h4 =>
     mr_checkPtrM_sized_never_unsupported mr_bm_dereferenceable_ne_unsupported ptr ptrTy pointee sz
       al mach msg h1 h2 h3 h4,
   fun ptr ptrTy pointee sz al mach msg h1 h2 h3 h4 =>
     mr_checkPtrM_sized_never_unsupported mr_tbm_dereferenceable_ne_unsupported ptr ptrTy pointee sz
       al mach msg h1 h2 h3 h4⟩

/-- `D3` **Universal ZST safe-pointer validity (both `some mach` and `none`)**: any in-bounds,
non-null, aligned, inhabited zero-sized safe pointer (`&()`, `Box<()>`, even dangling with no
provenance) is accepted by `checkPtrM` on `BM` and `TBM` regardless of whether a machine is passed. -/
theorem mr_checkPtrM_zst_always_ok {M : Type} [Memory M] [MemoryOps M]
    (hZeroDeref : ∀ (mem : M) (p : ThinPointer (Memory.Provenance M)),
      MemoryOps.dereferenceable mem p ⟨0⟩ = pure ())
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo) (al : Align)
    (m : Option (Machine M))
    (hSafe : PtrType.safe_pointee ptrTy = some pointee) (hLay : pointee.layout = .Sized ⟨0⟩ al)
    (hMeta : ptr.metadata = none) (hKind : PtrType.meta_kind ptrTy = .None)
    (hAddr : inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true)
    (hNull : (ptr.thin_pointer.addr != 0) = true) (hAl : Align.is_aligned al ptr.thin_pointer.addr = true)
    (hInh : pointee.inhabited = true) :
    checkPtrM ptr ptrTy m = .ok () := by
  have hE : ∀ msg, ensureElseUb true msg = pure () := fun _ => rfl
  have hMetaOk : checkPtrMetadataM ptr.metadata (PtrType.meta_kind ptrTy)
      (m.map (vtableFromPtrM ·)) = pure () := by
    rw [hMeta, hKind]; rfl
  have hCs : ∀ (vt : ThinPointer (Memory.Provenance M) → Interp VTable),
      LayoutStrategy.compute_size_and_align vt pointee.layout ptr.metadata = pure (⟨0⟩, al) := by
    intro vt; rw [hLay, hMeta]; rfl
  have hSz0 : inBounds (Size.mk 0).bytes .Signed x86_64.PTR_SIZE = true := by decide
  unfold checkPtrM
  rw [hAddr, hE, pure_bind, hMetaOk, pure_bind]
  simp only [hSafe]
  rw [hCs, pure_bind]
  dsimp only
  rw [hSz0, hE, pure_bind, hNull, hE, pure_bind, hAl, hE, pure_bind, hInh, hE, pure_bind]
  cases m with
  | none => rfl
  | some mach =>
    dsimp only [ConcurrentMemory.dereferenceable]
    rw [hZeroDeref mach.mem.memory ptr.thin_pointer]
    rfl

/-- `D3` **Universal null safe-pointer UB (both `some mach` and `none`, sized and ZST)**:
for every sized safe pointer with `addr = 0`, `checkPtrM` returns exact UB
`"Value::Ptr: null safe pointer"` (never `.unsupported`). -/
theorem mr_checkPtrM_null_always_ub {M : Type} [Memory M] [MemoryOps M]
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo) (sz : Size)
    (al : Align) (m : Option (Machine M))
    (hSafe : PtrType.safe_pointee ptrTy = some pointee) (hLay : pointee.layout = .Sized sz al)
    (hMeta : ptr.metadata = none) (hKind : PtrType.meta_kind ptrTy = .None)
    (hSize : inBounds sz.bytes .Signed x86_64.PTR_SIZE = true)
    (hZero : ptr.thin_pointer.addr = 0) :
    checkPtrM ptr ptrTy m = ub "Value::Ptr: null safe pointer" := by
  have hE : ∀ msg, ensureElseUb true msg = pure () := fun _ => rfl
  have hAddr0 : inBounds (0 : Int) .Unsigned x86_64.PTR_SIZE = true := by decide
  have hMetaOk : checkPtrMetadataM ptr.metadata (PtrType.meta_kind ptrTy)
      (m.map (vtableFromPtrM ·)) = pure () := by
    rw [hMeta, hKind]; rfl
  have hCs : ∀ (vt : ThinPointer (Memory.Provenance M) → Interp VTable),
      LayoutStrategy.compute_size_and_align vt pointee.layout ptr.metadata = pure (sz, al) := by
    intro vt; rw [hLay, hMeta]; rfl
  unfold checkPtrM
  rw [hZero, hAddr0, hE, pure_bind, hMetaOk, pure_bind]
  simp only [hSafe]
  rw [hCs, pure_bind]
  dsimp only
  rw [hSize, hE, pure_bind]
  rfl

/-- `D3` **Universal unaligned safe-pointer UB (both `some mach` and `none`)**:
for every in-bounds non-null sized safe pointer failing `Align.is_aligned`, `checkPtrM` returns
exact UB `"Value::Ptr: unaligned safe pointer"` (never `.unsupported`). -/
theorem mr_checkPtrM_unaligned_always_ub {M : Type} [Memory M] [MemoryOps M]
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo) (sz : Size)
    (al : Align) (m : Option (Machine M))
    (hSafe : PtrType.safe_pointee ptrTy = some pointee) (hLay : pointee.layout = .Sized sz al)
    (hMeta : ptr.metadata = none) (hKind : PtrType.meta_kind ptrTy = .None)
    (hAddr : inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true)
    (hSize : inBounds sz.bytes .Signed x86_64.PTR_SIZE = true)
    (hNull : (ptr.thin_pointer.addr != 0) = true)
    (hMisaligned : Align.is_aligned al ptr.thin_pointer.addr = false) :
    checkPtrM ptr ptrTy m = ub "Value::Ptr: unaligned safe pointer" := by
  have hE : ∀ msg, ensureElseUb true msg = pure () := fun _ => rfl
  have hMetaOk : checkPtrMetadataM ptr.metadata (PtrType.meta_kind ptrTy)
      (m.map (vtableFromPtrM ·)) = pure () := by
    rw [hMeta, hKind]; rfl
  have hCs : ∀ (vt : ThinPointer (Memory.Provenance M) → Interp VTable),
      LayoutStrategy.compute_size_and_align vt pointee.layout ptr.metadata = pure (sz, al) := by
    intro vt; rw [hLay, hMeta]; rfl
  unfold checkPtrM
  rw [hAddr, hE, pure_bind, hMetaOk, pure_bind]
  simp only [hSafe]
  rw [hCs, pure_bind]
  dsimp only
  rw [hSize, hE, pure_bind, hNull, hE, pure_bind, hMisaligned]
  rfl

/-- `D3` **contrast law (universal)**: WITHOUT a machine, every sized safe pointer with
provenance that passes the address, null, alignment, and inhabitedness checks is reported
`.unsupported` (`Memory::dereferenceable` needs the machine). -/
theorem mr_checkPtrM_none_sized_prov_unsupported {M : Type} [Memory M] [MemoryOps M]
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo) (sz : Size)
    (al : Align) (prov : Memory.Provenance M)
    (hSafe : PtrType.safe_pointee ptrTy = some pointee) (hLay : pointee.layout = .Sized sz al)
    (hMeta : ptr.metadata = none) (hKind : PtrType.meta_kind ptrTy = .None)
    (hAddr : inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true)
    (hSize : inBounds sz.bytes .Signed x86_64.PTR_SIZE = true)
    (hNull : (ptr.thin_pointer.addr != 0) = true) (hAl : Align.is_aligned al ptr.thin_pointer.addr = true)
    (hInh : pointee.inhabited = true) (hPos : sz.bytes ≠ 0) (hProv : ptr.thin_pointer.provenance = some prov) :
    checkPtrM ptr ptrTy none = unsupported "check_ptr for a safe pointer (Memory::dereferenceable)" := by
  have hE : ∀ m, ensureElseUb true m = pure () := fun _ => rfl
  have hMetaOk : checkPtrMetadataM ptr.metadata (PtrType.meta_kind ptrTy)
      ((none : Option (Machine M)).map (vtableFromPtrM ·)) = pure () := by
    rw [hMeta, hKind]; rfl
  have hCs : ∀ (vt : ThinPointer (Memory.Provenance M) → Interp VTable),
      LayoutStrategy.compute_size_and_align vt pointee.layout ptr.metadata = pure (sz, al) := by
    intro vt; rw [hLay, hMeta]; rfl
  unfold checkPtrM
  rw [hAddr, hE, pure_bind, hMetaOk, pure_bind]
  simp only [hSafe]
  rw [hCs, pure_bind]
  dsimp only
  rw [hSize, hE, pure_bind, hNull, hE, pure_bind, hAl, hE, pure_bind, hInh, hE, pure_bind]
  simp only [hPos, hProv, ite_false]

/-- `D3` **non-vacuity witnesses for `checkPtr` / `checkPtrM` universal laws (`Ref` and `Box`)**:
jointly witnesses the hypotheses of `mr_checkPtr_sized_never_unsupported`,
`mr_checkPtrM_sized_never_unsupported_bm_tbm`, `mr_checkPtrM_zst_always_ok`,
`mr_checkPtrM_null_always_ub`, `mr_checkPtrM_unaligned_always_ub`, and
`mr_checkPtrM_none_sized_prov_unsupported`. -/
theorem mr_checkPtrM_nonvacuity :
    (∀ (mem : BM) (p : ThinPointer (Memory.Provenance BM)),
      MemoryOps.dereferenceable mem p ⟨0⟩ = pure ()) ∧
    (∀ (mem : TBM) (p : ThinPointer (Memory.Provenance TBM)),
      MemoryOps.dereferenceable mem p ⟨0⟩ = pure ()) ∧
    (checkPtrM (M := BM) ⟨⟨4, some ((⟨0⟩, ()) : Prov)⟩, none⟩
        (.Ref .Immutable CrossFrameRefAndPanicMR.u32Pointee) none =
      unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    (checkPtrM (M := TBM) ⟨⟨4, some ((⟨0⟩, []) : TreeBorrowsProvenance)⟩, none⟩
        (.Box CrossFrameRefAndPanicMR.u32Pointee) none =
      unsupported "check_ptr for a safe pointer (Memory::dereferenceable)") ∧
    (checkPtrM (M := BM) ⟨⟨4, none⟩, none⟩ (.Box ocMrUnitPointee) none = .ok ()) ∧
    (checkPtrM (M := TBM) ⟨⟨0, none⟩, none⟩ (.Ref .Immutable ocMrUnitPointee) none =
      ub "Value::Ptr: null safe pointer") ∧
    (checkPtrM (M := BM) ⟨⟨2, none⟩, none⟩ (.Box CrossFrameRefAndPanicMR.u32Pointee) none =
      ub "Value::Ptr: unaligned safe pointer") := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

end UniversalLaws

/-! ## §5. Capstones -/

/-- **Episode 1 MiniRust capstone**: both 44-cell tables (MiniRust on `Mach` / `MachTB` and
Trusted `stepMirFn`), fail-closed ranges, exact mode sensitivity (`{11, 13, 14}`) on both
authorities, cross-authority agreement outside the documented `D1` boundary `8`, the `D1` Trusted
cast-erasure correspondence, and the universal `D1`–`D3` laws. -/
theorem ep1_minirust_opaquecast_fnentry_capstone :
    ((List.range mrOcCaseCount).map (mrOcObserve false) = mrOcExpectedBasic ∧
      (List.range mrOcCaseCount).map (mrOcObserve true) = mrOcExpectedTb) ∧
    ((List.range mrOcCaseCount).map (mrOcTrustedObserve false) = mrOcTrustedExpectedBasic ∧
      (List.range mrOcCaseCount).map (mrOcTrustedObserve true) = mrOcTrustedExpectedTb) ∧
    (∀ tb idx, mrOcCaseCount ≤ idx → mrOcObserve tb idx = .unsupported) ∧
    (∀ tb idx, mrOcCaseCount ≤ idx → mrOcTrustedObserve tb idx = .unsupported) ∧
    (∀ idx, idx < mrOcCaseCount →
      (mrOcObserve false idx ≠ mrOcObserve true idx ↔ ocCaseModeSensitive idx = true)) ∧
    (∀ idx, idx < mrOcCaseCount →
      (mrOcTrustedObserve false idx ≠ mrOcTrustedObserve true idx ↔ ocCaseModeSensitive idx = true)) ∧
    ((List.range mrOcCaseCount).all (fun idx =>
        idx == 8 || (mrOcObserve false idx == mrOcTrustedObserve false idx &&
          mrOcObserve true idx == mrOcTrustedObserve true idx)) = true) ∧
    (∀ idx, idx < 10 → idx ≠ 8 → mrOcTrustedObserve false idx = mrOcTrustedErasedObserve idx) ∧
    (mrOcTrustedObserve false 8 = .unsupported ∧ mrOcTrustedErasedObserve 8 = .okScalar 5 ∧
      mrOcObserve false 8 = .okScalar 5) ∧
    mrOcCaseCount = ocFixtureCaseCount := by
  refine ⟨mrOcObserve_table, mrOcTrustedObserve_table, mrOcObserve_out_of_range,
    mrOcTrustedObserve_out_of_range, mrOcObserve_mode_sensitivity,
    mrOcTrustedObserve_mode_sensitivity, mrOc_trusted_agreement, mrOcTrusted_cast_erasure_agree,
    ⟨?_, ?_, ?_⟩, rfl⟩ <;> kernel_rfl

/-- **Episode 1 MiniRust universal-laws & witnesses capstone**. -/
theorem ep1_minirust_opaquecast_fnentry_universal_capstone :
    type_of% @mr_translate_opaqueCast_fail_closed ∧
    type_of% @trusted_stripLeadingOpaqueCast_laws ∧
    type_of% @trusted_readProjectedValue_ocErase ∧
    type_of% @trusted_projectedValue_opaqueCast ∧
    type_of% @trusted_evalOperand_cast_deref_unsupported ∧
    type_of% @trusted_eraseLeadingOpaqueCastDecls_laws ∧
    type_of% trusted_uninitFieldWriteShell_opaque_witness ∧
    type_of% @trusted_evalOperand_move_pure_cast_deinit ∧
    type_of% @trusted_writePlaceValue_opaqueCast_laws ∧
    type_of% @trusted_evalStmt_deinit_opaqueCast ∧
    type_of% @trusted_evalStmt_setDiscriminant_opaqueCast ∧
    type_of% @trusted_evalTerminator_drop_opaqueCast ∧
    type_of% @trusted_evalFnEntryRetag_attach ∧
    type_of% @trusted_evalFnEntryRetag_ref_creates_protected_child ∧
    type_of% @trusted_restoreCallerProtectors_law ∧
    type_of% @trusted_fnEntryRetagPerm ∧
    type_of% @trusted_ocEraseRetags_retag_free ∧
    type_of% trusted_d1_d2_nonvacuity_witnesses ∧
    type_of% @mr_basic_retag_fnEntry_irrelevant ∧
    type_of% @mr_tb_retag_raw_noop ∧
    type_of% @mr_reborrowSettings_ref_protector ∧
    type_of% @mr_reborrowSettings_box_weak_protector ∧
    type_of% mr_reborrowSettings_nonvacuity ∧
    type_of% @mr_cm_dereferenceable_ne_unsupported ∧
    type_of% @mr_checkPtr_sized_never_unsupported ∧
    type_of% @mr_checkPtrM_sized_never_unsupported_bm_tbm ∧
    type_of% @mr_checkPtrM_zst_always_ok ∧
    type_of% @mr_checkPtrM_null_always_ub ∧
    type_of% @mr_checkPtrM_unaligned_always_ub ∧
    type_of% @mr_checkPtrM_none_sized_prov_unsupported ∧
    type_of% mr_checkPtrM_nonvacuity ∧
    type_of% mr_oc_exact_ub_diagnostics ∧
    type_of% mr_oc_minimize_lowering_contrasts ∧
    type_of% mr_checkPtr_some_vs_none_contrast ∧
    type_of% mr_checkPtrM_tb_some_vs_none_contrast :=
  ⟨@mr_translate_opaqueCast_fail_closed, @trusted_stripLeadingOpaqueCast_laws,
   @trusted_readProjectedValue_ocErase, @trusted_projectedValue_opaqueCast,
   @trusted_evalOperand_cast_deref_unsupported, @trusted_eraseLeadingOpaqueCastDecls_laws,
   trusted_uninitFieldWriteShell_opaque_witness, @trusted_evalOperand_move_pure_cast_deinit,
   @trusted_writePlaceValue_opaqueCast_laws, @trusted_evalStmt_deinit_opaqueCast,
   @trusted_evalStmt_setDiscriminant_opaqueCast, @trusted_evalTerminator_drop_opaqueCast,
   @trusted_evalFnEntryRetag_attach, @trusted_evalFnEntryRetag_ref_creates_protected_child,
   @trusted_restoreCallerProtectors_law, @trusted_fnEntryRetagPerm, @trusted_ocEraseRetags_retag_free,
   trusted_d1_d2_nonvacuity_witnesses, @mr_basic_retag_fnEntry_irrelevant, @mr_tb_retag_raw_noop,
   @mr_reborrowSettings_ref_protector, @mr_reborrowSettings_box_weak_protector,
   mr_reborrowSettings_nonvacuity, @mr_cm_dereferenceable_ne_unsupported,
   @mr_checkPtr_sized_never_unsupported, @mr_checkPtrM_sized_never_unsupported_bm_tbm,
   @mr_checkPtrM_zst_always_ok, @mr_checkPtrM_null_always_ub, @mr_checkPtrM_unaligned_always_ub,
   @mr_checkPtrM_none_sized_prov_unsupported, mr_checkPtrM_nonvacuity, mr_oc_exact_ub_diagnostics,
   mr_oc_minimize_lowering_contrasts, mr_checkPtr_some_vs_none_contrast,
   mr_checkPtrM_tb_some_vs_none_contrast⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict root isolation: ZERO `Miri.*`, `LeanMiriSpec.*`, or `Anneal.*` imports!
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName ||
        (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by MiniRustSpec.OpaqueCastAndFnEntryProtectorMR"
  let ns := `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR
  -- 2. Bridge-reality audit: our theorems transitively reach the real interpreters.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `mrOcObserve_table, `MiniRustSpec.Interp.stepM),
      (ns ++ `mrOcObserve_table, `MiniRustSpec.CrossFrameRefAndPanicMR.bootProgramM),
      (ns ++ `mrOcObserve_table, `MiniRustSpec.Interp.checkPtrM),
      (ns ++ `mrOcObserve_table, `MiniRustSpec.Interp.ConcurrentMemory.dereferenceable),
      (ns ++ `mrOcObserve_table, `MiniRustSpec.Interp.placeLoadM),
      (ns ++ `mrOcTrustedObserve_table, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `mrOcTrustedObserve_table, `Trusted.Rustc.V2026_06_01.MirSemantics.initMachineStateWithCallees),
      (ns ++ `mrOcTrusted_cast_erasure, `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn),
      (ns ++ `mrOcTrusted_cast_erasure, `MiniRustSpec.OpaqueCastAndFnEntryProtectorMR.ocEraseBody),
      (ns ++ `mr_translate_opaqueCast_fail_closed, `MiniRustSpec.Correspondence.translatePlace),
      (ns ++ `mr_translate_opaqueCast_fail_closed, `MiniRustSpec.Correspondence.simpleProj),
      (ns ++ `trusted_stripLeadingOpaqueCast_laws, `Trusted.Rustc.V2026_06_01.MirSemantics.stripLeadingOpaqueCast),
      (ns ++ `trusted_eraseLeadingOpaqueCastDecls_laws, `Trusted.Rustc.V2026_06_01.MirSemantics.eraseLeadingOpaqueCastDecls),
      (ns ++ `trusted_uninitFieldWriteShell_opaque_witness, `Trusted.Rustc.V2026_06_01.MirSemantics.uninitFieldWriteShell?),
      (ns ++ `trusted_readProjectedValue_ocErase, `Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue),
      (ns ++ `trusted_projectedValue_opaqueCast, `Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue),
      (ns ++ `trusted_evalOperand_cast_deref_unsupported, `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand),
      (ns ++ `trusted_evalOperand_move_pure_cast_deinit, `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand),
      (ns ++ `trusted_writePlaceValue_opaqueCast_laws, `Trusted.Rustc.V2026_06_01.MirSemantics.writePlaceValue),
      (ns ++ `trusted_evalStmt_deinit_opaqueCast, `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt),
      (ns ++ `trusted_evalStmt_setDiscriminant_opaqueCast, `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt),
      (ns ++ `trusted_evalTerminator_drop_opaqueCast, `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator),
      (ns ++ `trusted_evalFnEntryRetag_attach, `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnEntryRetag),
      (ns ++ `trusted_evalFnEntryRetag_ref_creates_protected_child, `Trusted.Rustc.V2026_06_01.MirSemantics.evalFnEntryRetag),
      (ns ++ `trusted_restoreCallerProtectors_law, `Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors),
      (ns ++ `trusted_fnEntryRetagPerm, `Trusted.Rustc.V2026_06_01.MirSemantics.fnEntryRetagPerm),
      (ns ++ `mr_basic_retag_fnEntry_irrelevant, `MiniRustSpec.Interp.MemoryOps.retag_ptr),
      (ns ++ `mr_tb_retag_raw_noop, `MiniRustSpec.Interp.TreeBorrowsMemory.retag_ptr),
      (ns ++ `mr_reborrowSettings_ref_protector, `MiniRustSpec.Interp.ReborrowSettings.new),
      (ns ++ `mr_reborrowSettings_box_weak_protector, `MiniRustSpec.Interp.ReborrowSettings.new),
      (ns ++ `mr_cm_dereferenceable_ne_unsupported, `MiniRustSpec.Interp.CM.dereferenceable),
      (ns ++ `mr_checkPtr_sized_never_unsupported, `MiniRustSpec.Interp.checkPtr),
      (ns ++ `mr_checkPtr_sized_never_unsupported, `MiniRustSpec.Interp.CM.dereferenceable),
      (ns ++ `mr_checkPtrM_sized_never_unsupported, `MiniRustSpec.Interp.checkPtrM),
      (ns ++ `mr_bm_dereferenceable_ne_unsupported, `MiniRustSpec.Interp.MemoryOps.dereferenceable),
      (ns ++ `mr_basicMemory_check_ptr_ne_unsupported, `MiniRustSpec.Interp.BasicMemory.check_ptr),
      (ns ++ `mr_checkPtr_some_vs_none_contrast, `MiniRustSpec.Interp.checkPtr),
      (ns ++ `mr_checkPtrM_tb_some_vs_none_contrast, `MiniRustSpec.Interp.checkPtrM) ]
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
      if ns.isPrefixOf n || (`MiniRustSpec.CrossFrameRefAndPanicMR).isPrefixOf n ||
          (`MiniRustSpec.WideDstAndMaybeUninitMR).isPrefixOf n ||
          n == `MiniRustSpec.Interp.checkPtrM || n == `MiniRustSpec.Interp.checkPtr then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach real {req}"
  -- 3. Constructive `[propext, Quot.sound]` purity across the ENTIRE namespace (ZERO
  -- `Classical.choice` allowed on any theorem or definition authored here!), standard-3-axiom
  -- purity across the environment, and a non-vacuous theorem count floor.
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
      if ns.isPrefixOf c && !c.isInternal && a == ``Classical.choice then
        throwError "{c} must be constructive (zero Classical.choice) but depends on Classical.choice"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 45 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end MiniRustSpec.OpaqueCastAndFnEntryProtectorMR
