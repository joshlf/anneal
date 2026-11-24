-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.ParametricCore.StageCutV2026Bridge
import Anneal.PureLift.SpatialMemV2026

/-!
# Episode 2 End-to-End `V2026_06_01` Stage-Cut & `SpatialMemV2026` Canary Suite

Kernel-checked positive witnesses and fail-closed negative boundary canaries across
all five converged capabilities against unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics`:

- **Witness 1 (`ByteRun`)**: padded `(u8, [pad; 3], u32)` `copyRangeComp` preserving
  `.uninit` padding + `decodeValueFromBytes` field recovery + disjoint sibling framing,
  and `[u16; 4]` `Rvalue.repeat` `CapturedMir` execution (`MirWpConverges`) matching
  `copyRepeatedlyComp` / `writeRepeatRunsComp`.
- **Witness 2 (`OverflowCastJoin`)**: real 8-block multi-diamond `CapturedMir` pipeline
  (`u32 -> u16` narrowing cast, `mulWithOverflow` + `SwitchInt` diamond,
  `addWithOverflow` + `SwitchInt` diamond, `u16 -> u32` widening cast, and
  interval-guarded `addUnchecked`) proved via $O(m)$ `OvfCastStageCut` composition →
  `MirWpConverges` for universally bounded inputs (`∀ x ≤ 20000`) plus exact functional
  (`r = 3 * x + 107`) and concrete (`1234 ↦ 3809`) witnesses, and (2b) the same pipeline
  run through `evalBlockTreeToCut` over a `ValidBlockTree` of the real `CapturedMir`
  blocks and sealed into a live `StepStageCut` → `MirWpConverges`.
- **Witness 3 (`CallStackUnwind` + `RefFrame`)**: real caller + inline callee
  `CapturedMir` bodies for (a) normal `TerminatorKind.call` with `&mut u32` writeback +
  a REAL `Retag(FnEntry)` strong protector (`activeProtectors = [1]` in the callee,
  released to `[]` by `return_`) + bystander local framing AND a real `&mut [u8]` slice-writing
  `CallSpecCut` → `mirWpConverges_of_callSpecCut_normal_cleanup` with `UpdatesOnly` +
  `exitFrameWithProtectors`, (b) callee `TerminatorKind.assert` unwinding through caller
  `UnwindAction.cleanup` landing pad into clean recovery → `MirWpConverges`, and (c)
  universal 3-node `topo3` disjoint sibling commutation (`protectedRefFrame_shared_topo3_commutation`)
  bridged to `TreeBorrowPerm ↔ TbPermission`.
- **Witness 3d (UNIVERSAL MIR Tree Borrows ⇒ `RefFrame` step refinement)**: for ALL
  `x ≤ 10000, bystander ≤ 10000` on the REAL `callerNormalBody → calleeBumpMutBody` run,
  the MIR deref write and `return_` commute EXACTLY with `performRangedAccess` /
  `exitFrameWithProtectors` on `rangedBorrowTreeOfMirAlloc` via general parametric
  theorems `rangedBorrowTreeOfMirAlloc_twoTag_{write,return}_refines`.
- **Witness 3e (Range-segmented subslice borrows & `accessed`-bit contrast)**:
  `rangedBorrowTreeOfMirAllocSegmented` commutes disjoint same-allocation subslice borrows
  (`[0..2)` and `[2..4)`) and releases protectors cleanly where flat 1-segment projection
  spuriously fails with `.ProtectedDisabled`, alongside `mirSemantics_vs_refFrame_accessed_coarsening`.
- **Witness 4 (`SpatialMemV2026`)**: full `freezePaddedToMem` → `mutatePaddedInMem` →
  `reabsorbPaddedFromMem` → `endPaddedLoan` → `deallocatePromotedLocal` lifecycle on
  both padded `(u8, [pad; 3], u32)` (contrasted with `u8U32Padded_freeze_refused`) and
  provenance-carrying `(u8, [pad; 7], *mut u8)` verified against `decodeValueFromBytes`.
- **Negative Boundary Canaries (`N1..N4`)**: OOB/zero-length/immutable/relocated copy
  rejection, overflowing `mulWithOverflow` arm routing + interval rejection, diverging
  `return_` UB + `.unreachable` assert UB + `.ProtectedDisabled` rejection (N3b: REAL
  inline diverging `TerminatorKind.call` (`target = none`) faulting from the caller's
  entry state vs. the converging contrast, and `exitFrameWithProtectors` failing with
  `.AccessFailure _ _ _ (.ProtectedDisabled .Unique)`), and
  non-padding `.uninit` / provenance stripping / surplus forgery / pinned-loan pure
  write blocking.
-/

namespace Anneal.ParametricStageCutAndSpatialMemTests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.ParametricCore
open Anneal.ParametricCore.V2026Bridge
open Anneal.ParametricCore.StageCutV2026Bridge
open Anneal.PureLift
open Anneal.PureLift.SpatialMemV2026
open Anneal.PureLift.V2026_06_01Bridge
open Anneal.RefFrame

/-! ## 0. Shared Real `V2026_06_01` MIR AST Fixtures -/

private def u32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def u16Layout : TypeLayout :=
  { size := ⟨2⟩, align := ⟨2⟩
    backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩)
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def boolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩)
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def u16BoolLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨2⟩
    backendRepr :=
      .scalarPair (.initialized (.int 16 false) ⟨0, 65535⟩)
        (.initialized (.int 8 false) ⟨0, 1⟩)
    fields := .arbitrary [⟨0⟩, ⟨2⟩] [0, 1], variants := .single 0, isUninhabited := false }

private def u16Arr4Layout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨2⟩
    backendRepr := .memory
    fields := .array ⟨2⟩ 4, variants := .single 0, isUninhabited := false }

private def ptrLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩
    backendRepr := .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def u8Layout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩)
    fields := .primitive, variants := .single 0, isUninhabited := false }

private def fatPtrLayout : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩
    backendRepr :=
      .scalarPair (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
        (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩)
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1], variants := .single 0, isUninhabited := false }

private def u8Arr4Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩
    backendRepr := .memory
    fields := .array ⟨1⟩ 4, variants := .single 0, isUninhabited := false }

private def u8Arr2Layout : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩
    backendRepr := .memory
    fields := .array ⟨1⟩ 2, variants := .single 0, isUninhabited := false }

private def testLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true
    entries :=
      [u32Layout, u16Layout, boolLayout, u16BoolLayout, u16Arr4Layout,
       ptrLayout, u8Layout, fatPtrLayout, u8Arr4Layout, u8Arr2Layout] }

private def u32T : Ty := { kind := .uint .u32, layoutIdx := 0 }
private def u16T : Ty := { kind := .uint .u16, layoutIdx := 1 }
private def boolT : Ty := { kind := .bool, layoutIdx := 2 }
private def u16BoolT : Ty := { kind := .tuple [.uint .u16, .bool], layoutIdx := 3 }
private def u16Arr4T : Ty := { kind := .array (.uint .u16) 4, layoutIdx := 4 }
private def refMutU32T : Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 5 }
private def u8T : Ty := { kind := .uint .u8, layoutIdx := 6 }
private def refMutSliceU8T : Ty := { kind := .ref .mut (.slice (.uint .u8)), layoutIdx := 7 }
private def refSharedSliceU8T : Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 7 }
private def u8Arr4T : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 8 }
private def refMutU8Arr4T : Ty := { kind := .ref .mut (.array (.uint .u8) 4), layoutIdx := 5 }
private def u8Arr2T : Ty := { kind := .array (.uint .u8) 2, layoutIdx := 9 }

private def u32C (n : Nat) : Operand :=
  .constant { ty := u32T, val := .scalar (.int { bits := n, sizeBytes := 4 }) }

private def u16C (n : Nat) : Operand :=
  .constant { ty := u16T, val := .scalar (.int { bits := n, sizeBytes := 2 }) }

private def fnOp (path : String) : Operand :=
  .constant { ty := { kind := .fnDef path [], layoutIdx := 0 }, val := .zeroSized }

private def pl (l : Nat) (proj : List ProjectionElem := []) : Place :=
  { local_ := l, projection := proj }

private def mkSt (k : StatementKind) : Statement :=
  { kind := k, span := "ParametricStageCutAndSpatialMemTests" }

private def mkBb (ss : List Statement) (t : TerminatorKind) (isClean : Bool := false) :
    BasicBlockData :=
  { statements := ss
    terminator := { kind := t, span := "ParametricStageCutAndSpatialMemTests" }
    isCleanup := isClean }

private def decl (m : Mutability) (ty : Ty) : LocalDecl :=
  { mutability := m, ty := ty, debugName := none }

private def mkBody (name : String) (argCount : Nat) (ds : List LocalDecl)
    (bbs : List BasicBlockData) : CapturedMir :=
  { defPath := name
    phase := .runtimeOptimized
    role := .subject
    argCount := argCount
    localDecls := ds
    basicBlocks := bbs
    fnAbi := Anneal.PureMirExec.pureAdtMultiBlockBody.fnAbi
    layouts := testLayouts
    allocations := [] }

private theorem step_to_mirWp {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (hStep : Anneal.PureMirExec.mirStep body s = .cont s')
    (hNext : MirWpConverges body s' post) :
    MirWpConverges body s post :=
  Anneal.PureMirExec.mirWpConverges_of_mirStep_cont hStep hNext

private theorem done_to_mirWp {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    {post : MirOutcome → Prop}
    (hDone : Anneal.PureMirExec.mirStep body s = .done out)
    (hPost : post out) :
    MirWpConverges body s post :=
  MirWpConverges.ret_of_step (Anneal.PureMirExec.stepMirFn_of_mirStep_done hDone) hPost

private theorem nat_ble_false_of_lt {a b : Nat} (h : a < b) : Nat.ble b a = false := by
  cases hB : Nat.ble b a with
  | false => rfl
  | true => have := Nat.ble_eq.mp hB; omega

private theorem wrapScalarBits_of_lt {x m : Nat} (h : x < m) : wrapScalarBits x m = x := by
  unfold wrapScalarBits
  cases hZ : Nat.beq m 0 with
  | true => have := Nat.beq_eq.mp hZ; omega
  | false => rw [nat_ble_false_of_lt h]

/-! ## Witness 1: `ByteRun` — Padded `(u8, [pad; 3], u32)` Copy & `[u16; 4]` `Rvalue.repeat` -/

/-- **Witness 1a (`ByteRun` padded copy & framing)**: copying a padded
`#[repr(C)] (u8, [pad; 3], u32)` struct (`a = 0x5A`, `b = 0x12345678`) across
`V2026ByteMem` via `copyRangeComp` preserves `.uninit` padding `[1..4)` verbatim,
recovers the exact MIR `Value` via unmodified `decodeValueFromBytes`, and frames a
disjoint sibling allocation. -/
theorem witness1a_byterun_padded_u8u32_copy_and_frame :
    let s : U8U32Struct := ⟨0x5A, ⟨0x12345678, by decide⟩⟩
    let srcBytes := flattenByteRuns abstractByteRunCodec (paddedU8U32ByteRuns s)
    let siblingBytes : List AbstractByte :=
      [.init 0xDE none, .init 0xAD none, .init 0xBE none, .init 0xEF none]
    let m0 : V2026ByteMem :=
      { nextAllocId := 4
        allocs :=
          [ ⟨1, 4, .mut, srcBytes, true⟩
          , ⟨2, 4, .mut, List.replicate 8 AbstractByte.uninit, true⟩
          , ⟨3, 4, .mut, siblingBytes, true⟩ ] }
    let srcL : ByteSubLens Nat := ⟨1, 0, 8⟩
    let dstL : ByteSubLens Nat := ⟨2, 0, 8⟩
    let sibL : ByteSubLens Nat := ⟨3, 0, 4⟩
    ∃ m1 : V2026ByteMem,
      copyRangeComp srcL dstL m0 = some m1 ∧
      dstL.get m1 = some (paddedU8U32Encode s) ∧
      readV2026Bytes m1 ⟨2, 1⟩ 3 1 = some [.uninit, .uninit, .uninit] ∧
      (∀ bs, dstL.get m1 = some bs →
        decodeValueFromBytes defaultCodecFuel u8U32BodyCtx.body.layouts (u8U32Ty 0) bs =
          some (.aggregate 0 [.scalar ⟨0x5A, 1⟩, .scalar ⟨0x12345678, 4⟩])) ∧
      sibL.get m1 = some siblingBytes := by
  intro s srcBytes siblingBytes m0 srcL dstL sibL
  let m1 : V2026ByteMem :=
    { nextAllocId := 4
      allocs :=
        [ ⟨1, 4, .mut, srcBytes, true⟩
        , ⟨2, 4, .mut, srcBytes, true⟩
        , ⟨3, 4, .mut, siblingBytes, true⟩ ] }
  have hCopy : copyRangeComp srcL dstL m0 = some m1 := rfl
  have hSrc : srcL.get m0 = some (paddedU8U32Encode s) := rfl
  have hSound :=
    copyRangeComp_paddedU8U32_preserves_decode (layouts := u8U32BodyCtx.body.layouts)
      (idx := 0) (l := u8U32TypeLayout) (mem := [0, 1])
      rfl rfl rfl srcL dstL m0 m1 s hSrc hCopy
  refine ⟨m1, hCopy, hSound.1, rfl, hSound.2.1, ?_⟩
  have hDisj : sibL.Disjoint V2026ByteMem dstL := Or.inl (by decide)
  rw [hSound.2.2 sibL hDisj]
  rfl

/-- Real `V2026_06_01` `CapturedMir` body executing `Rvalue.repeat (.copy _1) 4` to
build `[u16; 4]`. -/
def repeatU16x4Body : CapturedMir :=
  mkBody "tests::repeat_u16_x4" 1
    [decl .mut u16Arr4T, decl .not u16T]
    [mkBb [mkSt (.assign (pl 0) (.repeat (.copy (pl 1)) 4))] .return_]

/-- **Witness 1b (`ByteRun` `[u16; 4]` repeat fusion + real `Rvalue.repeat` MIR execution)**:
for EVERY `x < 65536`, executing `repeatU16x4Body` converges via `MirWpConverges` to
`.aggregate 0 (replicateValue 4 (.scalar ⟨x, 2⟩))`, whose unmodified
`encodeValueToBytes` equals the 4× repeated byte-run `flattenByteRuns abstractByteRunCodec
(repeatByteRuns 4 ...)`, matching fused `copyRepeatedlyComp = writeRepeatRunsComp` on
`V2026ByteMem`. -/
theorem witness1b_byterun_repeat_u16x4_mir_wp_converges (x : Nat) (hLt : x < 65536) :
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨x, 2⟩)] }
        memory := {} }
    let elemRuns : List (ByteRun (Nat × Nat)) :=
      [.initPlain [UInt8.ofNat x, UInt8.ofNat (x / 256)]]
    let expectedBytes := flattenByteRuns abstractByteRunCodec (repeatByteRuns 4 elemRuns)
    let m0 : V2026ByteMem :=
      { nextAllocId := 3
        allocs :=
          [ ⟨1, 2, .mut, flattenByteRuns abstractByteRunCodec elemRuns, true⟩
          , ⟨2, 2, .mut, List.replicate 8 AbstractByte.uninit, true⟩ ] }
    MirWpConverges repeatU16x4Body ms0
      (fun out =>
        match out with
        | .normal (v, _) =>
          v = .aggregate 0 (replicateValue 4 (.scalar ⟨x, 2⟩)) ∧
          encodeValueToBytes defaultCodecFuel testLayouts u16Arr4T v = some expectedBytes
        | _ => False) ∧
    copyRepeatedlyComp (Mem := V2026ByteMem) (Addr := Nat) (Byte := AbstractByte)
        ⟨1, 0, 2⟩ 2 0 4 m0 =
      writeRepeatRunsComp abstractByteRunCodec 2 0 4 elemRuns m0 ∧
    (∃ m1, copyRepeatedlyComp (Mem := V2026ByteMem) (Addr := Nat) (Byte := AbstractByte)
        ⟨1, 0, 2⟩ 2 0 4 m0 = some m1 ∧
      (⟨2, 0, 8⟩ : ByteSubLens Nat).get m1 = some expectedBytes) := by
  intro ms0 elemRuns expectedBytes m0
  have hStep1 : Anneal.PureMirExec.mirStep repeatU16x4Body ms0 =
      .cont { frame := { blockIdx := 0, stmtIdx := 1
                         locals := [.init (.aggregate 0 (replicateValue 4 (.scalar ⟨x, 2⟩))),
                                    .init (.scalar ⟨x, 2⟩)] }
              memory := {} } := rfl
  have hStep2 : Anneal.PureMirExec.mirStep repeatU16x4Body
      { frame := { blockIdx := 0, stmtIdx := 1
                   locals := [.init (.aggregate 0 (replicateValue 4 (.scalar ⟨x, 2⟩))),
                              .init (.scalar ⟨x, 2⟩)] }
        memory := {} } =
      .done (.normal (.aggregate 0 (replicateValue 4 (.scalar ⟨x, 2⟩)), {})) := rfl
  have hMir : MirWpConverges repeatU16x4Body ms0
      (fun out =>
        match out with
        | .normal (v, _) =>
          v = .aggregate 0 (replicateValue 4 (.scalar ⟨x, 2⟩)) ∧
          encodeValueToBytes defaultCodecFuel testLayouts u16Arr4T v = some expectedBytes
        | _ => False) :=
    step_to_mirWp hStep1 (done_to_mirWp hStep2
      ⟨rfl, encodeArrayU16Repeat_eq_flattenByteRuns testLayouts 4 x⟩)
  have hFuse :
      copyRepeatedlyComp (Mem := V2026ByteMem) (Addr := Nat) (Byte := AbstractByte)
          ⟨1, 0, 2⟩ 2 0 4 m0 =
        writeRepeatRunsComp abstractByteRunCodec 2 0 4 elemRuns m0 := by
    refine copyRepeatedlyComp_eq_writeRepeatRunsComp (src := ⟨1, 0, 2⟩) (dstAddr := 2)
      (dstOff := 0) (n := 4) (m := m0) abstractByteRunCodec elemRuns
      (by decide) (show 0 < 2 by decide) rfl rfl (Or.inl (show (2 : Nat) ≠ 1 by decide))
  have _ := hLt
  exact ⟨hMir, hFuse, ⟨_, rfl, rfl⟩⟩

/-- Real `V2026_06_01` `CapturedMir` body copying a 2-byte slice `src : &[u8]`
(`[0..2)` in `Memory.callerLocals[12]`) into `dst : &mut [u8]` (`[2..4)` in
`Memory.callerLocals[12]`), then transitioning to `bb1` to return `2u32`. -/
def copy2BytesSliceBody : CapturedMir :=
  mkBody "tests::copy_2_bytes_slice" 2
    [decl .mut u32T, decl .not refSharedSliceU8T, decl .not refMutSliceU8T, decl .mut u8Arr2T]
    [ mkBb
        [ mkSt (.assign (pl 3) (.use (.copy (pl 1 [.deref]))))
        , mkSt (.assign (pl 2 [.deref]) (.use (.copy (pl 3)))) ]
        (.goto 1)
    , mkBb [mkSt (.assign (pl 0) (.use (u32C 2)))] .return_ ]

/-- **Witness 1c (REAL `CapturedMir` → `ByteRunCopyCut` over `ValidBlockTree` → `MirWpConverges`)**:
for ALL `b0 b1 sib0 sib1 : UInt8`, seals the live `BlockTree`-backed execution of
`copy2BytesSliceBody` (`bb0 -> bb1`) as a genuine `ByteRunCopyCut` over
`Memory.callerLocals` (`memCallerByteStoreOps`, op `copyRange ⟨⟨12⟩, 0, 2⟩ ⟨⟨12⟩, 2, 2⟩`),
lifts it to unmodified `mirDetStep` via `byteRunCopyCut_mir_of_validBlockTree`, and
transports it via `mirWpConverges_of_byteRunCopyCut` into `MirWpConverges`, proving both
the copied destination bytes `[b0, b1]` and disjoint sibling slice `[sib0, sib1]` framing. -/
theorem witness1c_byterun_real_mir_copy_cut_mir_wp_converges
    (b0 b1 sib0 sib1 : UInt8) :
    let srcL : ByteSubLens CallerLocalAddr := ⟨⟨12⟩, 0, 2⟩
    let dstL : ByteSubLens CallerLocalAddr := ⟨⟨12⟩, 2, 2⟩
    let sibL : ByteSubLens CallerLocalAddr := ⟨⟨12⟩, 4, 2⟩
    let borrowSrc : BorrowEntry :=
      { tag := 1, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .frozen, rangeOffset := 0, rangeLen := 2 }
    let borrowDst : BorrowEntry :=
      { tag := 2, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, rangeOffset := 2, rangeLen := 2 }
    let m0 : Memory :=
      { borrows := [borrowDst, borrowSrc], nextTag := 3
        callerLocals :=
          List.replicate 12 LocalSlot.uninit ++ [u8BytesToSlot [b0, b1, 0, 0, sib0, sib1]] }
    let m1 : Memory :=
      { m0 with
        callerLocals :=
          List.replicate 12 LocalSlot.uninit ++ [u8BytesToSlot [b0, b1, b0, b1, sib0, sib1]] }
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit,
                              .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                              .init (.aggregate 0 [.ptr ⟨2, 2⟩ 8, .scalar ⟨2, 8⟩]),
                              .uninit] }
        memory := m0 }
    let ms1 : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := 0
                   locals := [.uninit,
                              .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                              .init (.aggregate 0 [.ptr ⟨2, 2⟩ 8, .scalar ⟨2, 8⟩]),
                              .init (.aggregate 0 [.scalar ⟨b0.toNat, 1⟩, .scalar ⟨b1.toNat, 1⟩])] }
        memory := m1 }
    ByteRunCopyCut (mirDetStep copy2BytesSliceBody) (fun ms => ms.memory)
      [ByteRunCopyOp.copyRange srcL dstL] 3 ms0 ms1 ∧
    MirWpConverges copy2BytesSliceBody ms0
      (fun out =>
        match out with
        | .normal (.scalar ⟨2, 4⟩, mFinal) =>
          dstL.get mFinal = some [b0, b1] ∧ sibL.get mFinal = some [sib0, sib1]
        | _ => False) := by
  intro srcL dstL sibL borrowSrc borrowDst m0 m1 ms0 ms1
  let bt := BlockTree.ofList copy2BytesSliceBody.basicBlocks
  have hExecOp :
      execByteRunCopyOps (Mem := Memory) (Addr := CallerLocalAddr) (Byte := UInt8)
        [ByteRunCopyOp.copyRange srcL dstL] m0 = some m1 := by
    rw [execByteRunCopyOps_cons]
    unfold ByteRunCopyOp.exec copyRangeComp
    have hSrcG : srcL.get m0 = some [b0, b1] := by
      unfold srcL ByteSubLens.get memCallerByteStoreOps
      change (match ParametricCore.listGet? m0.callerLocals 12 with
        | none => none
        | some slot =>
          match slotAsU8Bytes? slot with
          | none => none
          | some bytes =>
            match Nat.ble (0 + 2) bytes.length with
            | true => some ((bytes.drop 0).take 2)
            | false => none) = some [b0, b1]
      have hG : ParametricCore.listGet? m0.callerLocals 12 =
          some (u8BytesToSlot [b0, b1, 0, 0, sib0, sib1]) := rfl
      rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]; rfl
    have hDstS : dstL.set m0 [b0, b1] = some m1 := by
      unfold dstL ByteSubLens.set memCallerByteStoreOps
      change (match ParametricCore.listGet? m0.callerLocals 12 with
        | none => none
        | some slot =>
          match slotAsU8Bytes? slot with
          | none => none
          | some bytes =>
            match Nat.ble (2 + 2) bytes.length with
            | true =>
              match ParametricCore.listSet? m0.callerLocals 12 (u8BytesToSlot (listSplice bytes 2 [b0, b1])) with
              | some cl' => some { m0 with callerLocals := cl' }
              | none => none
            | false => none) = some m1
      have hG : ParametricCore.listGet? m0.callerLocals 12 =
          some (u8BytesToSlot [b0, b1, 0, 0, sib0, sib1]) := rfl
      rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]; rfl
    dsimp only
    have hLenEq : Nat.beq srcL.len dstL.len = true := rfl
    rw [hLenEq, hSrcG]; dsimp only; rw [hDstS]; rfl
  have hBtCut :
      ByteRunCopyCut (mirDetStepWith copy2BytesSliceBody bt.lookupForced?) (fun ms => ms.memory)
        [ByteRunCopyOp.copyRange srcL dstL] 3 ms0 ms1 := by
    apply seal_byteRunCopyCut
    refine ⟨?_, hExecOp⟩
    exact StepStageCut.step (s₁ := { ms0 with
        frame := { ms0.frame with
          stmtIdx := 1
          locals := [.uninit,
                     .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                     .init (.aggregate 0 [.ptr ⟨2, 2⟩ 8, .scalar ⟨2, 8⟩]),
                     .init (.aggregate 0 [.scalar ⟨b0.toNat, 1⟩, .scalar ⟨b1.toNat, 1⟩])] } }) rfl
      (StepStageCut.step (s₁ := { ms1 with frame := { ms1.frame with blockIdx := 0, stmtIdx := 2 } }) rfl
        (StepStageCut.step (s₁ := ms1) rfl (StepStageCut.refl _ 0 ms1)))
  have hLiveCut :
      ByteRunCopyCut (mirDetStep copy2BytesSliceBody) (fun ms => ms.memory)
        [ByteRunCopyOp.copyRange srcL dstL] 3 ms0 ms1 :=
    byteRunCopyCut_mir_of_validBlockTree (valid_blockTree_ofList copy2BytesSliceBody.basicBlocks) hBtCut
  have hGetDst : dstL.get m1 = some [b0, b1] := by
    unfold dstL ByteSubLens.get memCallerByteStoreOps
    change (match ParametricCore.listGet? m1.callerLocals 12 with
      | none => none
      | some slot =>
        match slotAsU8Bytes? slot with
        | none => none
        | some bytes =>
          match Nat.ble (2 + 2) bytes.length with
          | true => some ((bytes.drop 2).take 2)
          | false => none) = some [b0, b1]
    have hG : ParametricCore.listGet? m1.callerLocals 12 =
        some (u8BytesToSlot [b0, b1, b0, b1, sib0, sib1]) := rfl
    rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]; rfl
  have hGetSib : sibL.get m1 = some [sib0, sib1] := by
    unfold sibL ByteSubLens.get memCallerByteStoreOps
    change (match ParametricCore.listGet? m1.callerLocals 12 with
      | none => none
      | some slot =>
        match slotAsU8Bytes? slot with
        | none => none
        | some bytes =>
          match Nat.ble (4 + 2) bytes.length with
          | true => some ((bytes.drop 4).take 2)
          | false => none) = some [sib0, sib1]
    have hG : ParametricCore.listGet? m1.callerLocals 12 =
        some (u8BytesToSlot [b0, b1, b0, b1, sib0, sib1]) := rfl
    rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]; rfl
  refine ⟨hLiveCut, mirWpConverges_of_byteRunCopyCut hLiveCut (fun _ => ?_)⟩
  let ms2 : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 1
                 locals := [.init (.scalar ⟨2, 4⟩),
                            .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                            .init (.aggregate 0 [.ptr ⟨2, 2⟩ 8, .scalar ⟨2, 8⟩]),
                            .init (.aggregate 0 [.scalar ⟨b0.toNat, 1⟩, .scalar ⟨b1.toNat, 1⟩])] }
      memory := m1 }
  exact step_to_mirWp (body := copy2BytesSliceBody) (s := ms1) (s' := ms2) rfl
    (done_to_mirWp (body := copy2BytesSliceBody) (s := ms2)
      (out := .normal (.scalar ⟨2, 4⟩, m1)) rfl ⟨hGetDst, hGetSib⟩)

/-! ## Witness 2: `OverflowCastJoin` — Real 8-Block Multi-Diamond `CapturedMir` Pipeline -/

/-- Real 8-block multi-diamond `V2026_06_01` `CapturedMir` pipeline with clean
block boundaries at every `OvfCastStageCut` join point:
- `bb0` (Stage 1): narrowing `u32 -> u16` (`CastKind.intToInt`) → `bb1`
- `bb1` + `bb2` (Stage 2): `BinOp.mulWithOverflow` by `3u16` + `SwitchInt` diamond
  (`bb2` extracts `_2 := _4.0` → `bb3`; overflow → `bb7`)
- `bb3` + `bb4` (Stage 3): `BinOp.addWithOverflow` by `7u16` + `SwitchInt` diamond
  (`bb4` extracts `_2 := _5.0` → `bb5`; overflow → `bb7`)
- `bb5` (Stage 4): widening `u16 -> u32` (`CastKind.intToInt`) → `bb6`
- `bb6` (Tail): interval-guarded `BinOp.addUnchecked` by `100u32` → `return_`
- `bb7` (Overflow arm): early-return `0xFFFF_FFFFu32` → `return_`

Locals: `_0: u32` (return), `_1: u32` (bystander `k`), `_2: u32` (`accId := 2`),
`_3: u32` (`tmpId := 3`), `_4: (u16, bool)` (`ovfMulId := 4`), `_5: (u16, bool)` (`ovfAddId := 5`). -/
def ovfCastPipelineBody : CapturedMir :=
  mkBody "tests::ovf_cast_multi_diamond" 2
    [decl .mut u32T, decl .not u32T, decl .mut u32T, decl .mut u32T,
     decl .mut u16BoolT, decl .mut u16BoolT]
    [ -- bb0: narrow u32 -> u16
      mkBb [mkSt (.assign (pl 2) (.cast .intToInt (.copy (pl 2)) u16T))] (.goto 1)
    , -- bb1: checked mul by 3u16 + SwitchInt diamond
      mkBb [mkSt (.storageLive 4),
            mkSt (.assign (pl 4) (.binaryOp .mulWithOverflow (.copy (pl 2)) (u16C 3)))]
        (.switchInt (.copy (pl 4 [.field 1 boolT])) ⟨[(0, 2)], 7⟩)
    , -- bb2: extract wrapped product -> bb3
      mkBb [mkSt (.assign (pl 2) (.use (.copy (pl 4 [.field 0 u16T]))))] (.goto 3)
    , -- bb3: checked add by 7u16 + SwitchInt diamond
      mkBb [mkSt (.storageLive 5),
            mkSt (.assign (pl 5) (.binaryOp .addWithOverflow (.copy (pl 2)) (u16C 7)))]
        (.switchInt (.copy (pl 5 [.field 1 boolT])) ⟨[(0, 4)], 7⟩)
    , -- bb4: extract wrapped sum -> bb5
      mkBb [mkSt (.assign (pl 2) (.use (.copy (pl 5 [.field 0 u16T]))))] (.goto 5)
    , -- bb5: widen u16 -> u32
      mkBb [mkSt (.assign (pl 2) (.cast .intToInt (.copy (pl 2)) u32T))] (.goto 6)
    , -- bb6: interval-guarded addUnchecked +100u32 -> return_
      mkBb [mkSt (.storageLive 0),
            mkSt (.assign (pl 2) (.binaryOp .addUnchecked (.copy (pl 2)) (u32C 100))),
            mkSt (.assign (pl 0) (.use (.copy (pl 2))))] .return_
    , -- bb7: overflow early-return 0xFFFF_FFFFu32
      mkBb [mkSt (.assign (pl 0) (.use (u32C 0xFFFFFFFF)))] .return_ ]

private def ovfPipelineIds : StageLocalIds :=
  { accId := 2, tmpId := 3, ovfMulId := 4, ovfAddId := 5 }

private def ovfEarlyOk : MirOutcome → Bool
  | .normal (.scalar ⟨bits, 4⟩, _) => Nat.beq bits 0xFFFFFFFF
  | _ => false

private theorem frame_6_locals {baseLocals : List LocalSlot}
    {l0 l1 l2 l3 l4 l5 l2' l4' l5' : LocalSlot}
    (hFrame : ∀ j : Nat, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 →
      ParametricCore.listGet? [l0, l1, l2, l3, l4, l5] j = ParametricCore.listGet? baseLocals j) :
    ∀ j : Nat, j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 →
      ParametricCore.listGet? [l0, l1, l2', l3, l4', l5'] j = ParametricCore.listGet? baseLocals j := by
  intro j hj2 hj3 hj4 hj5
  have hF := hFrame j hj2 hj3 hj4 hj5
  cases j with
  | zero => exact hF
  | succ j1 =>
    cases j1 with
    | zero => exact hF
    | succ j2 =>
      cases j2 with
      | zero => exact False.elim (hj2 rfl)
      | succ j3 =>
        cases j3 with
        | zero => exact False.elim (hj3 rfl)
        | succ j4 =>
          cases j4 with
          | zero => exact False.elim (hj4 rfl)
          | succ j5 =>
            cases j5 with
            | zero => exact False.elim (hj5 rfl)
            | succ _ => exact hF

private abbrev ovfWpOps : MirWpOps MachineState MirOutcome Unit :=
  MirWpOps.ofDetStep (mirDetStep ovfCastPipelineBody)
    (fun st => some (v2026PureSlotOvfCastFrameOps.blockOf st))

private theorem ovfStep
    {stop : MachineState → Prop} {onDone : MirOutcome → Prop} {onFault : Unit → Prop}
    {n : Nat} {s s' : MachineState}
    (hStep : Anneal.PureMirExec.mirStep ovfCastPipelineBody s = .cont s')
    (hNext : wpUntilFuel (ops := ovfWpOps) stop onDone onFault n s') :
    wpUntilFuel (ops := ovfWpOps) stop onDone onFault (n + 1) s := by
  apply wpUntilFuel_step (ops := ovfWpOps)
  change (mirDetStep ovfCastPipelineBody s).wp _ _ _
  unfold mirDetStep toStepOutcome
  rw [hStep]
  exact hNext

private theorem ovf_step_bb0_0 (l0 l1 l3 l4 l5 : LocalSlot) (acc : Nat) (hLt : acc < 65536)
    (mem : Memory) (hAct : mem.activeCallee = none) (hBor : mem.borrows = [])
    (hStk : mem.callStack = []) :
    Anneal.PureMirExec.mirStep ovfCastPipelineBody
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [l0, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
        memory := mem } =
      .cont { frame := { blockIdx := 0, stmtIdx := 1
                         locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, l5] }
              memory := mem } := by
  cases mem with
  | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
    dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
    let m' : Memory :=
      { nextAllocId := na, globals := gl, borrows := [], nextTag := nt, callees := ca,
        traitImpls := ti, callStack := [], activeCallee := none, activeProtectors := ap,
        nextProtector := np, callerLocals := cl, fnPtrs := fp, exposedAllocIds := ex }
    have hW := wrapScalarBits_of_lt hLt
    cases ap with
    | nil =>
      change Step.cont
        ({ frame := { blockIdx := 0, stmtIdx := 1
                      locals := [l0, l1, .init (.scalar ⟨wrapScalarBits acc 65536, 2⟩), l3, l4, l5] }
           memory := { m' with activeProtectors := [] } } : MachineState) = _
      rw [hW]
    | cons hd tl =>
      change Step.cont
        ({ frame := { blockIdx := 0, stmtIdx := 1
                      locals := [l0, l1, .init (.scalar ⟨wrapScalarBits acc 65536, 2⟩), l3, l4, l5] }
           memory := { m' with activeProtectors := hd :: tl } } : MachineState) = _
      rw [hW]

private theorem ovf_step_bb1_1 (l0 l1 l3 l5 : LocalSlot) (acc : Nat) (hLt : acc * 3 < 65536)
    (mem : Memory) (hAct : mem.activeCallee = none) (hBor : mem.borrows = [])
    (hStk : mem.callStack = []) :
    Anneal.PureMirExec.mirStep ovfCastPipelineBody
      { frame := { blockIdx := 1, stmtIdx := 1
                   locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .uninit, l5] }
        memory := mem } =
      .cont { frame := { blockIdx := 1, stmtIdx := 2
                         locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3,
                                    .init (.aggregate 0 [.scalar ⟨acc * 3, 2⟩, .scalar ⟨0, 1⟩]), l5] }
              memory := mem } := by
  cases mem with
  | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
    dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
    let m' : Memory :=
      { nextAllocId := na, globals := gl, borrows := [], nextTag := nt, callees := ca,
        traitImpls := ti, callStack := [], activeCallee := none, activeProtectors := ap,
        nextProtector := np, callerLocals := cl, fnPtrs := fp, exposedAllocIds := ex }
    have hBle : Nat.ble 65536 (acc * 3) = false := nat_ble_false_of_lt hLt
    have hEv :
        evalRvalue [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .uninit, l5]
          (.binaryOp .mulWithOverflow (.copy (pl 2)) (u16C 3)) m'
          ovfCastPipelineBody.localDecls ovfCastPipelineBody.layouts =
        .ok (.aggregate 0 [.scalar ⟨acc * 3, 2⟩, .scalar ⟨0, 1⟩])
          [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .uninit, l5] m' := by
      change evalScalarBinOp .mulWithOverflow ⟨acc, 2⟩ ⟨3, 2⟩ _ _ false = _
      rw [evalScalarBinOp_mulWithOverflow_unsigned_eq .u16]
      have hMulEq : mulWithOverflowU .u16 acc 3 = (acc * 3, false) := by
        unfold mulWithOverflowU
        change ((acc * 3) % 65536, Nat.ble 65536 (acc * 3)) = (acc * 3, false)
        rw [Nat.mod_eq_of_lt hLt, hBle]
      rw [hMulEq]
      rfl
    unfold Anneal.PureMirExec.mirStep stepMirFn
    change (match evalStmt
        { frame := { blockIdx := 1, stmtIdx := 1
                     locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .uninit, l5] }
          memory := m' }
        (mkSt (.assign (pl 4) (.binaryOp .mulWithOverflow (.copy (pl 2)) (u16C 3))))
        ovfCastPipelineBody.localDecls ovfCastPipelineBody.layouts with
      | .tau (.running s') => Step.cont s'
      | .vis (.inr (.inl (.emit _))) k => match k PUnit.unit with | .running s' => Step.cont s' | _ => Step.fault
      | .ret out => Step.done out
      | _ => Step.fault) = _
    dsimp only [evalStmt, mkSt]
    rw [hEv]
    cases ap <;> rfl

private theorem ovf_step_bb3_1 (l0 l1 l3 l4 : LocalSlot) (acc : Nat) (hLt : acc + 7 < 65536)
    (mem : Memory) (hAct : mem.activeCallee = none) (hBor : mem.borrows = [])
    (hStk : mem.callStack = []) :
    Anneal.PureMirExec.mirStep ovfCastPipelineBody
      { frame := { blockIdx := 3, stmtIdx := 1
                   locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .uninit] }
        memory := mem } =
      .cont { frame := { blockIdx := 3, stmtIdx := 2
                         locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4,
                                    .init (.aggregate 0 [.scalar ⟨acc + 7, 2⟩, .scalar ⟨0, 1⟩])] }
              memory := mem } := by
  cases mem with
  | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
    dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
    let m' : Memory :=
      { nextAllocId := na, globals := gl, borrows := [], nextTag := nt, callees := ca,
        traitImpls := ti, callStack := [], activeCallee := none, activeProtectors := ap,
        nextProtector := np, callerLocals := cl, fnPtrs := fp, exposedAllocIds := ex }
    have hBle : Nat.ble 65536 (Nat.add acc 7) = false := nat_ble_false_of_lt hLt
    have hEv :
        evalRvalue [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .uninit]
          (.binaryOp .addWithOverflow (.copy (pl 2)) (u16C 7)) m'
          ovfCastPipelineBody.localDecls ovfCastPipelineBody.layouts =
        .ok (.aggregate 0 [.scalar ⟨acc + 7, 2⟩, .scalar ⟨0, 1⟩])
          [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .uninit] m' := by
      change evalScalarBinOp .addWithOverflow ⟨acc, 2⟩ ⟨7, 2⟩ _ _ false = _
      rw [evalScalarBinOp_addWithOverflow_unsigned_eq .u16]
      have hAddEq : addWithOverflowU .u16 acc 7 = (acc + 7, false) := by
        unfold addWithOverflowU
        change ((acc + 7) % 65536, Nat.ble 65536 (acc + 7)) = (acc + 7, false)
        rw [Nat.mod_eq_of_lt hLt, hBle]
      rw [hAddEq]
      rfl
    unfold Anneal.PureMirExec.mirStep stepMirFn
    change (match evalStmt
        { frame := { blockIdx := 3, stmtIdx := 1
                     locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .uninit] }
          memory := m' }
        (mkSt (.assign (pl 5) (.binaryOp .addWithOverflow (.copy (pl 2)) (u16C 7))))
        ovfCastPipelineBody.localDecls ovfCastPipelineBody.layouts with
      | .tau (.running s') => Step.cont s'
      | .vis (.inr (.inl (.emit _))) k => match k PUnit.unit with | .running s' => Step.cont s' | _ => Step.fault
      | .ret out => Step.done out
      | _ => Step.fault) = _
    dsimp only [evalStmt, mkSt]
    rw [hEv]
    cases ap <;> rfl

private theorem ovf_step_bb5_0 (l0 l1 l3 l4 l5 : LocalSlot) (acc : Nat) (hLt : acc < 4294967296)
    (mem : Memory) (hAct : mem.activeCallee = none) (hBor : mem.borrows = [])
    (hStk : mem.callStack = []) :
    Anneal.PureMirExec.mirStep ovfCastPipelineBody
      { frame := { blockIdx := 5, stmtIdx := 0
                   locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, l5] }
        memory := mem } =
      .cont { frame := { blockIdx := 5, stmtIdx := 1
                         locals := [l0, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
              memory := mem } := by
  cases mem with
  | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
    dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
    let m' : Memory :=
      { nextAllocId := na, globals := gl, borrows := [], nextTag := nt, callees := ca,
        traitImpls := ti, callStack := [], activeCallee := none, activeProtectors := ap,
        nextProtector := np, callerLocals := cl, fnPtrs := fp, exposedAllocIds := ex }
    have hW := wrapScalarBits_of_lt hLt
    cases ap with
    | nil =>
      change Step.cont
        ({ frame := { blockIdx := 5, stmtIdx := 1
                      locals := [l0, l1, .init (.scalar ⟨wrapScalarBits acc 4294967296, 4⟩), l3, l4, l5] }
           memory := { m' with activeProtectors := [] } } : MachineState) = _
      rw [hW]
    | cons hd tl =>
      change Step.cont
        ({ frame := { blockIdx := 5, stmtIdx := 1
                      locals := [l0, l1, .init (.scalar ⟨wrapScalarBits acc 4294967296, 4⟩), l3, l4, l5] }
           memory := { m' with activeProtectors := hd :: tl } } : MachineState) = _
      rw [hW]

private theorem ovf_step_bb6_1 (l1 l3 l4 l5 : LocalSlot) (acc : Nat) (hLt : acc + 100 < 4294967296)
    (mem : Memory) (hAct : mem.activeCallee = none) (hBor : mem.borrows = [])
    (hStk : mem.callStack = []) :
    Anneal.PureMirExec.mirStep ovfCastPipelineBody
      { frame := { blockIdx := 6, stmtIdx := 1
                   locals := [.uninit, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
        memory := mem } =
      .cont { frame := { blockIdx := 6, stmtIdx := 2
                         locals := [.uninit, l1, .init (.scalar ⟨acc + 100, 4⟩), l3, l4, l5] }
              memory := mem } := by
  cases mem with
  | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
    dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
    let m' : Memory :=
      { nextAllocId := na, globals := gl, borrows := [], nextTag := nt, callees := ca,
        traitImpls := ti, callStack := [], activeCallee := none, activeProtectors := ap,
        nextProtector := np, callerLocals := cl, fnPtrs := fp, exposedAllocIds := ex }
    have hBle : Nat.ble 4294967296 (Nat.add acc 100) = false := nat_ble_false_of_lt hLt
    have hEv :
        evalRvalue [.uninit, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5]
          (.binaryOp .addUnchecked (.copy (pl 2)) (u32C 100)) m'
          ovfCastPipelineBody.localDecls ovfCastPipelineBody.layouts =
        .ok (.scalar ⟨acc + 100, 4⟩)
          [.uninit, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] m' := by
      change evalScalarBinOp .addUnchecked ⟨acc, 4⟩ ⟨100, 4⟩ _ _ false = _
      rw [evalScalarBinOp_addUnchecked_unsigned_eq .u32]
      have hUnchEq : addUncheckedU .u32 acc 100 = some (acc + 100) := by
        unfold addUncheckedU addWithOverflowU
        change (match Nat.ble 4294967296 (acc + 100) with
          | true => none | false => some ((acc + 100) % 4294967296)) = some (acc + 100)
        rw [hBle, Nat.mod_eq_of_lt hLt]
      rw [hUnchEq]
    unfold Anneal.PureMirExec.mirStep stepMirFn
    change (match evalStmt
        { frame := { blockIdx := 6, stmtIdx := 1
                     locals := [.uninit, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
          memory := m' }
        (mkSt (.assign (pl 2) (.binaryOp .addUnchecked (.copy (pl 2)) (u32C 100))))
        ovfCastPipelineBody.localDecls ovfCastPipelineBody.layouts with
      | .tau (.running s') => Step.cont s'
      | .vis (.inr (.inl (.emit _))) k => match k PUnit.unit with | .running s' => Step.cont s' | _ => Step.fault
      | .ret out => Step.done out
      | _ => Step.fault) = _
    dsimp only [evalStmt, mkSt]
    rw [hEv]
    cases ap <;> rfl

/-- Stage 1 `OvfCastStageCut` (`bb0 -> bb1`): narrowing `u32 [lo, hi] → u16 [lo, hi]`. -/
private theorem ovfStage1_narrow_cut (baseLocals : List LocalSlot) (hLen : baseLocals.length = 6)
    (lo hi : Nat) (hHi : hi ≤ 20000) :
    OvfCastStageCut v2026PureSlotOvfCastFrameOps (mirDetStep ovfCastPipelineBody)
      baseLocals ovfPipelineIds (fun _ => false) ⟨0, .u32, lo, hi⟩ ⟨1, .u16, lo, hi⟩ 2 := by
  apply seal_ovfCastStageCut
  intro ms ⟨hBlk, hLocLen, ⟨acc, hGetAcc, hLo, hHiA, _⟩, hFrame⟩
  obtain ⟨hBb, hStmt, hAct, hBor, hStk⟩ := v2026PureSlot_blockOf_unpack (by dsimp; decide) hBlk
  cases ms with
  | mk fr mem =>
    cases fr with
    | mk bb st locs =>
      dsimp only [v2026PureSlotOvfCastFrameOps] at hLocLen hGetAcc hFrame
      dsimp only at hBb hStmt hAct hBor hStk hLo hHiA
      subst hBb; subst hStmt
      rw [hLen] at hLocLen
      cases locs with | nil => nomatch hLocLen | cons l0 r1 =>
      cases r1 with | nil => nomatch hLocLen | cons l1 r2 =>
      cases r2 with | nil => nomatch hLocLen | cons l2 r3 =>
      cases r3 with | nil => nomatch hLocLen | cons l3 r4 =>
      cases r4 with | nil => nomatch hLocLen | cons l4 r5 =>
      cases r5 with | nil => nomatch hLocLen | cons l5 r6 =>
      cases r6 with | cons _ _ => nomatch hLocLen | nil =>
      injection hGetAcc with hL2; subst hL2
      have hStep1 := ovf_step_bb0_0 l0 l1 l3 l4 l5 acc (by omega) mem hAct hBor hStk
      have hStep2 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 0, stmtIdx := 1
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 1, stmtIdx := 0
                             locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, l5] }
                  memory := mem } := by
        cases mem; dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk; rfl
      exact ovfStep hStep1 (ovfStep hStep2 (wpUntilFuel_here (ops := ovfWpOps)
        ⟨by unfold v2026PureSlotOvfCastFrameOps; simp [hAct, hBor, hStk],
         by rw [hLen]; rfl, ⟨acc, rfl, hLo, hHiA, by show hi < 65536; omega⟩,
         frame_6_locals hFrame⟩))

/-- Stage 2 `OvfCastStageCut` (`bb1 -> bb3`): checked multiplication diamond
`u16 [lo, hi] → u16 [lo * 3, hi * 3]`. -/
private theorem ovfStage2_mul_diamond_cut (baseLocals : List LocalSlot) (hLen : baseLocals.length = 6)
    (lo hi : Nat) (hHi : hi ≤ 20000) :
    OvfCastStageCut v2026PureSlotOvfCastFrameOps (mirDetStep ovfCastPipelineBody)
      baseLocals ovfPipelineIds (fun _ => false) ⟨1, .u16, lo, hi⟩ ⟨3, .u16, lo * 3, hi * 3⟩ 5 := by
  apply seal_ovfCastStageCut
  intro ms ⟨hBlk, hLocLen, ⟨acc, hGetAcc, hLo, hHiA, _⟩, hFrame⟩
  obtain ⟨hBb, hStmt, hAct, hBor, hStk⟩ := v2026PureSlot_blockOf_unpack (by dsimp; decide) hBlk
  cases ms with
  | mk fr mem =>
    cases fr with
    | mk bb st locs =>
      dsimp only [v2026PureSlotOvfCastFrameOps] at hLocLen hGetAcc hFrame
      dsimp only at hBb hStmt hAct hBor hStk hLo hHiA
      subst hBb; subst hStmt
      rw [hLen] at hLocLen
      cases locs with | nil => nomatch hLocLen | cons l0 r1 =>
      cases r1 with | nil => nomatch hLocLen | cons l1 r2 =>
      cases r2 with | nil => nomatch hLocLen | cons l2 r3 =>
      cases r3 with | nil => nomatch hLocLen | cons l3 r4 =>
      cases r4 with | nil => nomatch hLocLen | cons l4 r5 =>
      cases r5 with | nil => nomatch hLocLen | cons l5 r6 =>
      cases r6 with | cons _ _ => nomatch hLocLen | nil =>
      injection hGetAcc with hL2; subst hL2
      let mulTuple : Value := .aggregate 0 [.scalar ⟨acc * 3, 2⟩, .scalar ⟨0, 1⟩]
      have hStep0 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 1, stmtIdx := 0
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 1, stmtIdx := 1
                             locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .uninit, l5] }
                  memory := mem } := by
        cases mem with
        | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
          dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
          cases ap <;> rfl
      have hStep1 := ovf_step_bb1_1 l0 l1 l3 l5 acc (by omega) mem hAct hBor hStk
      have hStep2 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 1, stmtIdx := 2
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .init mulTuple, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 2, stmtIdx := 0
                             locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .init mulTuple, l5] }
                  memory := mem } := by
        cases mem; dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk; rfl
      have hStep3 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 2, stmtIdx := 0
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, .init mulTuple, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 2, stmtIdx := 1
                             locals := [l0, l1, .init (.scalar ⟨acc * 3, 2⟩), l3, .init mulTuple, l5] }
                  memory := mem } := by
        cases mem with
        | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
          dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
          cases ap <;> rfl
      have hStep4 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 2, stmtIdx := 1
                       locals := [l0, l1, .init (.scalar ⟨acc * 3, 2⟩), l3, .init mulTuple, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 3, stmtIdx := 0
                             locals := [l0, l1, .init (.scalar ⟨acc * 3, 2⟩), l3, .init mulTuple, l5] }
                  memory := mem } := by
        cases mem; dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk; rfl
      exact ovfStep hStep0 (ovfStep hStep1 (ovfStep hStep2 (ovfStep hStep3 (ovfStep hStep4
        (wpUntilFuel_here (ops := ovfWpOps)
          ⟨by unfold v2026PureSlotOvfCastFrameOps; simp [hAct, hBor, hStk],
           by rw [hLen]; rfl,
           ⟨acc * 3, rfl, by dsimp; omega, by dsimp; omega, by show hi * 3 < 65536; omega⟩,
           frame_6_locals hFrame⟩)))))

/-- Stage 3 `OvfCastStageCut` (`bb3 -> bb5`): checked addition diamond
`u16 [lo * 3, hi * 3] → u16 [lo * 3 + 7, hi * 3 + 7]`. -/
private theorem ovfStage3_add_diamond_cut (baseLocals : List LocalSlot) (hLen : baseLocals.length = 6)
    (lo hi : Nat) (hHi : hi ≤ 20000) :
    OvfCastStageCut v2026PureSlotOvfCastFrameOps (mirDetStep ovfCastPipelineBody)
      baseLocals ovfPipelineIds (fun _ => false)
      ⟨3, .u16, lo * 3, hi * 3⟩ ⟨5, .u16, lo * 3 + 7, hi * 3 + 7⟩ 5 := by
  apply seal_ovfCastStageCut
  intro ms ⟨hBlk, hLocLen, ⟨acc, hGetAcc, hLo, hHiA, _⟩, hFrame⟩
  obtain ⟨hBb, hStmt, hAct, hBor, hStk⟩ := v2026PureSlot_blockOf_unpack (by dsimp; decide) hBlk
  cases ms with
  | mk fr mem =>
    cases fr with
    | mk bb st locs =>
      dsimp only [v2026PureSlotOvfCastFrameOps] at hLocLen hGetAcc hFrame
      dsimp only at hBb hStmt hAct hBor hStk hLo hHiA
      subst hBb; subst hStmt
      rw [hLen] at hLocLen
      cases locs with | nil => nomatch hLocLen | cons l0 r1 =>
      cases r1 with | nil => nomatch hLocLen | cons l1 r2 =>
      cases r2 with | nil => nomatch hLocLen | cons l2 r3 =>
      cases r3 with | nil => nomatch hLocLen | cons l3 r4 =>
      cases r4 with | nil => nomatch hLocLen | cons l4 r5 =>
      cases r5 with | nil => nomatch hLocLen | cons l5 r6 =>
      cases r6 with | cons _ _ => nomatch hLocLen | nil =>
      injection hGetAcc with hL2; subst hL2
      let addTuple : Value := .aggregate 0 [.scalar ⟨acc + 7, 2⟩, .scalar ⟨0, 1⟩]
      have hStep0 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 3, stmtIdx := 0
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 3, stmtIdx := 1
                             locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .uninit] }
                  memory := mem } := by
        cases mem with
        | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
          dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
          cases ap <;> rfl
      have hStep1 := ovf_step_bb3_1 l0 l1 l3 l4 acc (by omega) mem hAct hBor hStk
      have hStep2 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 3, stmtIdx := 2
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .init addTuple] }
            memory := mem } =
          .cont { frame := { blockIdx := 4, stmtIdx := 0
                             locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .init addTuple] }
                  memory := mem } := by
        cases mem; dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk; rfl
      have hStep3 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 4, stmtIdx := 0
                       locals := [l0, l1, .init (.scalar ⟨acc, 2⟩), l3, l4, .init addTuple] }
            memory := mem } =
          .cont { frame := { blockIdx := 4, stmtIdx := 1
                             locals := [l0, l1, .init (.scalar ⟨acc + 7, 2⟩), l3, l4, .init addTuple] }
                  memory := mem } := by
        cases mem with
        | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
          dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
          cases ap <;> rfl
      have hStep4 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 4, stmtIdx := 1
                       locals := [l0, l1, .init (.scalar ⟨acc + 7, 2⟩), l3, l4, .init addTuple] }
            memory := mem } =
          .cont { frame := { blockIdx := 5, stmtIdx := 0
                             locals := [l0, l1, .init (.scalar ⟨acc + 7, 2⟩), l3, l4, .init addTuple] }
                  memory := mem } := by
        cases mem; dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk; rfl
      exact ovfStep hStep0 (ovfStep hStep1 (ovfStep hStep2 (ovfStep hStep3 (ovfStep hStep4
        (wpUntilFuel_here (ops := ovfWpOps)
          ⟨by unfold v2026PureSlotOvfCastFrameOps; simp [hAct, hBor, hStk],
           by rw [hLen]; rfl,
           ⟨acc + 7, rfl, by dsimp; omega, by dsimp; omega, by show hi * 3 + 7 < 65536; omega⟩,
           frame_6_locals hFrame⟩)))))

/-- Stage 4 `OvfCastStageCut` (`bb5 -> bb6`): widening `u16 [lo * 3 + 7, hi * 3 + 7] → u32`. -/
private theorem ovfStage4_widen_cut (baseLocals : List LocalSlot) (hLen : baseLocals.length = 6)
    (lo hi : Nat) (hHi : hi ≤ 20000) :
    OvfCastStageCut v2026PureSlotOvfCastFrameOps (mirDetStep ovfCastPipelineBody)
      baseLocals ovfPipelineIds (fun _ => false)
      ⟨5, .u16, lo * 3 + 7, hi * 3 + 7⟩ ⟨6, .u32, lo * 3 + 7, hi * 3 + 7⟩ 2 := by
  apply seal_ovfCastStageCut
  intro ms ⟨hBlk, hLocLen, ⟨acc, hGetAcc, hLo, hHiA, _⟩, hFrame⟩
  obtain ⟨hBb, hStmt, hAct, hBor, hStk⟩ := v2026PureSlot_blockOf_unpack (by dsimp; decide) hBlk
  cases ms with
  | mk fr mem =>
    cases fr with
    | mk bb st locs =>
      dsimp only [v2026PureSlotOvfCastFrameOps] at hLocLen hGetAcc hFrame
      dsimp only at hBb hStmt hAct hBor hStk hLo hHiA
      subst hBb; subst hStmt
      rw [hLen] at hLocLen
      cases locs with | nil => nomatch hLocLen | cons l0 r1 =>
      cases r1 with | nil => nomatch hLocLen | cons l1 r2 =>
      cases r2 with | nil => nomatch hLocLen | cons l2 r3 =>
      cases r3 with | nil => nomatch hLocLen | cons l3 r4 =>
      cases r4 with | nil => nomatch hLocLen | cons l4 r5 =>
      cases r5 with | nil => nomatch hLocLen | cons l5 r6 =>
      cases r6 with | cons _ _ => nomatch hLocLen | nil =>
      injection hGetAcc with hL2; subst hL2
      have hStep1 := ovf_step_bb5_0 l0 l1 l3 l4 l5 acc (by omega) mem hAct hBor hStk
      have hStep2 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
          { frame := { blockIdx := 5, stmtIdx := 1
                       locals := [l0, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
            memory := mem } =
          .cont { frame := { blockIdx := 6, stmtIdx := 0
                             locals := [l0, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
                  memory := mem } := by
        cases mem; dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk; rfl
      exact ovfStep hStep1 (ovfStep hStep2 (wpUntilFuel_here (ops := ovfWpOps)
        ⟨by unfold v2026PureSlotOvfCastFrameOps; simp [hAct, hBor, hStk],
         by rw [hLen]; rfl, ⟨acc, rfl, hLo, hHiA, by show hi * 3 + 7 < 4294967296; omega⟩,
         frame_6_locals hFrame⟩))

/-- Parametric $O(m)$ composed 4-stage `OvfCastStageCut` (`bb0 -> bb6`, total fuel `14`,
`earlyOk := fun _ => false`) collapsing both `SwitchInt` diamonds and both `intToInt`
casts into a single compositional cut for ANY interval `[lo, hi]` with `hi ≤ 20000`.
Instantiating `(0, 20000)` yields the wide interval cut `[0, 20000] → [7, 60007]`;
instantiating singleton `(x, x)` yields the EXACT functional cut `[x, x] → [3*x + 7, 3*x + 7]`. -/
theorem ovfPipeline_composed_cut (baseLocals : List LocalSlot) (hLen : baseLocals.length = 6)
    (lo hi : Nat) (hHi : hi ≤ 20000) :
    OvfCastStageCut v2026PureSlotOvfCastFrameOps (mirDetStep ovfCastPipelineBody)
      baseLocals ovfPipelineIds (fun _ => false)
      ⟨0, .u32, lo, hi⟩ ⟨6, .u32, lo * 3 + 7, hi * 3 + 7⟩ 14 :=
  ovfCastStageCut_compose
    (ovfCastStageCut_compose
      (ovfCastStageCut_compose
        (ovfStage1_narrow_cut baseLocals hLen lo hi hHi)
        (ovfStage2_mul_diamond_cut baseLocals hLen lo hi hHi))
      (ovfStage3_add_diamond_cut baseLocals hLen lo hi hHi))
    (ovfStage4_widen_cut baseLocals hLen lo hi hHi)

/-- **Witness 2 (`OverflowCastJoin` end-to-end $O(m)$ `OvfCastStageCut` composition →
`MirWpConverges`)**:
BOTH the wide interval postcondition (`107 ≤ r ∧ r ≤ 60107`, with NO early-return
escape hatch) AND the exact symbolic functional postcondition (`r = 3 * x + 107`)
are derived DIRECTLY through the SAME $O(m)$ composed `ovfPipeline_composed_cut` +
`mirWpConverges_of_ovfCastStageCut` (at `(0, 20000)` and singleton `(x, x)` respectively),
plus concrete witness `x = 1234 ↦ 3809`. -/
theorem witness2_ovfCast_multi_diamond_mir_wp_converges :
    (∀ (x k : Nat), x ≤ 20000 →
      let baseLocals : List LocalSlot :=
        [.uninit, .init (.scalar ⟨k, 4⟩), .init (.scalar ⟨x, 4⟩), .uninit, .uninit, .uninit]
      let ms0 : MachineState :=
        { frame := { blockIdx := 0, stmtIdx := 0, locals := baseLocals }, memory := {} }
      MirWpConverges ovfCastPipelineBody ms0
        (fun out =>
          match out with
          | .normal (.scalar ⟨r, 4⟩, _) => 107 ≤ r ∧ r ≤ 60107
          | _ => False) ∧
      MirWpConverges ovfCastPipelineBody ms0
        (fun out =>
          match out with
          | .normal (.scalar ⟨r, 4⟩, _) => r = 3 * x + 107 ∧ 107 ≤ r ∧ r ≤ 60107
          | _ => False)) ∧
    MirWpConverges ovfCastPipelineBody
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨42, 4⟩), .init (.scalar ⟨1234, 4⟩),
                              .uninit, .uninit, .uninit] }
        memory := {} }
      (fun out =>
        match out with
        | .normal (.scalar ⟨r, 4⟩, _) => r = 3809
        | _ => False) := by
  have hFromCut : ∀ (x k lo hi : Nat), lo ≤ x → x ≤ hi → hi ≤ 20000 →
      MirWpConverges ovfCastPipelineBody
        { frame := { blockIdx := 0, stmtIdx := 0
                     locals := [.uninit, .init (.scalar ⟨k, 4⟩), .init (.scalar ⟨x, 4⟩),
                                .uninit, .uninit, .uninit] }
          memory := {} }
        (fun out =>
          match out with
          | .normal (.scalar ⟨r, 4⟩, _) => lo * 3 + 107 ≤ r ∧ r ≤ hi * 3 + 107
          | _ => False) := by
    intro x k lo hi hLoX hXHi hHi
    let baseLocals : List LocalSlot :=
      [.uninit, .init (.scalar ⟨k, 4⟩), .init (.scalar ⟨x, 4⟩), .uninit, .uninit, .uninit]
    refine mirWpConverges_of_ovfCastStageCut (ovfPipeline_composed_cut baseLocals rfl lo hi hHi)
      ⟨rfl, rfl, ⟨x, rfl, hLoX, hXHi, by show hi < 4294967296; omega⟩, fun _ _ _ _ _ => rfl⟩
      ?_ (fun _ hF => by cases hF)
    intro ms' ⟨hBlk, hLocLen, ⟨acc, hGetAcc, hLo, hHiA, _⟩, _⟩
    obtain ⟨hBb, hStmt, hAct, hBor, hStk⟩ := v2026PureSlot_blockOf_unpack (by dsimp; decide) hBlk
    cases ms' with
    | mk fr mem =>
      cases fr with
      | mk bb st locs =>
        dsimp only [v2026PureSlotOvfCastFrameOps] at hLocLen hGetAcc
        dsimp only at hBb hStmt hAct hBor hStk hLo hHiA
        subst hBb; subst hStmt
        cases locs with | nil => nomatch hLocLen | cons l0 r1 =>
        cases r1 with | nil => nomatch hLocLen | cons l1 r2 =>
        cases r2 with | nil => nomatch hLocLen | cons l2 r3 =>
        cases r3 with | nil => nomatch hLocLen | cons l3 r4 =>
        cases r4 with | nil => nomatch hLocLen | cons l4 r5 =>
        cases r5 with | nil => nomatch hLocLen | cons l5 r6 =>
        cases r6 with | cons _ _ => nomatch hLocLen | nil =>
        injection hGetAcc with hL2; subst hL2
        have hT0 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
            { frame := { blockIdx := 6, stmtIdx := 0
                         locals := [l0, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
              memory := mem } =
            .cont { frame := { blockIdx := 6, stmtIdx := 1
                               locals := [.uninit, l1, .init (.scalar ⟨acc, 4⟩), l3, l4, l5] }
                    memory := mem } := by
          cases mem with
          | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
            dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
            cases ap <;> rfl
        have hT1 := ovf_step_bb6_1 l1 l3 l4 l5 acc (by omega) mem hAct hBor hStk
        have hT2 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
            { frame := { blockIdx := 6, stmtIdx := 2
                         locals := [.uninit, l1, .init (.scalar ⟨acc + 100, 4⟩), l3, l4, l5] }
              memory := mem } =
            .cont { frame := { blockIdx := 6, stmtIdx := 3
                               locals := [.init (.scalar ⟨acc + 100, 4⟩), l1,
                                          .init (.scalar ⟨acc + 100, 4⟩), l3, l4, l5] }
                    memory := mem } := by
          cases mem with
          | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
            dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
            cases ap <;> rfl
        have hT3 : Anneal.PureMirExec.mirStep ovfCastPipelineBody
            { frame := { blockIdx := 6, stmtIdx := 3
                         locals := [.init (.scalar ⟨acc + 100, 4⟩), l1,
                                    .init (.scalar ⟨acc + 100, 4⟩), l3, l4, l5] }
              memory := mem } =
            .done (.normal (.scalar ⟨acc + 100, 4⟩, mem)) := by
          cases mem with
          | mk na gl bo nt ca ti cs ac ap np cl fp ex =>
            dsimp only at hAct hBor hStk; subst hAct; subst hBor; subst hStk
            cases ap <;> rfl
        exact step_to_mirWp hT0 (step_to_mirWp hT1 (step_to_mirWp hT2
          (done_to_mirWp hT3 ⟨by omega, by omega⟩)))
  refine ⟨?_, ?_⟩
  · intro x k hx
    refine ⟨hFromCut x k 0 20000 (Nat.zero_le x) hx (Nat.le_refl _), ?_⟩
    exact MirWpConverges.mono (by
      intro out h
      cases out with
      | normal rv =>
        rcases rv with ⟨v, mem⟩
        cases v with
        | scalar sc =>
          rcases sc with ⟨bits, sz⟩
          by_cases h4 : sz = 4
          · subst h4
            change x * 3 + 107 ≤ bits ∧ bits ≤ x * 3 + 107 at h
            exact ⟨by omega, by omega, by omega⟩
          · match sz, h4 with
            | 4, hn => exact False.elim (hn rfl)
            | 0, _ | 1, _ | 2, _ | 3, _ | _ + 5, _ => exact False.elim h
        | unit | ptr _ _ | aggregate _ _ | uninit => cases h
      | panic | abort => cases h)
      (hFromCut x k x x (Nat.le_refl x) (Nat.le_refl x) hx)
  · exact MirWpConverges.mono (by
      intro out h
      cases out with
      | normal rv =>
        rcases rv with ⟨v, mem⟩
        cases v with
        | scalar sc =>
          rcases sc with ⟨bits, sz⟩
          by_cases h4 : sz = 4
          · subst h4
            change 1234 * 3 + 107 ≤ bits ∧ bits ≤ 1234 * 3 + 107 at h
            change bits = 3809
            omega
          · match sz, h4 with
            | 4, hn => exact False.elim (hn rfl)
            | 0, _ | 1, _ | 2, _ | 3, _ | _ + 5, _ => exact False.elim h
        | unit | ptr _ _ | aggregate _ _ | uninit => cases h
      | panic | abort => cases h)
      (hFromCut 1234 42 1234 1234 (by decide) (by decide) (by decide))

/-! ## Witness 3: `CallStackUnwind` & `RefFrame` — Inline Call, `CallSpecCut`, Cleanup Unwind & `topo3` -/

/-- Real inline callee `fn bump_mut(p: &mut u32) -> u32 { *p = *p + 5; 1 }`, opening
with the compiler-emitted function-entry `Retag(FnEntry, _1)` so that unmodified
`V2026_06_01.MirSemantics.evalFnEntryRetag` allocates a REAL strong protector
(`activeProtectors := protId :: _`, `nextProtector += 1`) and a protected child
tag (`perm := .reservedFrz false`, `protector := some protId`, `parentTag := some 1`). -/
def calleeBumpMutBody : CapturedMir :=
  mkBody "tests::bump_mut" 1
    [decl .mut u32T, decl .not refMutU32T]
    [mkBb
      [ mkSt (.retag .fnEntry (pl 1))
      , mkSt (.assign (pl 1 [.deref]) (.binaryOp .add (.copy (pl 1 [.deref])) (u32C 5)))
      , mkSt (.assign (pl 0) (.use (u32C 1))) ]
      .return_]

/-- Real caller `fn caller_normal(mut x: u32, bystander: u32) -> u32`:
creates `p := &mut x`, calls `bump_mut(p)` with `unwind = .cleanup 2`, and returns
`x + bystander + status` (`= x + bystander + 6`). -/
def callerNormalBody : CapturedMir :=
  mkBody "tests::caller_normal" 2
    [decl .mut u32T, decl .mut u32T, decl .not u32T, decl .mut refMutU32T,
     decl .mut u32T, decl .mut u32T]
    [ mkBb [mkSt (.assign (pl 3) (.ref (.mut false) (pl 1)))]
        (.call (fnOp "tests::bump_mut") [.copy (pl 3)] (pl 4) (some 1) (.cleanup 2))
    , mkBb
        [ mkSt (.assign (pl 5) (.binaryOp .add (.copy (pl 1)) (.copy (pl 2))))
        , mkSt (.assign (pl 0) (.binaryOp .add (.copy (pl 5)) (.copy (pl 4)))) ]
        .return_
    , mkBb [mkSt (.assign (pl 0) (.use (u32C 999)))] .return_ (isClean := true) ]

/-- Real `&mut [u8]` slice-writing callee `fn write2(buf: &mut [u8], b0: u8, b1: u8) -> u32`:
opens with `Retag(FnEntry, _1)` creating a REAL strong protector (`activeProtectors = [1]`,
protected child tag `2`), writes `[b0, b1]` into the caller's `[u8; N]` buffer in
`Memory.callerLocals`, and returns `1u32`. -/
def calleeWrite2BytesBody : CapturedMir :=
  mkBody "tests::write2_bytes" 3
    [decl .mut u32T, decl .not refMutSliceU8T, decl .not u8T, decl .not u8T]
    [mkBb
      [ mkSt (.retag .fnEntry (pl 1))
      , mkSt (.assign (pl 1 [.deref]) (.aggregate (.array u8T) [.copy (pl 2), .copy (pl 3)]))
      , mkSt (.assign (pl 0) (.use (u32C 1))) ]
      .return_]

/-- Real inline slice-prefix writer `fn write_prefix(buf: &mut [u8], b0: u8, b1: u8) -> u32`:
opens with `Retag(FnEntry, _1)`, writes `(*buf)[0] := b0` and `(*buf)[1] := b1` via
`ProjectionElem.constantIndex`, leaving indices `[2..4)` untouched, and returns `2u32`. -/
def calleeWriteSlicePrefixBody : CapturedMir :=
  mkBody "tests::write_slice_prefix" 3
    [decl .mut u32T, decl .not refMutSliceU8T, decl .not u8T, decl .not u8T]
    [mkBb
      [ mkSt (.retag .fnEntry (pl 1))
      , mkSt (.assign (pl 1 [.deref, .constantIndex 0 2 false]) (.use (.copy (pl 2))))
      , mkSt (.assign (pl 1 [.deref, .constantIndex 1 2 false]) (.use (.copy (pl 3))))
      , mkSt (.assign (pl 0) (.use (u32C 2))) ]
      .return_]

/-- Real caller `fn caller_slice_write(mut arr: [u8; 4], b0: u8, b1: u8) -> [u8; 4]`:
creates a REAL mutable borrow `&mut arr` via `Rvalue.ref (.mut false)`, unsizes
`&mut [u8; 4] → &mut [u8]` via `CastKind.pointerCoercion "Unsize"`, invokes
`tests::write_slice_prefix` via `TerminatorKind.call`, and returns the updated `[u8; 4]`. -/
def callerSliceWriteBody : CapturedMir :=
  mkBody "tests::caller_slice_write" 3
    [decl .mut u8Arr4T, decl .mut u8Arr4T, decl .not u8T, decl .not u8T,
     decl .mut refMutU8Arr4T, decl .mut refMutSliceU8T, decl .mut u32T]
    [ mkBb
        [ mkSt (.assign (pl 4) (.ref (.mut false) (pl 1)))
        , mkSt (.assign (pl 5) (.cast (.pointerCoercion "Unsize") (.copy (pl 4)) refMutSliceU8T)) ]
        (.call (fnOp "tests::write_slice_prefix")
          [.copy (pl 5), .copy (pl 2), .copy (pl 3)] (pl 6) (some 1) (.cleanup 2))
    , mkBb [mkSt (.assign (pl 0) (.use (.copy (pl 1))))] .return_
    , mkBb [mkSt (.assign (pl 0) (.use (.copy (pl 1))))] .return_ (isClean := true) ]

/-- Real inline callee `fn assert_flag(flag: bool) -> u32 { assert!(flag); 0 }`
unwinding with `UnwindAction.continue_`. -/
def calleeAssertBody : CapturedMir :=
  mkBody "tests::assert_flag" 1
    [decl .mut u32T, decl .not boolT]
    [ mkBb [] (.assert (.copy (pl 1)) true 1 .continue_)
    , mkBb [mkSt (.assign (pl 0) (.use (u32C 0)))] .return_ ]

/-- Real caller `fn caller_cleanup(flag: bool) -> u32`: calls `assert_flag(flag)` with
`UnwindAction.cleanup 2`; when `flag = false`, unwinds into cleanup landing pad `bb2`
(`isCleanup = true`) which recovers cleanly returning `999u32`. -/
def callerCleanupBody : CapturedMir :=
  mkBody "tests::caller_cleanup" 1
    [decl .mut u32T, decl .not boolT, decl .mut u32T]
    [ mkBb [] (.call (fnOp "tests::assert_flag") [.copy (pl 1)] (pl 2) (some 1) (.cleanup 2))
    , mkBb [mkSt (.assign (pl 0) (.use (.copy (pl 2))))] .return_
    , mkBb [mkSt (.assign (pl 0) (.use (u32C 999)))] .return_ (isClean := true) ]

/-- **Witness 3a-i (`CallStackUnwind` normal inline call + `&mut` writeback + REAL
protector lifecycle + framing)**: for ALL `x ≤ 10000`, `bystander ≤ 10000`,
`callerNormalBody` invokes `calleeBumpMutBody` through `Memory.callees`; the callee's
`Retag(FnEntry, _1)` pushes strong protector `1` (`activeProtectors = [1]`) on a
protected child tag `2` of the caller's `&mut x` tag `1`, writes `*p = x + 5` through
tag `2` (both tags become `.unique`), and `TerminatorKind.return_` RELEASES the
protector (`restoreCallerProtectors` → `activeProtectors = []`, `nextProtector = 2`
witnessing that exactly one protector was allocated and released), frames
`bystander`, and converges via `MirWpConverges` to `x + bystander + 6`. -/
theorem witness3a_inline_call_mut_writeback_and_frame (x bystander : Nat)
    (hx : x ≤ 10000) (hb : bystander ≤ 10000) :
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                              .uninit, .uninit, .uninit] }
        memory := { callees := [calleeBumpMutBody] } }
    MirWpConverges callerNormalBody ms0
      (fun out =>
        match out with
        | .normal (.scalar ⟨r, 4⟩, mem) =>
          r = x + bystander + 6 ∧ mem.callStack = [] ∧ mem.activeProtectors = [] ∧
          mem.nextProtector = 2 ∧
          mem.borrows.map BorrowEntry.protector = [some 1, none] ∧
          mem.borrows.map BorrowEntry.parentTag = [some 1, none]
        | _ => False) := by
  intro ms0
  have hW1 : wrapScalarBits (Nat.add x 5) 4294967296 = x + 5 :=
    wrapScalarBits_of_lt (show x + 5 < 4294967296 by omega)
  have hW2 : wrapScalarBits (Nat.add (x + 5) bystander) 4294967296 = x + 5 + bystander :=
    wrapScalarBits_of_lt (show x + 5 + bystander < 4294967296 by omega)
  have hW3 : wrapScalarBits (Nat.add (x + 5 + bystander) 1) 4294967296 = x + 5 + bystander + 1 :=
    wrapScalarBits_of_lt (show x + 5 + bystander + 1 < 4294967296 by omega)
  let borrow1 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
      perm := .reservedFrz false }
  let child2 : BorrowEntry :=
    { tag := 2, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
      perm := .reservedFrz false, protector := some 1, parentTag := some 1 }
  let mem1 : Memory := { callees := [calleeBumpMutBody], borrows := [borrow1], nextTag := 2 }
  let savedCaller0 : SavedCallerFrame :=
    { callerBody := callerNormalBody
      frame := { blockIdx := 0, stmtIdx := 1
                 locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
      destination := pl 4
      returnTarget := 1
      calleeProtectors := []
      returnUnwind := .cleanup 2
      isDiverging := false }
  let savedCaller1 : SavedCallerFrame :=
    { savedCaller0 with
      frame := { blockIdx := 0, stmtIdx := 1
                 locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] } }
  let mem2 : Memory :=
    { mem1 with callStack := [savedCaller0], activeCallee := some calleeBumpMutBody }
  let mem3 : Memory :=
    { mem2 with borrows := [child2, borrow1], nextTag := 3, activeProtectors := [1],
                nextProtector := 2 }
  let mem4 : Memory :=
    { mem3 with borrows := [{ child2 with perm := .unique }, { borrow1 with perm := .unique }],
                callStack := [savedCaller1] }
  let mem5 : Memory :=
    { callees := [calleeBumpMutBody],
      borrows := [{ child2 with perm := .unique }, { borrow1 with perm := .unique }],
      nextTag := 3, nextProtector := 2, activeCallee := some callerNormalBody }
  have h1 : Anneal.PureMirExec.mirStep callerNormalBody ms0 =
      .cont { frame := { blockIdx := 0, stmtIdx := 1
                         locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                                    .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
              memory := mem1 } := rfl
  have h2 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 0, stmtIdx := 1
                   locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                              .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
        memory := mem1 } =
      .cont { frame := { blockIdx := 0, stmtIdx := 0
                         locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8)] }
              memory := mem2 } := rfl
  have h3 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8)] }
        memory := mem2 } =
      .cont { frame := { blockIdx := 0, stmtIdx := 1
                         locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
              memory := mem3 } := rfl
  have h4 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 0, stmtIdx := 1
                   locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
        memory := mem3 } =
      .cont { frame := { blockIdx := 0, stmtIdx := 2
                         locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
              memory := mem4 } := by
    change Step.cont
      ({ frame := { blockIdx := 0, stmtIdx := 2
                    locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
         memory :=
           { mem3 with
             borrows := [{ child2 with perm := .unique }, { borrow1 with perm := .unique }]
             callStack :=
               [{ savedCaller0 with
                  frame := { blockIdx := 0, stmtIdx := 1
                             locals := [.uninit,
                                        .init (.scalar ⟨wrapScalarBits (Nat.add x 5) 4294967296, 4⟩),
                                        .init (.scalar ⟨bystander, 4⟩),
                                        .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] } }] } } : MachineState) = _
    rw [hW1]
  have h5 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 0, stmtIdx := 2
                   locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
        memory := mem4 } =
      .cont { frame := { blockIdx := 0, stmtIdx := 3
                         locals := [.init (.scalar ⟨1, 4⟩), .init (.ptr ⟨2, 0⟩ 8)] }
              memory := mem4 } := rfl
  have h6 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 0, stmtIdx := 3
                   locals := [.init (.scalar ⟨1, 4⟩), .init (.ptr ⟨2, 0⟩ 8)] }
        memory := mem4 } =
      .cont { frame := { blockIdx := 1, stmtIdx := 0
                         locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                                    .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩), .uninit] }
              memory := mem5 } := rfl
  have h7 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 1, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                              .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩), .uninit] }
        memory := mem5 } =
      .cont { frame := { blockIdx := 1, stmtIdx := 1
                         locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                                    .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩),
                                    .init (.scalar ⟨x + 5 + bystander, 4⟩)] }
              memory := mem5 } := by
    change Step.cont
      ({ frame := { blockIdx := 1, stmtIdx := 1
                    locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                               .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩),
                               .init (.scalar ⟨wrapScalarBits (Nat.add (x + 5) bystander) 4294967296, 4⟩)] }
         memory := mem5 } : MachineState) = _
    rw [hW2]
  have h8 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 1, stmtIdx := 1
                   locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                              .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩),
                              .init (.scalar ⟨x + 5 + bystander, 4⟩)] }
        memory := mem5 } =
      .cont { frame := { blockIdx := 1, stmtIdx := 2
                         locals := [.init (.scalar ⟨x + 5 + bystander + 1, 4⟩),
                                    .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                                    .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩),
                                    .init (.scalar ⟨x + 5 + bystander, 4⟩)] }
              memory := mem5 } := by
    change Step.cont
      ({ frame := { blockIdx := 1, stmtIdx := 2
                    locals := [.init (.scalar ⟨wrapScalarBits (Nat.add (x + 5 + bystander) 1) 4294967296, 4⟩),
                               .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                               .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩),
                               .init (.scalar ⟨x + 5 + bystander, 4⟩)] }
         memory := mem5 } : MachineState) = _
    rw [hW3]
  have h9 : Anneal.PureMirExec.mirStep callerNormalBody
      { frame := { blockIdx := 1, stmtIdx := 2
                   locals := [.init (.scalar ⟨x + 5 + bystander + 1, 4⟩),
                              .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                              .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩),
                              .init (.scalar ⟨x + 5 + bystander, 4⟩)] }
        memory := mem5 } =
      .done (.normal (.scalar ⟨x + 5 + bystander + 1, 4⟩,
        { mem5 with borrows := disableFrameBorrows mem5.borrows 0 6 })) := rfl
  exact step_to_mirWp h1 (step_to_mirWp h2 (step_to_mirWp h3 (step_to_mirWp h4
    (step_to_mirWp h5 (step_to_mirWp h6 (step_to_mirWp h7 (step_to_mirWp h8
      (done_to_mirWp h9 ⟨by omega, rfl, rfl, rfl, rfl, rfl⟩))))))))

/-- **Witness 3a-ii (`CallSpecCut` `&mut [u8]` slice writeback + lossless orthogonal
`(callerLocals, RangedBorrowTree)` adapter + `exitFrameWithProtectors` + disjoint sibling
framing → `MirWpConverges`)**: seals `calleeWrite2BytesBody` (with REAL `Retag(FnEntry, _1)`)
behind a `CallSpecCut` whose byte store is `List LocalSlot` (`callerLocalsByteStoreOps`)
and whose borrow/protector state lives in `RangedBorrowTree`:
- `adapter.mkEntry cl t` reconstructs `Memory` faithfully from BOTH `cl` (`callerLocals`)
  and `t` (`mirBorrowsOfRangedTree t 0 12 0 2`, `activeProtectors := t.protectedTags`,
  `nextTag := maxTag(t) + 1`), with ZERO hardcoded borrow lists or overwritten fields;
- `adapter.classifyOut` projects `.normal (rv, m1)` losslessly to
  `(m1.callerLocals, rangedBorrowTreeOfMirAlloc m1.borrows m1.activeProtectors 0 12 2)`;
- proves `UpdatesOnly [⟨⟨12⟩, 0, 2⟩]` on `callerLocals`, `exitFrameWithProtectors _ [1]`
  releasing the protector attached by the real fat-pointer `Retag(FnEntry)`, and
  disjoint sibling slice `[2..4)` framing via `mirWpConverges_of_callSpecCut_normal_cleanup`. -/
theorem witness3a_callSpecCut_slice_writeback_and_frame (b0 b1 : UInt8) (sib0 sib1 : UInt8) :
    let mutL : ByteSubLens CallerLocalAddr := ⟨⟨12⟩, 0, 2⟩
    let sibL : ByteSubLens CallerLocalAddr := ⟨⟨12⟩, 2, 2⟩
    let borrowSlice : BorrowEntry :=
      { tag := 1, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, rangeOffset := 0, rangeLen := 2 }
    let cl0 : List LocalSlot :=
      List.replicate 12 LocalSlot.uninit ++ [u8BytesToSlot [0, 0, sib0, sib1]]
    let tree0 : RangedBorrowTree := rangedBorrowTreeOfMirAlloc [borrowSlice] [] 0 12 2
    let adapter : CalleeMachineAdapter MachineState MirOutcome (List LocalSlot) Value :=
      { mkEntry := fun cl t =>
          { frame := { blockIdx := 0, stmtIdx := 0
                       locals := [.uninit,
                                  .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                  .init (.scalar ⟨b0.toNat, 1⟩),
                                  .init (.scalar ⟨b1.toNat, 1⟩)] }
            memory :=
              { borrows := mirBorrowsOfRangedTree t 0 12 (fun _ => (0, 2))
                activeProtectors := t.protectedTags
                nextTag := (t.topology.foldr (fun n acc => Nat.max n.tag acc) 0) + 1
                callerLocals := cl } }
        classifyOut := fun out =>
          match out with
          | .normal (rv, m1) =>
            some (.returned rv m1.callerLocals
              (rangedBorrowTreeOfMirAlloc m1.borrows m1.activeProtectors 0 12 2))
          | _ => none }
    let spec : CallSpec (List LocalSlot) CallerLocalAddr Value :=
      { pre := fun cl t => cl = cl0 ∧ t = tree0
        postRet := fun rv cl tRel =>
          rv = .scalar ⟨1, 4⟩ ∧ mutL.get cl = some [b0, b1] ∧
          sibL.get cl = some [sib0, sib1] ∧
          tRel.protectedTags = []
        postUnwind := fun _ _ => False
        modifies := [mutL]
        frameTags := [1]
        canNormal := true
        canUnwind := false }
    CallSpecCut (wops := mirDetWpOps calleeWrite2BytesBody) adapter spec ∧
    MirWpConverges calleeWrite2BytesBody (adapter.mkEntry cl0 tree0)
      (fun out =>
        match out with
        | .normal (rv, m') =>
          rv = .scalar ⟨1, 4⟩ ∧
          mutL.get m'.callerLocals = some [b0, b1] ∧
          sibL.get m'.callerLocals = some [sib0, sib1] ∧
          (exitFrameWithProtectors (rangedBorrowTreeOfMirAlloc m'.borrows m'.activeProtectors 0 12 2) [1]).status = .Released ∧
          (exitFrameWithProtectors (rangedBorrowTreeOfMirAlloc m'.borrows m'.activeProtectors 0 12 2) [1]).tree.protectedTags = []
        | _ => False) := by
  intro mutL sibL borrowSlice cl0 tree0 adapter spec
  let borrowSliceProt : BorrowEntry := { borrowSlice with protector := some 1 }
  let m0 : Memory :=
    { borrows := [borrowSlice], nextTag := 2, callerLocals := cl0 }
  let mRetag : Memory :=
    { m0 with
      borrows := [borrowSliceProt]
      activeProtectors := [1]
      nextProtector := 2 }
  let cl1 : List LocalSlot :=
    List.replicate 12 LocalSlot.uninit ++ [u8BytesToSlot [b0, b1, sib0, sib1]]
  let m1 : Memory :=
    { mRetag with callerLocals := cl1 }
  have hSetMut : mutL.set cl0 [b0, b1] = some cl1 := by
    unfold mutL ByteSubLens.set callerLocalsByteStoreOps
    change (match ParametricCore.listGet? cl0 12 with
      | none => none
      | some slot =>
        match slotAsU8Bytes? slot with
        | none => none
        | some bytes =>
          match Nat.ble (0 + 2) bytes.length with
          | true =>
            ParametricCore.listSet? cl0 12 (u8BytesToSlot (listSplice bytes 0 [b0, b1]))
          | false => none) = some cl1
    have hG : ParametricCore.listGet? cl0 12 = some (u8BytesToSlot [0, 0, sib0, sib1]) := rfl
    rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]
    rfl
  have hGetMut : mutL.get cl1 = some [b0, b1] := by
    unfold mutL ByteSubLens.get callerLocalsByteStoreOps
    change (match ParametricCore.listGet? cl1 12 with
      | none => none
      | some slot =>
        match slotAsU8Bytes? slot with
        | none => none
        | some bytes =>
          match Nat.ble (0 + 2) bytes.length with
          | true => some ((bytes.drop 0).take 2)
          | false => none) = some [b0, b1]
    have hG : ParametricCore.listGet? cl1 12 = some (u8BytesToSlot [b0, b1, sib0, sib1]) := rfl
    rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]
    rfl
  have hGetSib : sibL.get cl1 = some [sib0, sib1] := by
    unfold sibL ByteSubLens.get callerLocalsByteStoreOps
    change (match ParametricCore.listGet? cl1 12 with
      | none => none
      | some slot =>
        match slotAsU8Bytes? slot with
        | none => none
        | some bytes =>
          match Nat.ble (2 + 2) bytes.length with
          | true => some ((bytes.drop 2).take 2)
          | false => none) = some [sib0, sib1]
    have hG : ParametricCore.listGet? cl1 12 = some (u8BytesToSlot [b0, b1, sib0, sib1]) := rfl
    rw [hG]; dsimp only; rw [slotAsU8Bytes?_u8BytesToSlot]
    rfl
  have hStep0 : Anneal.PureMirExec.mirStep calleeWrite2BytesBody (adapter.mkEntry cl0 tree0) =
      .cont { frame := { blockIdx := 0, stmtIdx := 1
                         locals := [.uninit,
                                    .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                    .init (.scalar ⟨b0.toNat, 1⟩),
                                    .init (.scalar ⟨b1.toNat, 1⟩)] }
              memory := mRetag } := rfl
  have hStep1 : Anneal.PureMirExec.mirStep calleeWrite2BytesBody
      { frame := { blockIdx := 0, stmtIdx := 1
                   locals := [.uninit,
                              .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                              .init (.scalar ⟨b0.toNat, 1⟩),
                              .init (.scalar ⟨b1.toNat, 1⟩)] }
        memory := mRetag } =
      .cont { frame := { blockIdx := 0, stmtIdx := 2
                         locals := [.uninit,
                                    .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                    .init (.scalar ⟨b0.toNat, 1⟩),
                                    .init (.scalar ⟨b1.toNat, 1⟩)] }
              memory := m1 } := rfl
  have hStep2 : Anneal.PureMirExec.mirStep calleeWrite2BytesBody
      { frame := { blockIdx := 0, stmtIdx := 2
                   locals := [.uninit,
                              .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                              .init (.scalar ⟨b0.toNat, 1⟩),
                              .init (.scalar ⟨b1.toNat, 1⟩)] }
        memory := m1 } =
      .cont { frame := { blockIdx := 0, stmtIdx := 3
                         locals := [.init (.scalar ⟨1, 4⟩),
                                    .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                    .init (.scalar ⟨b0.toNat, 1⟩),
                                    .init (.scalar ⟨b1.toNat, 1⟩)] }
              memory := m1 } := rfl
  have hStep3 : Anneal.PureMirExec.mirStep calleeWrite2BytesBody
      { frame := { blockIdx := 0, stmtIdx := 3
                   locals := [.init (.scalar ⟨1, 4⟩),
                              .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                              .init (.scalar ⟨b0.toNat, 1⟩),
                              .init (.scalar ⟨b1.toNat, 1⟩)] }
        memory := m1 } =
      .done (.normal (.scalar ⟨1, 4⟩, m1)) := rfl
  have hCut : CallSpecCut (wops := mirDetWpOps calleeWrite2BytesBody) adapter spec := by
    apply seal_callSpecCut (wops := mirDetWpOps calleeWrite2BytesBody)
    intro cl t ⟨hClEq, hTEq⟩
    subst hClEq; subst hTEq
    have hDet0 : mirDetStep calleeWrite2BytesBody (adapter.mkEntry cl0 tree0) =
        .step { frame := { blockIdx := 0, stmtIdx := 1
                           locals := [.uninit,
                                      .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                      .init (.scalar ⟨b0.toNat, 1⟩),
                                      .init (.scalar ⟨b1.toNat, 1⟩)] }
                memory := mRetag } := by
      unfold mirDetStep toStepOutcome; rw [hStep0]
    have hDet1 : mirDetStep calleeWrite2BytesBody
        { frame := { blockIdx := 0, stmtIdx := 1
                     locals := [.uninit,
                                .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                .init (.scalar ⟨b0.toNat, 1⟩),
                                .init (.scalar ⟨b1.toNat, 1⟩)] }
          memory := mRetag } =
        .step { frame := { blockIdx := 0, stmtIdx := 2
                           locals := [.uninit,
                                      .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                      .init (.scalar ⟨b0.toNat, 1⟩),
                                      .init (.scalar ⟨b1.toNat, 1⟩)] }
                memory := m1 } := by
      unfold mirDetStep toStepOutcome; rw [hStep1]
    have hDet2 : mirDetStep calleeWrite2BytesBody
        { frame := { blockIdx := 0, stmtIdx := 2
                     locals := [.uninit,
                                .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                .init (.scalar ⟨b0.toNat, 1⟩),
                                .init (.scalar ⟨b1.toNat, 1⟩)] }
          memory := m1 } =
        .step { frame := { blockIdx := 0, stmtIdx := 3
                           locals := [.init (.scalar ⟨1, 4⟩),
                                      .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                      .init (.scalar ⟨b0.toNat, 1⟩),
                                      .init (.scalar ⟨b1.toNat, 1⟩)] }
                memory := m1 } := by
      unfold mirDetStep toStepOutcome; rw [hStep2]
    have hDet3 : mirDetStep calleeWrite2BytesBody
        { frame := { blockIdx := 0, stmtIdx := 3
                     locals := [.init (.scalar ⟨1, 4⟩),
                                .init (.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]),
                                .init (.scalar ⟨b0.toNat, 1⟩),
                                .init (.scalar ⟨b1.toNat, 1⟩)] }
          memory := m1 } =
        .done (.normal (.scalar ⟨1, 4⟩, m1)) := by
      unfold mirDetStep toStepOutcome; rw [hStep3]
    apply wpOutcome_step (ops := mirDetWpOps calleeWrite2BytesBody)
    change (mirDetStep calleeWrite2BytesBody _).wp _ _ _
    rw [hDet0]
    apply wpOutcome_step (ops := mirDetWpOps calleeWrite2BytesBody)
    change (mirDetStep calleeWrite2BytesBody _).wp _ _ _
    rw [hDet1]
    apply wpOutcome_step (ops := mirDetWpOps calleeWrite2BytesBody)
    change (mirDetStep calleeWrite2BytesBody _).wp _ _ _
    rw [hDet2]
    apply wpOutcome_step (ops := mirDetWpOps calleeWrite2BytesBody)
    change (mirDetStep calleeWrite2BytesBody _).wp _ _ _
    rw [hDet3]
    exact ⟨rfl, UpdatesOnly.of_single_set hSetMut, _, rfl, rfl, hGetMut, hGetSib, rfl⟩
  refine ⟨hCut, ?_⟩
  have hWp := mirWpConverges_of_callSpecCut_normal_cleanup (isCleanupBb := fun bb => Nat.beq bb 2)
    (retBb := 1) (cleanupBb := 2)
    (onNormal := fun bb rv cl' t' =>
      bb = 1 ∧ rv = .scalar ⟨1, 4⟩ ∧
      mutL.get cl' = some [b0, b1] ∧ sibL.get cl' = some [sib0, sib1] ∧ t'.protectedTags = [])
    (onCleanup := fun _ _ _ => False)
    (onUnwindExit := fun _ _ => False)
    (onTerminate := fun _ _ => False)
    hCut ⟨rfl, rfl⟩ rfl
    (fun retVal cl' tRel _ _ _ ⟨hRv, hM, hS, hP⟩ => ⟨rfl, hRv, hM, hS, hP⟩)
    (fun _ _ hC _ _ _ => by cases hC)
    (fun _ _ hA _ _ => by cases hA)
  exact MirWpConverges.mono (by
    intro out hOut
    cases out with
    | normal rv =>
      rcases rv with ⟨v, m'⟩
      dsimp only [adapter, spec] at hOut
      cases hEx : exitFrameWithProtectors (rangedBorrowTreeOfMirAlloc m'.borrows m'.activeProtectors 0 12 2) [1] with
      | mk tRel st =>
        rw [hEx] at hOut
        cases st with
        | Released =>
          dsimp only [evalCallCont4Dispatch] at hOut
          dsimp only
          rw [hEx]
          exact ⟨hOut.2.1, hOut.2.2.1, hOut.2.2.2.1, rfl, hOut.2.2.2.2⟩
        | _ => exact False.elim hOut
    | panic | abort => exact False.elim hOut) hWp

/-- **Witness 3a-iii (REAL caller `Rvalue.ref` + `PointerCoercion "Unsize"` + inline
`TerminatorKind.call` `&mut [u8]` slice writeback + REAL `FnEntry` protector release)**:
for ALL `b0 b1 sib0 sib1 : UInt8`, `callerSliceWriteBody` takes a REAL `&mut [u8; 4]`
borrow of its local array `[0, 0, sib0, sib1]`, unsizes it to `&mut [u8]` via
`CastKind.pointerCoercion "Unsize"`, invokes `calleeWriteSlicePrefixBody` (which opens
with `Retag(FnEntry, _1)` attaching strong protector `1` to tag `1`), writes `b0, b1`
into indices `0, 1`, frames `[sib0, sib1]` at indices `2, 3`, releases protector `1` on
`return_`, and converges via `MirWpConverges` to `[b0, b1, sib0, sib1]`. -/
theorem witness3a_iii_caller_ref_unsize_slice_call_writeback
    (b0 b1 sib0 sib1 : UInt8) :
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit,
                              u8BytesToSlot [0, 0, sib0, sib1],
                              .init (.scalar ⟨b0.toNat, 1⟩),
                              .init (.scalar ⟨b1.toNat, 1⟩),
                              .uninit, .uninit, .uninit] }
        memory := { callees := [calleeWriteSlicePrefixBody] } }
    MirWpConverges callerSliceWriteBody ms0
      (fun out =>
        match out with
        | .normal (v, mem) =>
          v = .aggregate 0 (u8BytesToValues [b0, b1, sib0, sib1]) ∧
          mem.callStack = [] ∧
          mem.activeProtectors = [] ∧
          mem.nextProtector = 2
        | _ => False) := by
  intro ms0
  let fatPtr : Value := .aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨4, 8⟩]
  let b1Entry : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
      perm := .reservedFrz false }
  let b1Prot : BorrowEntry := { b1Entry with protector := some 1 }
  let b1ProtUniq : BorrowEntry := { b1Prot with perm := .unique }
  let mem1 : Memory := { callees := [calleeWriteSlicePrefixBody], borrows := [b1Entry], nextTag := 2 }
  let callerLocs2 : List LocalSlot :=
    [.uninit, u8BytesToSlot [0, 0, sib0, sib1],
     .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩),
     .init (.ptr ⟨1, 0⟩ 8), .init fatPtr, .uninit]
  let saved0 : SavedCallerFrame :=
    { callerBody := callerSliceWriteBody
      frame := { blockIdx := 0, stmtIdx := 2, locals := callerLocs2 }
      destination := pl 6
      returnTarget := 1
      calleeProtectors := []
      returnUnwind := .cleanup 2
      isDiverging := false }
  let saved1 : SavedCallerFrame :=
    { saved0 with
      frame := { blockIdx := 0, stmtIdx := 2
                 locals := [.uninit, u8BytesToSlot [b0, 0, sib0, sib1],
                            .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .init fatPtr, .uninit] } }
  let saved2 : SavedCallerFrame :=
    { saved0 with
      frame := { blockIdx := 0, stmtIdx := 2
                 locals := [.uninit, u8BytesToSlot [b0, b1, sib0, sib1],
                            .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .init fatPtr, .uninit] } }
  let calleeLocs0 : List LocalSlot :=
    [.uninit, .init fatPtr, .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩)]
  let calleeLocsRet : List LocalSlot :=
    [.init (.scalar ⟨2, 4⟩), .init fatPtr, .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩)]
  let mem2 : Memory :=
    { mem1 with callStack := [saved0], activeCallee := some calleeWriteSlicePrefixBody }
  let mem3 : Memory :=
    { mem2 with borrows := [b1Prot], activeProtectors := [1], nextProtector := 2 }
  let mem4 : Memory :=
    { mem3 with borrows := [b1ProtUniq], callStack := [saved1] }
  let mem5 : Memory :=
    { mem4 with callStack := [saved2] }
  let mem6 : Memory :=
    { callees := [calleeWriteSlicePrefixBody], borrows := [b1ProtUniq], nextTag := 2,
      activeCallee := some callerSliceWriteBody, activeProtectors := [], nextProtector := 2 }
  let s1 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1
                 locals := [.uninit, u8BytesToSlot [0, 0, sib0, sib1],
                            .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
      memory := mem1 }
  let s2 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2, locals := callerLocs2 }, memory := mem1 }
  let s3 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 0, locals := calleeLocs0 }, memory := mem2 }
  let s4 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1, locals := calleeLocs0 }, memory := mem3 }
  let s5 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2, locals := calleeLocs0 }, memory := mem4 }
  let s6 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3, locals := calleeLocs0 }, memory := mem5 }
  let s7 : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 4, locals := calleeLocsRet }, memory := mem5 }
  let s8 : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 0
                 locals := [.uninit, u8BytesToSlot [b0, b1, sib0, sib1],
                            .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .init fatPtr, .init (.scalar ⟨2, 4⟩)] }
      memory := mem6 }
  let s9 : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 1
                 locals := [u8BytesToSlot [b0, b1, sib0, sib1],
                            u8BytesToSlot [b0, b1, sib0, sib1],
                            .init (.scalar ⟨b0.toNat, 1⟩), .init (.scalar ⟨b1.toNat, 1⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .init fatPtr, .init (.scalar ⟨2, 4⟩)] }
      memory := mem6 }
  exact step_to_mirWp (s' := s1) rfl
    (step_to_mirWp (s' := s2) rfl
      (step_to_mirWp (s' := s3) rfl
        (step_to_mirWp (s' := s4) rfl
          (step_to_mirWp (s' := s5) rfl
            (step_to_mirWp (s' := s6) rfl
              (step_to_mirWp (s' := s7) rfl
                (step_to_mirWp (s' := s8) rfl
                  (step_to_mirWp (s' := s9) rfl
                    (done_to_mirWp (out := .normal
                      (.aggregate 0 (u8BytesToValues [b0, b1, sib0, sib1]),
                       { mem6 with borrows := disableFrameBorrows mem6.borrows 0 7 })) rfl
                      ⟨rfl, rfl, rfl, rfl⟩)))))))))

/-- **Witness 3b (`CallStackUnwind` callee `assert` failure → caller `UnwindAction.cleanup` recovery)**:
calling `calleeAssertBody` with `flag = false` triggers `.continue_` unwind across the
saved caller frame's `.cleanup 2` landing pad (`isCleanup = true`), releasing callee
protectors and recovering cleanly with return value `999u32` via `MirWpConverges`. -/
theorem witness3b_callee_assert_unwinds_into_caller_cleanup :
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨0, 1⟩), .uninit] }
        memory := { callees := [calleeAssertBody] } }
    MirWpConverges callerCleanupBody ms0
      (fun out =>
        match out with
        | .normal (.scalar ⟨999, 4⟩, mem) => mem.callStack = [] ∧ mem.activeProtectors = []
        | _ => False) := by
  have h1 : Anneal.PureMirExec.mirStep callerCleanupBody
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨0, 1⟩), .uninit] }
        memory := { callees := [calleeAssertBody] } } =
      .cont
        { frame := { blockIdx := 0, stmtIdx := 0
                     locals := [.uninit, .init (.scalar ⟨0, 1⟩)] }
          memory :=
            { callees := [calleeAssertBody]
              callStack :=
                [{ callerBody := callerCleanupBody
                   frame := { blockIdx := 0, stmtIdx := 0
                              locals := [.uninit, .init (.scalar ⟨0, 1⟩), .uninit] }
                   destination := pl 2
                   returnTarget := 1
                   calleeProtectors := []
                   returnUnwind := .cleanup 2
                   isDiverging := false }]
              activeCallee := some calleeAssertBody } } := rfl
  have h2 : Anneal.PureMirExec.mirStep callerCleanupBody
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨0, 1⟩)] }
        memory :=
          { callees := [calleeAssertBody]
            callStack :=
              [{ callerBody := callerCleanupBody
                 frame := { blockIdx := 0, stmtIdx := 0
                            locals := [.uninit, .init (.scalar ⟨0, 1⟩), .uninit] }
                 destination := pl 2
                 returnTarget := 1
                 calleeProtectors := []
                 returnUnwind := .cleanup 2
                 isDiverging := false }]
            activeCallee := some calleeAssertBody } } =
      .cont
        { frame := { blockIdx := 2, stmtIdx := 0
                     locals := [.uninit, .init (.scalar ⟨0, 1⟩), .uninit] }
          memory :=
            { callees := [calleeAssertBody]
              activeCallee := some callerCleanupBody } } := rfl
  have h3 : Anneal.PureMirExec.mirStep callerCleanupBody
      { frame := { blockIdx := 2, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨0, 1⟩), .uninit] }
        memory :=
          { callees := [calleeAssertBody]
            activeCallee := some callerCleanupBody } } =
      .cont
        { frame := { blockIdx := 2, stmtIdx := 1
                     locals := [.init (.scalar ⟨999, 4⟩), .init (.scalar ⟨0, 1⟩), .uninit] }
          memory :=
            { callees := [calleeAssertBody]
              activeCallee := some callerCleanupBody } } := rfl
  have h4 : Anneal.PureMirExec.mirStep callerCleanupBody
      { frame := { blockIdx := 2, stmtIdx := 1
                   locals := [.init (.scalar ⟨999, 4⟩), .init (.scalar ⟨0, 1⟩), .uninit] }
        memory :=
          { callees := [calleeAssertBody]
            activeCallee := some callerCleanupBody } } =
      .done (.normal (.scalar ⟨999, 4⟩,
        { callees := [calleeAssertBody]
          activeCallee := some callerCleanupBody })) := rfl
  exact step_to_mirWp h1 (step_to_mirWp h2 (step_to_mirWp h3 (done_to_mirWp h4 ⟨rfl, rfl⟩)))

/-- **Witness 3c (`RefFrame` universal `topo3` disjoint sibling commutation + `TreeBorrowPerm ↔ TbPermission`)**:
verifies universal 3-node `topo3` disjoint sibling commutation through `exitFrameWithProtectors`
and `evalProtectedRefFrameExit` over `V2026ByteMem`, paired with exact `TreeBorrowPerm ↔ TbPermission`
transition-table and `treeBorrowNodeAccess ↔ performAccess` equivalence against unmodified
`V2026_06_01.MirSemantics`. -/
theorem witness3c_topo3_commutation_and_mir_tb_bridge :
    (∀ kind rel perm isProt,
      tbOutcomeOfMir (treeBorrowPermTransition kind rel perm isProt) =
        performPermAccess (tbKindOfMir kind) (tbRelOfMir rel) (tbPermOfMir perm) isProt) ∧
    (∀ (pSrc pDst : TbPermission) (accSrc accDst protBoth : Bool)
      (_hRead : permCanLocalRead pSrc = true)
      (_hWrite : permCanProtectedLocalWrite pDst = true)
      (rf : RefFrame Nat) (mem : V2026ByteMem) (exit : CalleeExit Value AbstractByte),
      let protTags := if protBoth then [1, 2] else [2]
      let tree0 := mkSharedTopo3Tree16 pSrc accSrc pDst accDst protTags
      let s1 := performRangedAccess tree0 0 8 1 .Read .VisitChildrenOfAccessed
      let s12 := performRangedAccess s1.tree 8 8 2 .Write .VisitChildrenOfAccessed
      let s2 := performRangedAccess tree0 8 8 2 .Write .VisitChildrenOfAccessed
      let s21 := performRangedAccess s2.tree 0 8 1 .Read .VisitChildrenOfAccessed
      let out12 := evalProtectedRefFrameExit ⟨rf, protTags⟩ mem s12.tree exit
      let out21 := evalProtectedRefFrameExit ⟨rf, protTags⟩ mem s21.tree exit
      s1.status = .Completed ∧
      s2.status = .Completed ∧
      s12.status = .Completed ∧
      s21.status = .Completed ∧
      s12.tree = s21.tree ∧
      out12 = out21 ∧
      out12.1 = evalRefFrameExit rf mem exit ∧
      out12.2.protectedTags = []) := by
  refine ⟨treeBorrowPermTransition_eq_performPermAccess, ?_⟩
  intro pSrc pDst accSrc accDst protBoth hRead hWrite rf mem exit
  exact protectedRefFrame_shared_topo3_commutation
    pSrc pDst accSrc accDst protBoth hRead hWrite rf mem exit

/-- **Witness 3d (UNIVERSAL MIR Tree Borrows step ⇒ `RefFrame` step refinement on the REAL
`callerNormalBody` → `calleeBumpMutBody` run)**: for ALL `x ≤ 10000` and `bystander ≤ 10000`,
projecting each live `Memory` through the sound per-allocation `rangedBorrowTreeOfMirAlloc _ _ 0 1 4`
(caller local `_1 = x`):
1. after the callee's `Retag(FnEntry, _1)` (`s₃`), protector `1` is live and tag `2` is
   protected in the projection;
2. the REAL MIR deref write `*_1 = *_1 + 5` (`s₃ → s₄`, through tag `2`) commutes EXACTLY
   with `performRangedAccess _ 0 4 2 .Write .VisitChildrenOfAccessed` on the projection
   (proved via `rangedBorrowTreeOfMirAlloc_twoTag_write_refines`, `.Completed`, exact tree
   equality `= proj s₄`);
3. the REAL `TerminatorKind.return_` (`s₅ → s₆`) commutes EXACTLY with
   `exitFrameWithProtectors _ [2]` on the projection (proved via
   `rangedBorrowTreeOfMirAlloc_twoTag_return_refines`, `.Released`, exact tree equality
   `= proj s₆`, `activeProtectors = []`, caller local `_1 = x + 5`, bystander `_2 = bystander`). -/
theorem witness3d_mir_tree_borrows_step_refines_refframe
    (x bystander : Nat) (hx : x ≤ 10000) (_hb : bystander ≤ 10000) :
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                              .uninit, .uninit, .uninit] }
        memory := { callees := [calleeBumpMutBody] } }
    let proj : MachineState → RangedBorrowTree := fun s =>
      rangedBorrowTreeOfMirAlloc s.memory.borrows s.memory.activeProtectors 0 1 4
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      Anneal.PureMirExec.mirStep callerNormalBody ms0 = .cont s₁ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₁ = .cont s₂ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₂ = .cont s₃ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₃ = .cont s₄ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₄ = .cont s₅ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₅ = .cont s₆ ∧
      s₃.memory.activeProtectors = [1] ∧ (proj s₃).protectedTags = [2] ∧
      (performRangedAccess (proj s₃) 0 4 2 .Write .VisitChildrenOfAccessed).status =
        .Completed ∧
      (performRangedAccess (proj s₃) 0 4 2 .Write .VisitChildrenOfAccessed).tree = proj s₄ ∧
      (exitFrameWithProtectors (proj s₅) [2]).status = .Released ∧
      (exitFrameWithProtectors (proj s₅) [2]).tree = proj s₆ ∧
      s₆.memory.activeProtectors = [] ∧ s₆.memory.callStack = [] ∧
      ParametricCore.listGet? s₆.frame.locals 1 = some (.init (.scalar ⟨x + 5, 4⟩)) ∧
      ParametricCore.listGet? s₆.frame.locals 2 = some (.init (.scalar ⟨bystander, 4⟩)) := by
  intro ms0 proj
  have hW1 : wrapScalarBits (Nat.add x 5) 4294967296 = x + 5 :=
    wrapScalarBits_of_lt (show x + 5 < 4294967296 by omega)
  let borrow1 : BorrowEntry :=
    { tag := 1, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
      perm := .reservedFrz false }
  let child2 : BorrowEntry :=
    { tag := 2, targetLocal := 1, targetFrameDepth := 0, targetProjection := [],
      perm := .reservedFrz false, protector := some 1, parentTag := some 1 }
  let mem1 : Memory :=
    { callees := [calleeBumpMutBody], borrows := [borrow1], nextTag := 2 }
  let savedCaller0 : SavedCallerFrame :=
    { callerBody := callerNormalBody
      frame := { blockIdx := 0, stmtIdx := 1
                 locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
      destination := pl 4
      returnTarget := 1
      calleeProtectors := []
      returnUnwind := .cleanup 2
      isDiverging := false }
  let mem2 : Memory :=
    { mem1 with callStack := [savedCaller0], activeCallee := some calleeBumpMutBody }
  let mem3 : Memory :=
    { mem2 with
      borrows := [child2, borrow1], nextTag := 3,
      activeProtectors := [1], nextProtector := 2 }
  let mem4 : Memory :=
    { mem3 with
      borrows := [{ child2 with perm := .unique }, { borrow1 with perm := .unique }]
      callStack :=
        [{ savedCaller0 with
           frame := { blockIdx := 0, stmtIdx := 1
                      locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                                 .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] } }] }
  let mem5 : Memory :=
    { callees := [calleeBumpMutBody],
      borrows := [{ child2 with perm := .unique }, { borrow1 with perm := .unique }],
      nextTag := 3, nextProtector := 2, activeCallee := some callerNormalBody }
  let s₁ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1
                 locals := [.uninit, .init (.scalar ⟨x, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] }
      memory := mem1 }
  let s₂ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 0
                 locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8)] }
      memory := mem2 }
  let s₃ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 1
                 locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
      memory := mem3 }
  let s₄ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 2
                 locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
      memory := mem4 }
  let s₅ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 3
                 locals := [.init (.scalar ⟨1, 4⟩), .init (.ptr ⟨2, 0⟩ 8)] }
      memory := mem4 }
  let s₆ : MachineState :=
    { frame := { blockIdx := 1, stmtIdx := 0
                 locals := [.uninit, .init (.scalar ⟨x + 5, 4⟩), .init (.scalar ⟨bystander, 4⟩),
                            .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨1, 4⟩), .uninit] }
      memory := mem5 }
  have hStep4 : Anneal.PureMirExec.mirStep callerNormalBody s₃ = .cont s₄ := by
    change Step.cont
      ({ frame := { blockIdx := 0, stmtIdx := 2
                    locals := [.uninit, .init (.ptr ⟨2, 0⟩ 8)] }
         memory :=
           { mem3 with
             borrows := [{ child2 with perm := .unique }, { borrow1 with perm := .unique }]
             callStack :=
               [{ savedCaller0 with
                  frame := { blockIdx := 0, stmtIdx := 1
                             locals := [.uninit,
                                        .init (.scalar ⟨wrapScalarBits (Nat.add x 5) 4294967296, 4⟩),
                                        .init (.scalar ⟨bystander, 4⟩),
                                        .init (.ptr ⟨1, 0⟩ 8), .uninit, .uninit] } }] } } : MachineState) = _
    rw [hW1]
  have hWriteRef := rangedBorrowTreeOfMirAlloc_twoTag_write_refines child2 borrow1 [] 0 1 4
    (by decide) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    (fun _ h => nomatch h)
  have hRetRef := rangedBorrowTreeOfMirAlloc_twoTag_return_refines
    { child2 with perm := .unique } { borrow1 with perm := .unique } [] 0 1 4
    ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    (fun _ h => nomatch h)
  exact ⟨s₁, s₂, s₃, s₄, s₅, s₆,
    rfl, rfl, rfl, hStep4, rfl, rfl,
    rfl, hWriteRef.1, hWriteRef.2.1, hWriteRef.2.2,
    hRetRef.2.1, hRetRef.2.2.2, rfl, rfl, rfl, rfl⟩

/-- **Witness 3e (Range-segmented same-allocation subslice borrows & `accessed`-bit contrast)**:
contrasts flat 1-segment `rangedBorrowTreeOfMirAlloc` against range-segmented
`rangedBorrowTreeOfMirAllocSegmented` on two disjoint protected `&mut` subslice borrows
(`[0..2)` and `[2..4)`) of the same allocation `(0, 12)` — showing flat projection
spuriously reports `.ProtectedDisabled .Unique`, while segmented projection commutes
disjoint reads/writes and releases protector `[2]` cleanly — together with the explicit
`accessed`-bit over-approximation witness (`mirSemantics_vs_refFrame_accessed_coarsening`). -/
theorem witness3e_partial_range_segmented_borrows_and_accessed_contrast :
    let bSrc : BorrowEntry :=
      { tag := 1, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 1, rangeOffset := 0, rangeLen := 2 }
    let bDst : BorrowEntry :=
      { tag := 2, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 2, rangeOffset := 2, rangeLen := 2 }
    let tFlat := rangedBorrowTreeOfMirAlloc [bDst, bSrc] [2, 1] 0 12 4
    let tSeg := rangedBorrowTreeOfMirAllocSegmented [bDst, bSrc] [2, 1] 0 12 [(0, 2), (2, 2)]
    let s1 := performRangedAccess tSeg 0 2 1 .Read .VisitChildrenOfAccessed
    let s12 := performRangedAccess s1.tree 2 2 2 .Write .VisitChildrenOfAccessed
    let s2 := performRangedAccess tSeg 2 2 2 .Write .VisitChildrenOfAccessed
    let s21 := performRangedAccess s2.tree 0 2 1 .Read .VisitChildrenOfAccessed
    (exitFrameWithProtectors tFlat [2]).status =
      .AccessFailure 0 4 1 (.ProtectedDisabled .Unique) ∧
    s12.status = .Completed ∧ s21.status = .Completed ∧ s12.tree = s21.tree ∧
    (exitFrameWithProtectors s12.tree [2]).status = .Released ∧
    (exitFrameWithProtectors s12.tree [2]).tree =
      rangedBorrowTreeOfMirAllocSegmented [bDst, bSrc] [1] 0 12 [(0, 2), (2, 2)] ∧
    (TbLocationState.performAccess ⟨.Frozen, false⟩ .Write .ForeignAccess true =
      .Success ⟨.Disabled, false⟩ ∧
     treeBorrowNodeAccess .write .foreignAccess .frozen true = .ub) :=
  let hSeg := rangedBorrowTreeOfMirAlloc_partial_range_spurious_vs_segmented
  ⟨hSeg.1, hSeg.2.2.2.1, hSeg.2.2.2.2.1, hSeg.2.2.2.2.2.1,
   hSeg.2.2.2.2.2.2.1, hSeg.2.2.2.2.2.2.2,
   mirSemantics_vs_refFrame_accessed_coarsening.2⟩

/-- **Negative Canary N3c (`accessed`-bit soundness of the MIR → `RefFrame` projection)**:
on the REAL `callerNormalBody` run, the post-`Retag(FnEntry)` state `s₃` holds protected
child tag `2` at `.reservedFrz false` under protector `1`. Unmodified MIR faults on ANY
foreign write to such a node (`.ub`), so the projection must encode it as ACCESSED: the
sound `rangedBorrowTreeOfMirAlloc` projection of `s₃` carries `(2, ⟨.ReservedFrz false, true⟩)`,
and a sibling `&mut` write through tag `3` then fails with
`.ProtectedDisabled (.ReservedFrz false)` — exactly MIR's verdict — whereas the unsound
unaccessed encoding would complete silently. -/
theorem neg3c_projection_accessed_bit_soundness :
    let ms0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨7, 4⟩), .init (.scalar ⟨3, 4⟩),
                              .uninit, .uninit, .uninit] }
        memory := { callees := [calleeBumpMutBody] } }
    ∃ s₁ s₂ s₃ : MachineState,
      Anneal.PureMirExec.mirStep callerNormalBody ms0 = .cont s₁ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₁ = .cont s₂ ∧
      Anneal.PureMirExec.mirStep callerNormalBody s₂ = .cont s₃ ∧
      s₃.memory.borrows.map BorrowEntry.perm = [.reservedFrz false, .reservedFrz false] ∧
      s₃.memory.activeProtectors = [1] ∧
      (rangedBorrowTreeOfMirAlloc s₃.memory.borrows s₃.memory.activeProtectors 0 1 4).segments =
        [⟨0, 4, [(0, ⟨.Unique, true⟩), (2, ⟨.ReservedFrz false, true⟩),
                 (1, ⟨.ReservedFrz false, true⟩)]⟩] ∧
      treeBorrowNodeAccess .write .foreignAccess (.reservedFrz false) true = .ub ∧
      TbLocationState.performAccess ⟨.ReservedFrz false, false⟩ .Write .ForeignAccess true =
        .Success ⟨.Disabled, false⟩ :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl,
   borrowEntryAccessed_unaccessed_reserved_unsound.1.1,
   borrowEntryAccessed_unaccessed_reserved_unsound.1.2.1⟩

/-- **Witness 3f (MIR-side per-allocation isolation, exact multi-range/protector round-trip,
and span boundary-alignment exactness)**:
1. Unmodified MIR writes (`invalidateTreeBorrowsAtProj`), reads
   (`freezeTreeBorrowsOnReadAtProj`), and foreign frame teardowns (`disableFrameBorrows`)
   on any distinct allocation `(depthA, locA) ≠ (depthB, locB)` leave both
   `rangedBorrowTreeOfMirAlloc` and `rangedBorrowTreeOfMirAllocSegmented` on `(depthB, locB)`
   **100% invariant**;
2. `mirBorrowsOfRangedTree` round-trips `rangedBorrowTreeOfMirAlloc` **identically** on a
   multi-range, distinct-protector borrow list `[bDst{range:=[2..4), prot:=20},
   bSrc{range:=[0..2), prot:=10}]` via `mirBorrowsOfRangedTree_rangedBorrowTreeOfMirAlloc_eq`;
3. `borrowCoversSegment` is byte-exact on every boundary-aligned span
   (`borrowCoversSegment_exact_of_aligned`) and over-approximates straddling spans such as
   `[0, 4)` against `[0, 2)` at byte `2` (`borrowCoversSegment_misaligned_overapprox`). -/
theorem witness3f_mir_isolation_roundtrip_and_span_alignment
    (allBorrows borrows : List BorrowEntry) (activeProtectors : List Nat)
    (actorTag : Option Nat) (proj : List ProjectionElem) (off len : Nat) :
    let bSrc : BorrowEntry :=
      { tag := 1, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 10, rangeOffset := 0, rangeLen := 2 }
    let bDst : BorrowEntry :=
      { tag := 2, targetLocal := 12, targetFrameDepth := 0, targetProjection := [],
        perm := .unique, protector := some 20, rangeOffset := 2, rangeLen := 2 }
    let rngOf : Nat → Nat × Nat := fun t => if Nat.beq t 1 then (0, 2) else (2, 2)
    let protOf : Nat → Option Nat := fun t => if Nat.beq t 1 then some 10 else some 20
    (rangedBorrowTreeOfMirAlloc
        (invalidateTreeBorrowsAtProj allBorrows borrows 1 actorTag proj off len 0)
        activeProtectors 0 2 4 =
      rangedBorrowTreeOfMirAlloc borrows activeProtectors 0 2 4) ∧
    (rangedBorrowTreeOfMirAlloc
        (freezeTreeBorrowsOnReadAtProj allBorrows borrows 1 actorTag proj off len activeProtectors 0)
        activeProtectors 0 2 4 =
      rangedBorrowTreeOfMirAlloc borrows activeProtectors 0 2 4) ∧
    (mirBorrowsOfAlloc (disableFrameBorrows borrows 1 8) 0 2 =
      mirBorrowsOfAlloc borrows 0 2) ∧
    (mirBorrowsOfRangedTree
        (rangedBorrowTreeOfMirAlloc [bDst, bSrc] [20, 10] 0 12 4)
        0 12 rngOf protOf = [bDst, bSrc]) ∧
    (¬ spanAlignedWithBorrow bSrc 0 4 ∧ borrowCoversSegment bSrc 0 4 = true ∧
      ¬ borrowContainsByte bSrc 2) ∧
    (∀ b, 0 ≤ b → b < 2 → borrowContainsByte bSrc b) ∧
    (∀ b, 2 ≤ b → b < 4 → ¬ borrowContainsByte bSrc b) := by
  intro bSrc bDst rngOf protOf
  have hIso := rangedBorrowTreeOfMirAlloc_invariant_under_foreign_alloc_ops
    allBorrows borrows activeProtectors 1 0 2 0 4 [(0, 2), (2, 2)] actorTag proj off len
    (Or.inr (by decide))
  have hFrame := mirBorrowsOfAlloc_disableFrameBorrows_ne borrows 1 8 0 2 (by decide)
  have hRT : mirBorrowsOfRangedTree
      (rangedBorrowTreeOfMirAlloc [bDst, bSrc] [20, 10] 0 12 4)
      0 12 rngOf protOf = [bDst, bSrc] :=
    mirBorrowsOfRangedTree_rangedBorrowTreeOfMirAlloc_eq [bDst, bSrc] [20, 10] 0 12 4
      rngOf protOf
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | h2
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · rcases List.mem_cons.mp h2 with rfl | h3
          · exact ⟨rfl, rfl, rfl, rfl⟩
          · cases h3)
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | h2
        · exact ⟨by decide, by decide⟩
        · rcases List.mem_cons.mp h2 with rfl | h3
          · exact ⟨by decide, by decide⟩
          · cases h3)
      (fun e1 h1 e2 h2 hEq => by
        rcases List.mem_cons.mp h1 with rfl | h1' <;>
        rcases List.mem_cons.mp h2 with rfl | h2'
        · rfl
        · rcases List.mem_cons.mp h2' with rfl | h2''
          · cases hEq
          · cases h2''
        · rcases List.mem_cons.mp h1' with rfl | h1''
          · cases hEq
          · cases h1''
        · rcases List.mem_cons.mp h1' with rfl | h1''
          · rcases List.mem_cons.mp h2' with rfl | h2''
            · rfl
            · cases h2''
          · cases h1'')
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | h2
        · rfl
        · rcases List.mem_cons.mp h2 with rfl | h3
          · rfl
          · cases h3)
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | h2
        · exact ⟨rfl, rfl⟩
        · rcases List.mem_cons.mp h2 with rfl | h3
          · exact ⟨rfl, rfl⟩
          · cases h3)
  have hMis := borrowCoversSegment_misaligned_overapprox
  have hExIn := (borrowCoversSegment_exact_of_aligned bSrc 0 2 (by decide) hMis.2.2.2.1).1.mp rfl
  have hExOut := (borrowCoversSegment_exact_of_aligned bSrc 2 2 (by decide) hMis.2.2.2.2.1).2.mp rfl
  exact ⟨hIso.1, hIso.2.2, hFrame, hRT,
    ⟨hMis.1, hMis.2.1, hMis.2.2.1⟩,
    (fun b h1 h2 => hExIn b h1 h2),
    (fun b h1 h2 => hExOut b h1 h2)⟩

/-! ## Witness 4: `SpatialMemV2026` — Padded `(u8, [pad; 3], u32)` & Provenance Pointer Struct -/

/-- **Witness 4a (`SpatialMemV2026` padded `(u8, [pad; 3], u32)` lifecycle + contrast
with `u8U32Padded_freeze_refused`)**: freezes `(a := 0x2A, b := 0x11223344)`, mutates
field `b` to `0xCAFEBABE` in `V2026ByteMem`, preserves `.uninit` padding `[1..4)`,
frames disjoint sibling allocation `5`, decodes via unmodified `decodeValueFromBytes`,
reabsorbs, ends the loan, and deallocates the promoted stack allocation. -/
theorem witness4a_spatialMem_padded_u8u32_lifecycle :
    let m0 : V2026ByteMem :=
      { nextAllocId := 10
        allocs := [⟨5, 4, .mut, [.init 0xAA none, .init 0xBB none, .init 0xCC none, .init 0xDD none], true⟩] }
    let bInit : U32Val := ⟨0x11223344, by decide⟩
    let bNew : U32Val := ⟨0xCAFEBABE, by decide⟩
    let initS : U8U32Struct := ⟨0x2A, bInit⟩
    let newS : U8U32Struct := ⟨0x2A, bNew⟩
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨paddedU8U32ToSymVal initS, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨paddedU8U32ToSymVal initS, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := u8U32BodyCtx.specs
        mirLocals := [.immediate .unit, .immediate (paddedU8U32ToMirVal initS)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    ∃ stPinned stMut stReabsorbed stEnded stDealloc,
      freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
        paddedU8U32MemCodec_lawful_sample st0 = .ok stPinned ∧
      mutatePaddedInMem u8U32BodyCtx 1 1 4 4 (u32MemEncode bNew) stPinned = .ok stMut ∧
      readV2026Bytes stMut.mem ⟨10, 1⟩ 3 1 = some [.uninit, .uninit, .uninit] ∧
      loadV2026Typed u8U32BodyCtx.body.layouts (u8U32Ty 0) stMut.mem ⟨10, 0⟩ 8 4 =
        some (.aggregate 0 [.scalar ⟨0x2A, 1⟩, .scalar ⟨0xCAFEBABE, 4⟩]) ∧
      reabsorbPaddedFromMem u8U32BodyCtx 0 stMut = .ok stReabsorbed ∧
      endPaddedLoan u8U32BodyCtx 0 stReabsorbed = .ok stEnded ∧
      getLocal stdValAlg 1 stEnded.sym = some (paddedU8U32ToSymVal newS) ∧
      deallocatePromotedLocal u8U32BodyCtx 1 stEnded = .ok stDealloc ∧
      readV2026Bytes stMut.mem ⟨5, 0⟩ 4 4 =
        some [.init 0xAA none, .init 0xBB none, .init 0xCC none, .init 0xDD none] := by
  intro m0 bInit bNew initS newS st0
  obtain ⟨stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFr, _, hMut, hPad, hLoad, hReab, hEnd, hGet, hDealloc, _, _, _, hFrMut, _, _⟩ :=
    paddedStruct_mem_freeze_mutate_reabsorb_sound 0x2A bInit bNew m0 rfl rfl ⟨5, 0⟩ 4 4 (by decide)
  exact ⟨stPinned, stMut, stReabsorbed, stEnded, stDealloc,
    hFr, hMut, hPad, hLoad, hReab, hEnd, hGet, hDealloc, hFrMut⟩

/-- **Witness 4b (`SpatialMemV2026` provenance-carrying `(u8, [pad; 7], *mut u8)` lifecycle)**:
freezes `(tag := 0x07, ptr := ⟨77, 0x1040⟩)`, mutates byte `0` to `0x99` in `V2026ByteMem`,
preserves all 7 `.uninit` padding bytes `[1..8)` and all 8 `(77, 77)` pointer provenance
bytes `[8..16)`, recovers `.aggregate 0 [.scalar ⟨0x99, 1⟩, .ptr ⟨77, 0x1040⟩ 8]` via
unmodified `decodeValueFromBytes`, reabsorbs, and ends the loan cleanly. -/
theorem witness4b_spatialMem_provPtr_lifecycle :
    let codec := provPtrPaddedMemCodec 77 0
    let ptrOff : U64Offset := ⟨0x1040, by decide⟩
    let initS : ProvPtrStruct := ⟨0x07, ptrOff⟩
    let newS : ProvPtrStruct := ⟨0x99, ptrOff⟩
    let m0 : V2026ByteMem := ⟨20, []⟩
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨StdVal.unit, .unborrowed⟩, ⟨codec.encodeToSymVal initS, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨codec.encodeToSymVal initS, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := provPtrBodyCtx.specs
        mirLocals := [.immediate .unit, .immediate (codec.encodeToMirVal initS)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    ∃ stPinned stMut stReabsorbed stEnded,
      freezePaddedToMem provPtrBodyCtx 0 codec (provPtrPaddedMemCodec_lawful_sample 77) st0 =
        .ok stPinned ∧
      mutatePaddedInMem provPtrBodyCtx 1 1 0 1 [.init 0x99 none] stPinned = .ok stMut ∧
      readV2026Bytes stMut.mem ⟨20, 1⟩ 7 1 =
        some [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit] ∧
      loadV2026Typed provPtrBodyCtx.body.layouts (provPtrMirTy 0) stMut.mem ⟨20, 0⟩ 16 8 =
        some (.aggregate 0 [.scalar ⟨0x99, 1⟩, .ptr ⟨77, 0x1040⟩ 8]) ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 stMut = .ok stReabsorbed ∧
      endPaddedLoan provPtrBodyCtx 0 stReabsorbed = .ok stEnded ∧
      getLocal stdValAlg 1 stEnded.sym = some (codec.encodeToSymVal newS) := by
  intro codec ptrOff initS newS m0 st0
  obtain ⟨stPinned, stMut, stReabsorbed, stEnded,
    hFr, hMut, hPad, hLoad, hReab, hEnd, hGet, _⟩ :=
    provPtrStruct_mem_freeze_mutate_reabsorb_sound 77 0x07 0x99 ptrOff m0 rfl rfl ⟨99, 0⟩ 4 4
      (by decide)
  exact ⟨stPinned, stMut, stReabsorbed, stEnded, hFr, hMut, hPad, hLoad, hReab, hEnd, hGet⟩

/-! ## Fail-Closed Negative Boundary Canaries (`N1..N4`) -/

/-- **Negative Canary N1 (`ByteRun`)**: out-of-bounds, zero-length, immutable
`CapturedAllocation`, and relocation-bearing `CapturedAllocation` copies ALL fail
closed with `none`. -/
theorem neg1_byterun_oob_zero_immutable_relocated_rejected :
    let mV : V2026ByteMem :=
      { nextAllocId := 3
        allocs :=
          [ ⟨1, 4, .mut, List.replicate 4 (.init 1 none), true⟩
          , ⟨2, 4, .mut, List.replicate 4 AbstractByte.uninit, true⟩ ] }
    let immAlloc : CapturedAllocation :=
      { allocId := 10, bytes := [some 1, some 2, some 3, some 4],
        relocations := [], align := ⟨4⟩, mutability := .not }
    let relocAlloc : CapturedAllocation :=
      { allocId := 11, bytes := List.replicate 8 (some 0),
        relocations := [(0, ⟨99, 0⟩)], align := ⟨8⟩, mutability := .mut }
    let dstAlloc : CapturedAllocation :=
      { allocId := 12, bytes := List.replicate 8 (some 0),
        relocations := [], align := ⟨8⟩, mutability := .mut }
    let memG : Memory := { globals := [immAlloc, relocAlloc, dstAlloc] }
    copyRangeComp (Mem := V2026ByteMem) (Addr := Nat) (Byte := AbstractByte)
      ⟨1, 2, 4⟩ ⟨2, 0, 4⟩ mV = none ∧
    copyRangeComp (Mem := V2026ByteMem) (Addr := Nat) (Byte := AbstractByte)
      ⟨1, 0, 0⟩ ⟨2, 0, 0⟩ mV = none ∧
    copyRangeComp (Mem := Memory) (Addr := Nat) (Byte := Option UInt8)
      ⟨10, 0, 4⟩ ⟨12, 0, 4⟩ memG = none ∧
    copyRangeComp (Mem := Memory) (Addr := Nat) (Byte := Option UInt8)
      ⟨11, 0, 8⟩ ⟨12, 0, 8⟩ memG = none := by
  refine ⟨rfl, copyRangeComp_v2026_none_of_zero_len (Or.inl rfl),
    copyRangeComp_memGlobals_none_of_immutable rfl rfl,
    copyRangeComp_memGlobals_none_of_relocated rfl (by decide)⟩

/-- **Negative Canary N2 (`OverflowCastJoin`)**: overflowing input `x = 30000`
(`30000 * 3 = 90000 ≥ 65536`) routes through the overflow arm (`bb7`) of
`ovfCastPipelineBody` to `0xFFFF_FFFFu32`, sets `mulWithOverflowU .u16 30000 3 = (24464, true)`,
and fails false-branch interval admission (`StageIntervalSpec.inRange = false`). -/
theorem neg2_ovfCast_overflow_arm_and_interval_rejection :
    let msOvf : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨42, 4⟩), .init (.scalar ⟨30000, 4⟩),
                              .uninit, .uninit, .uninit] }
        memory := {} }
    MirWpConverges ovfCastPipelineBody msOvf
      (fun out =>
        match out with
        | .normal (.scalar ⟨r, 4⟩, _) => r = 0xFFFFFFFF
        | _ => False) ∧
    mulWithOverflowU .u16 30000 3 = (24464, true) ∧
    StageIntervalSpec.inRange ⟨3, .u16, 0, 60000⟩ 90000 = false := by
  intro msOvf
  refine ⟨?_, rfl, rfl⟩
  exact
    step_to_mirWp (s' := { frame := { blockIdx := 0, stmtIdx := 1
                                      locals := [.uninit, .init (.scalar ⟨42, 4⟩),
                                                 .init (.scalar ⟨30000, 2⟩), .uninit, .uninit, .uninit] }
                           memory := {} }) rfl
      (step_to_mirWp (s' := { frame := { blockIdx := 1, stmtIdx := 0
                                         locals := [.uninit, .init (.scalar ⟨42, 4⟩),
                                                    .init (.scalar ⟨30000, 2⟩), .uninit, .uninit, .uninit] }
                              memory := {} }) rfl
        (step_to_mirWp (s' := { frame := { blockIdx := 1, stmtIdx := 1
                                           locals := [.uninit, .init (.scalar ⟨42, 4⟩),
                                                      .init (.scalar ⟨30000, 2⟩), .uninit, .uninit, .uninit] }
                                memory := {} }) rfl
          (step_to_mirWp (s' := { frame := { blockIdx := 1, stmtIdx := 2
                                             locals := [.uninit, .init (.scalar ⟨42, 4⟩),
                                                        .init (.scalar ⟨30000, 2⟩), .uninit,
                                                        .init (.aggregate 0 [.scalar ⟨24464, 2⟩, .scalar ⟨1, 1⟩]),
                                                        .uninit] }
                                  memory := {} }) rfl
            (step_to_mirWp (s' := { frame := { blockIdx := 7, stmtIdx := 0
                                               locals := [.uninit, .init (.scalar ⟨42, 4⟩),
                                                          .init (.scalar ⟨30000, 2⟩), .uninit,
                                                          .init (.aggregate 0 [.scalar ⟨24464, 2⟩, .scalar ⟨1, 1⟩]),
                                                          .uninit] }
                                    memory := {} }) rfl
              (step_to_mirWp (s' := { frame := { blockIdx := 7, stmtIdx := 1
                                                 locals := [.init (.scalar ⟨0xFFFFFFFF, 4⟩),
                                                            .init (.scalar ⟨42, 4⟩),
                                                            .init (.scalar ⟨30000, 2⟩), .uninit,
                                                            .init (.aggregate 0 [.scalar ⟨24464, 2⟩, .scalar ⟨1, 1⟩]),
                                                            .uninit] }
                                      memory := {} }) rfl
                (done_to_mirWp rfl rfl))))))

private def retZeroBody : CapturedMir :=
  mkBody "tests::ret_zero" 0 [decl .mut u32T] [mkBb [] .return_]

private def assertUnreachableBody : CapturedMir :=
  mkBody "tests::assert_unreachable" 1
    [decl .mut u32T, decl .not boolT]
    [ mkBb [] (.assert (.copy (pl 1)) true 1 .unreachable)
    , mkBb [mkSt (.assign (pl 0) (.use (u32C 0)))] .return_ ]

/-- **Negative Canary N3 (`CallStackUnwind` + `RefFrame`)**:
1. Returning normally to a `SavedCallerFrame` with `isDiverging = true` fails with
   `MirStepNode.fail .ub` and `¬ MirWpConverges`;
2. Failing `.assert` with `UnwindAction.unreachable` fails with `MirStepNode.fail .ub`
   and `¬ MirWpConverges`;
3. Conflicting foreign write on a protected `.Unique` / `.unique` borrow triggers BOTH
   unmodified `V2026_06_01.MirSemantics.treeBorrowNodeAccess = .ub` AND
   `Anneal.RefFrame.TbLocationState.performAccess = .Error _ (.ProtectedDisabled .Unique)`. -/
theorem neg3_diverging_return_unreachable_assert_and_protected_disabled :
    let divCaller : SavedCallerFrame :=
      { callerBody := retZeroBody
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }
        destination := pl 0
        returnTarget := 0
        calleeProtectors := []
        returnUnwind := .terminate
        isDiverging := true }
    let sDiv : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨0, 4⟩)] }
        memory := { callStack := [divCaller] } }
    let sUnreach : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨0, 1⟩)] }
        memory := {} }
    (stepMirFn retZeroBody sDiv = MirStepNode.fail .ub ∧
      ∀ post, ¬ MirWpConverges retZeroBody sDiv post) ∧
    (stepMirFn assertUnreachableBody sUnreach = MirStepNode.fail .ub ∧
      ∀ post, ¬ MirWpConverges assertUnreachableBody sUnreach post) ∧
    (treeBorrowNodeAccess .write .foreignAccess .unique true = .ub ∧
      TbLocationState.performAccess ⟨.Unique, true⟩ .Write .ForeignAccess true =
        .Error ⟨.Disabled, true⟩ (.ProtectedDisabled .Unique)) := by
  intro divCaller sDiv sUnreach
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨rfl, rfl⟩⟩
  · exact stepMirFn_return_diverging_ub (body := retZeroBody) (s := sDiv)
      rfl rfl rfl rfl rfl rfl rfl rfl
  · intro post
    exact not_mirWpConverges_return_diverging_ub (body := retZeroBody) (s := sDiv)
      rfl rfl rfl rfl rfl rfl rfl rfl
  · exact stepMirFn_assert_unreachable_ub (body := assertUnreachableBody) (s := sUnreach)
      rfl rfl rfl rfl rfl rfl rfl
  · intro post
    exact not_mirWpConverges_assert_unreachable_ub (body := assertUnreachableBody) (s := sUnreach)
      rfl rfl rfl rfl rfl rfl rfl

/-- Real inline callee `fn ret_zero_callee() -> u32 { 0 }`. -/
private def retZeroCallee : CapturedMir :=
  mkBody "tests::ret_zero_callee" 0 [decl .mut u32T]
    [mkBb [mkSt (.assign (pl 0) (.use (u32C 0)))] .return_]

/-- Real caller issuing a DIVERGING `TerminatorKind.call` (`target = none`, i.e.
`onRet = none`) to `ret_zero_callee`. -/
private def divCallerBody : CapturedMir :=
  mkBody "tests::div_caller" 0 [decl .mut u32T, decl .mut u32T]
    [ mkBb [] (.call (fnOp "tests::ret_zero_callee") [] (pl 1) none .continue_)
    , mkBb [mkSt (.assign (pl 0) (.use (.copy (pl 1))))] .return_ ]

/-- Contrast caller: the SAME callee via a converging `TerminatorKind.call`
(`target = some 1`). -/
private def convCallerBody : CapturedMir :=
  mkBody "tests::conv_caller" 0 [decl .mut u32T, decl .mut u32T]
    [ mkBb [] (.call (fnOp "tests::ret_zero_callee") [] (pl 1) (some 1) .continue_)
    , mkBb [mkSt (.assign (pl 0) (.binaryOp .add (.copy (pl 1)) (u32C 41)))] .return_ ]

private def divCallerS0 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }
    memory := { callees := [retZeroCallee] } }

/-- Two mutually protected sibling `&mut` tags (`1`, `2`) under `topo3`, whose
`RefFrame` permissions are the `TreeBorrowPerm ↔ TbPermission` image of the MIR
`.unique` permission. -/
private def protExitTree : RangedBorrowTree :=
  { topology := topo3
    protectedTags := [1, 2]
    segments := [⟨0, 8, [(0, ⟨.Unique, true⟩), (1, ⟨tbPermOfMir .unique, true⟩),
                          (2, ⟨tbPermOfMir .unique, true⟩)]⟩] }

/-- **Negative Canary N3b (`CallStackUnwind` on REAL inline diverging calls + `RefFrame`
frame exit)**:
1. A REAL caller `TerminatorKind.call ... (target := none)` (`onRet = none`) pushes a
   diverging `SavedCallerFrame` via unmodified `pushDivergingCalleeFrame`; when the
   inline callee (`Memory.activeCallee = some retZeroCallee`) executes
   `TerminatorKind.return_`, execution faults (`stepMirFn_inline_return_diverging_ub`)
   so `¬ MirWpConverges` from the caller's ENTRY state, while the SAME callee under a
   converging call (`target := some 1`) returns `0 + 41 = 41`;
2. `exitFrameWithProtectors` on frame `[2]` performs tag `2`'s implicit protector-release
   write, which is a conflicting FOREIGN write to protected sibling `&mut` tag `1`
   (`.unique` ↦ `.Unique`) and fails with
   `.AccessFailure 0 8 1 (.ProtectedDisabled .Unique)` (mirrored by unmodified
   `treeBorrowNodeAccess .write .foreignAccess .unique true = .ub`). -/
theorem neg3b_real_diverging_call_and_exitFrame_protected_disabled :
    (∀ post, ¬ MirWpConverges divCallerBody divCallerS0 post) ∧
    MirWpConverges convCallerBody divCallerS0
      (fun out => match out with
        | .normal (.scalar ⟨r, 4⟩, mem) => r = 41 ∧ mem.callStack = []
        | _ => False) ∧
    (exitFrameWithProtectors protExitTree [2]).status =
      .AccessFailure 0 8 1 (.ProtectedDisabled .Unique) ∧
    treeBorrowNodeAccess .write .foreignAccess .unique true = .ub := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro post
    exact not_mirWpConverges_of_step_tau (s' := _) rfl
      (not_mirWpConverges_of_step_tau (s' := _) rfl
        (not_mirWpConverges_inline_return_diverging_ub (callee := retZeroCallee)
          rfl rfl rfl rfl rfl rfl rfl rfl))
  · exact step_to_mirWp rfl (step_to_mirWp rfl (step_to_mirWp rfl (step_to_mirWp rfl
      (done_to_mirWp rfl ⟨rfl, rfl⟩))))

/-- **Witness 2b (`BlockTree` on `CapturedMir` → `OverflowCastJoin` pipeline)**: kernel
evaluation of `evalBlockTreeToCut` over `BlockTree.ofList ovfCastPipelineBody.basicBlocks`
(`O(log n)` block lookups through `mirDetStepWith`) runs the narrowing cast and BOTH
checked `SwitchInt` diamonds plus the widening cast from `bb0` to the `bb6` cutpoint,
sealed as a `StepStageCut` on live `mirDetStep` (`stepStageCut_of_validBlockTreeToCut`)
and composed into `MirWpConverges` with the interval-guarded `addUnchecked` tail:
`1234 ↦ 3 * 1234 + 107 = 3809`. -/
theorem witness2b_ovfCast_blockTree_cut_mir_wp_converges :
    MirWpConverges ovfCastPipelineBody
      { frame := { blockIdx := 0, stmtIdx := 0
                   locals := [.uninit, .init (.scalar ⟨42, 4⟩), .init (.scalar ⟨1234, 4⟩),
                              .uninit, .uninit, .uninit] }
        memory := {} }
      (fun out =>
        match out with
        | .normal (.scalar ⟨r, 4⟩, _) => r = 3809
        | _ => False) :=
  mirWpConverges_of_stepStageCut
    (stepStageCut_of_validBlockTreeToCut (valid_blockTree_ofList _)
      (cuts := MaskTree.ofList [false, false, false, false, false, false, true, false])
      (fuel := 14) (s₁ := _) rfl)
    (step_to_mirWp rfl (step_to_mirWp rfl (step_to_mirWp rfl (done_to_mirWp rfl rfl))))

/-- **Negative Canary N4 (`SpatialMemV2026`)**:
1. Non-padding `.uninit` byte reabsorption returns `.fail` and `decodeValueFromBytes = none`;
2. Pointer provenance stripping AND surplus scalar provenance forgery BOTH return
   `valAndBytesMatchTargetSpec = false`;
3. Pure mutation `writePaddedSymPlace` on a `.spatialPinned` loan returns `.fail`. -/
theorem neg4_spatialMem_uninit_prov_strip_forgery_and_pinned_write_blocked :
    -- 1. Non-padding `.uninit` byte rejected by both `reabsorbPaddedFromMem` and `decodeValueFromBytes`
    (∀ byteOff, byteOff = 0 ∨ byteOff = 4 ∨ byteOff = 5 ∨ byteOff = 6 ∨ byteOff = 7 →
      ∃ stPinned mBad,
        freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0)
          paddedU8U32MemCodec_lawful_sample sampleU8U32InitState = .ok stPinned ∧
        writeV2026Uninit stPinned.mem ⟨1, byteOff⟩ 1 1 = some mBad ∧
        reabsorbPaddedFromMem u8U32BodyCtx 0 { stPinned with mem := mBad } = .fail ∧
        loadV2026Typed u8U32BodyCtx.body.layouts (u8U32Ty 0) mBad ⟨1, 0⟩ 8 4 = none) ∧
    -- 2. Provenance stripping & surplus scalar provenance forgery rejected
    (∃ stPinned mStripped bsStripped,
      freezePaddedToMem provPtrBodyCtx 0 (provPtrPaddedMemCodec 7 0)
        (provPtrPaddedMemCodec_lawful_sample 7) (sampleProvPtrInitState 7) = .ok stPinned ∧
      writeV2026Bytes stPinned.mem ⟨1, 8⟩ 1 [.init 0x00 none] = some mStripped ∧
      readV2026Bytes mStripped ⟨1, 0⟩ 16 8 = some bsStripped ∧
      valAndBytesMatchTargetSpec false provPtrBodyCtx.body.layouts
        (provPtrTargetSpec 0) (provPtrToMirVal 7 ⟨0x10, ⟨0x1000, by decide⟩⟩) bsStripped = false ∧
      reabsorbPaddedFromMem provPtrBodyCtx 0 { stPinned with mem := mStripped } = .fail) ∧
    valAndBytesMatchTargetSpec false u8U32BodyCtx.body.layouts u32TargetSpec
      (.scalar ⟨42, 4⟩)
      [.init 42 (some (7, 7)), .init 0 none, .init 0 none, .init 0 none] = false ∧
    -- 3. Unauthenticated `BodySpatialCtx` & `.ref` target rejected, plus pinned pure-write blocking
    (bodySpatialCtxWf
      { body := { u8U32SampleBody with layouts := { pointerBits := 64, isLittleEndian := true, entries := [] } }
        specs := u8U32BodyCtx.specs } = false ∧
      ∃ stPinned,
        readPlaceVal stdValAlg (.derefSub 2 []) stPinned.sym = none ∧
        writePlaceVal stdValAlg (.derefSub 2 [])
          ((paddedU8U32MemCodec 0).encodeToSymVal ⟨0x22, ⟨0xAABBCCDD, by decide⟩⟩) stPinned.sym = none ∧
        endPaddedLoan
          { body :=
              { u8U32SampleBody with
                localDecls :=
                  u8U32SampleBody.localDecls ++
                    [{ mutability := .mut
                       ty := { kind := .ref .mut (u8U32Ty 0).kind, layoutIdx := 0 }
                       debugName := some "r" }] }
            specs :=
              u8U32BodyCtx.specs ++ [.mirTy { kind := .ref .mut (u8U32Ty 0).kind, layoutIdx := 0 }] }
          0 stPinned = .fail) ∧
    -- 4. Forged under-alignment, forged all-padding mask, and desynced `mirLocals` rejected
    (codecLayoutAndMaskMatchSpec u8U32BodyCtx.body.layouts (paddedU8U32MemCodec 0).targetTy
        { size := 8, alignBytes := 1 } (paddedU8U32MemCodec 0).padMask = false ∧
      codecLayoutAndMaskMatchSpec u8U32BodyCtx.body.layouts (paddedU8U32MemCodec 0).targetTy
        (paddedU8U32MemCodec 0).layout (List.replicate 8 true) = false ∧
      freezePaddedToMem u8U32BodyCtx 0 (paddedU8U32MemCodec 0) paddedU8U32MemCodec_lawful_sample
        { sampleU8U32InitState with
          mirLocals := [.immediate .unit, .immediate (.aggregate 0 [.scalar ⟨0xFF, 1⟩, .scalar ⟨0, 4⟩])] } =
        .fail) := by
  refine ⟨padded_nonpad_uninit_rejected, provPtr_provenance_stripping_rejected, rfl,
    ⟨rfl, ?_⟩, forged_align_padMask_and_desync_mirLocal_rejected⟩
  obtain ⟨stPinned, _, hRd, hWr, _, _, _, hEnd⟩ :=
    pinned_loan_blocks_pure_mutation_until_reabsorb
  exact ⟨stPinned, hRd, hWr, hEnd⟩

end Anneal.ParametricStageCutAndSpatialMemTests
