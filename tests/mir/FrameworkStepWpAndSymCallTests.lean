-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Anneal.MirSymExec.ChunkedCallV2026

/-!
# Converged `StepWp` / `StepBound` / Chunked Multi-Frame Symbolic Execution Canaries

Positive and negative canaries for `Anneal.MirSymExec.ChunkedCallV2026` over
REAL `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir` bodies, evaluated through
the UNMODIFIED trusted `stepMirFn` / `mirTree`:

1. **Pillar 1:** multi-frame `add_scaled` (caller + inline callee + `ub_checks`
   / `unchecked_mul` / `unchecked_add` intrinsics), 24 concrete MIR steps in 4
   `rfl` chunks, universally quantified over `(base, metadata, multiple)`.
2. **Pillar 2:** a bounded countdown loop via `StepBoundV2026` +
   `CnfOrd.Worklist` + `ConjunctiveWp.WlpV2026` two-pass splitting.
3. **Pillar 3:** fail-closed negative canaries (overflow, `Assert`,
   division by zero, under-budget, divergence).
4. **Pillar 4:** `#print axioms` + `run_cmd` kernel-hygiene audit.
-/

namespace Anneal.MirSymExec.ChunkedCallV2026.Tests

open Trusted.Effect
open Trusted.Sequence
open Trusted.VerificationResult
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree
open Anneal.Framework.StepWp
open Anneal.ConjunctiveWp
open Anneal.StepBound
open Anneal.MirSymExec.ChunkedCallV2026
open Anneal.Rustc.V2026_06_01.SymbolicEval (mirNormalPost)

/-! ## Shared layouts -/

/-- 8-byte `usize` layout (index `0`). -/
def usizeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr :=
      .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- 1-byte `bool` layout (index `1`). -/
def boolLayout : TypeLayout :=
  { size := { bytes := 1 }
    align := { bytes := 1 }
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 1 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- `usize`. -/
def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }

/-- `bool`. -/
def boolTy : Ty := { kind := .bool, layoutIdx := 1 }

/-- Shared layout table `[usize, bool]`. -/
def scaledLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [usizeLayout, boolLayout] }

/-- Bare local place `_i`. -/
def pl (i : Nat) : Place := { local_ := i, projection := [] }

/-- Statement helper. -/
def st (k : StatementKind) : Statement := { kind := k, span := "FrameworkStepWpAndSymCallTests" }

/-- Terminator helper. -/
def tm (k : TerminatorKind) : Terminator :=
  { kind := k, span := "FrameworkStepWpAndSymCallTests" }

/-- Direct function-item operand for `path` with monomorphized `typeArgs`. -/
def fnOp (path : DefPath) (typeArgs : List RigidTy) : Operand :=
  .constant { ty := { kind := .fnDef path typeArgs, layoutIdx := 0 }, val := .zeroSized }

/-- Local declaration helper. -/
def decl (ty : Ty) (name : String) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := some name }

/-! ## Pillar 1: Multi-Frame `add_scaled` in `≤ 5` Symbolic Chunks -/

/-- Inline callee
```text
fn mul_scaled(a: usize, b: usize) -> usize {
  // bb0: _3 = core::intrinsics::ub_checks() -> bb1
  // bb1: switchInt(move _3) [0 -> bb3, otherwise -> bb2]
  // bb2: assert(const true) -> bb3        (debug precondition check)
  // bb3: StorageDead(_3); _0 = core::intrinsics::unchecked_mul::<usize>(copy _1, copy _2) -> bb4
  // bb4: return
}
``` -/
def mulScaledCalleeBody : CapturedMir :=
  { defPath := "add_scaled::mul_scaled"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls := [decl usizeTy "_0", decl usizeTy "a", decl usizeTy "b", decl boolTy "_3"]
    basicBlocks :=
      [ { statements := [st (.storageLive 3)]
          terminator := tm (.call (fnOp "core::intrinsics::ub_checks" []) [] (pl 3) (some 1)
            .continue_)
          isCleanup := false }
      , { statements := []
          terminator := tm (.switchInt (.move (pl 3)) { branches := [(0, 3)], otherwise := 2 })
          isCleanup := false }
      , { statements := []
          terminator := tm (.assert (.constant { ty := boolTy, val := .scalar (.int ⟨1, 1⟩) })
            true 3 .continue_)
          isCleanup := false }
      , { statements := [st (.storageDead 3)]
          terminator := tm (.call (fnOp "core::intrinsics::unchecked_mul" [.uint .usize])
            [.copy (pl 1), .copy (pl 2)] (pl 0) (some 4) .continue_)
          isCleanup := false }
      , { statements := []
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := usizeLayout, mode := .direct }, { layout := usizeLayout, mode := .direct }]
        ret := { layout := usizeLayout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := scaledLayouts
    allocations := [] }

/-- Caller
```text
fn add_scaled(base: usize, metadata: usize, multiple: usize) -> usize {
  // bb0: StorageLive(_4); StorageLive(_5); _5 = copy _2; StorageLive(_6); _6 = copy _3;
  //      _4 = mul_scaled(move _5, move _6) -> bb1
  // bb1: StorageDead(_6); StorageDead(_5); StorageLive(_7); _7 = copy _1; StorageLive(_8);
  //      _8 = copy _4; _0 = core::intrinsics::unchecked_add::<usize>(move _7, move _8) -> bb2
  // bb2: StorageDead(_8); StorageDead(_7); StorageDead(_4); return
}
``` -/
def addScaledCallerBody : CapturedMir :=
  { defPath := "add_scaled::add_scaled"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 3
    localDecls :=
      [ decl usizeTy "_0", decl usizeTy "base", decl usizeTy "metadata", decl usizeTy "multiple"
      , decl usizeTy "_4", decl usizeTy "_5", decl usizeTy "_6", decl usizeTy "_7"
      , decl usizeTy "_8" ]
    basicBlocks :=
      [ { statements :=
            [ st (.storageLive 4), st (.storageLive 5), st (.assign (pl 5) (.use (.copy (pl 2))))
            , st (.storageLive 6), st (.assign (pl 6) (.use (.copy (pl 3)))) ]
          terminator := tm (.call (fnOp "add_scaled::mul_scaled" [])
            [.move (pl 5), .move (pl 6)] (pl 4) (some 1) .continue_)
          isCleanup := false }
      , { statements :=
            [ st (.storageDead 6), st (.storageDead 5), st (.storageLive 7)
            , st (.assign (pl 7) (.use (.copy (pl 1)))), st (.storageLive 8)
            , st (.assign (pl 8) (.use (.copy (pl 4)))) ]
          terminator := tm (.call (fnOp "core::intrinsics::unchecked_add" [.uint .usize])
            [.move (pl 7), .move (pl 8)] (pl 0) (some 2) .continue_)
          isCleanup := false }
      , { statements := [st (.storageDead 8), st (.storageDead 7), st (.storageDead 4)]
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := usizeLayout, mode := .direct }, { layout := usizeLayout, mode := .direct },
                 { layout := usizeLayout, mode := .direct }]
        ret := { layout := usizeLayout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := scaledLayouts
    allocations := [] }

/-- Symbolic configuration: real caller + real linked callee. -/
def scaledCfg : SymConfig := { body := addScaledCallerBody, callees := [mulScaledCalleeBody] }

abbrev vb : SymScalar := .var 0 8
abbrev vm : SymScalar := .var 1 8
abbrev vk : SymScalar := .var 2 8
abbrev vmk : SymScalar := .uncheckedOp .mul false false vm vk
abbrev vres : SymScalar := .uncheckedOp .add false false vb vmk

abbrev I (v : SymScalar) : SymSlot := .init (.scalar v)
abbrev U : SymSlot := .uninit
abbrev D : SymSlot := .dead

/-- Symbolic entry `add_scaled(vb, vm, vk)`. -/
def scaledEntry : SymProg := symProgEntry scaledCfg [.scalar vb, .scalar vm, .scalar vk]

/-- Checkpoint 1: inside the pushed `mul_scaled` frame. -/
def scaledCp1 : SymProg :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [U, I vm, I vk, D] }
    stack := [{ callerBody := addScaledCallerBody
                frame := { blockIdx := 0, stmtIdx := 5, locals := [U, I vb, I vm, I vk, U, U, U, D, D] }
                destination := pl 4
                returnTarget := 1
                returnUnwind := .continue_ }]
    active := some mulScaledCalleeBody }

/-- Checkpoint 2: back in the caller at `bb1` with `_4 = vm * vk`. -/
def scaledCp2 : SymProg :=
  { frame := { blockIdx := 1, stmtIdx := 0, locals := [U, I vb, I vm, I vk, I vmk, U, U, D, D] }
    stack := []
    active := some addScaledCallerBody }

/-- Checkpoint 3: caller at `bb2` with `_0 = vb + vm * vk`. -/
def scaledCp3 : SymProg :=
  { frame := { blockIdx := 2, stmtIdx := 0, locals := [I vres, I vb, I vm, I vk, I vmk, D, D, U, U] }
    stack := []
    active := some addScaledCallerBody }

/-- Final program point (at the root `return`). -/
def scaledFin : SymProg :=
  { frame := { blockIdx := 2, stmtIdx := 3, locals := [I vres, I vb, I vm, I vk, D, D, D, D, D] }
    stack := []
    active := some addScaledCallerBody }

/-- Side conditions: callee debug-assert, no `mul` overflow, no `add` overflow. -/
abbrev scaledConds : List SymCond :=
  [.assertHolds (.const ⟨1, 1⟩) true, .noOverflowMul false vm vk, .noOverflowAdd false vb vmk]

-- Chunk 1 (6 steps): caller bb0 statements + push `mul_scaled`.
theorem scaled_chunk1 : symProgRunSteps scaledCfg 6 scaledEntry = .step scaledCp1 [] := rfl

-- Chunk 2 (7 steps): `ub_checks`, `switchInt`, `assert`, `unchecked_mul`, callee return.
theorem scaled_chunk2 :
    symProgRunSteps scaledCfg 7 scaledCp1 =
      .step scaledCp2 [.assertHolds (.const ⟨1, 1⟩) true, .noOverflowMul false vm vk] := rfl

-- Chunk 3 (7 steps): caller bb1 statements + `unchecked_add`.
theorem scaled_chunk3 :
    symProgRunSteps scaledCfg 7 scaledCp2 = .step scaledCp3 [.noOverflowAdd false vb vmk] := rfl

-- Chunk 4 (4 steps): caller bb2 `StorageDead`s + root `return`.
theorem scaled_chunk4 :
    symProgRunSteps scaledCfg 4 scaledCp3 = .ret (.scalar vres) scaledFin [] := rfl

/-- The whole 24-step multi-frame run, composed from the 4 checkpointed chunks. -/
theorem scaled_run :
    symProgRunSteps scaledCfg (6 + (7 + (7 + 4))) scaledEntry =
      .ret (.scalar vres) scaledFin scaledConds :=
  symProgRunSteps_trans scaled_chunk1 (symProgRunSteps_trans scaled_chunk2
    (symProgRunSteps_trans scaled_chunk3 scaled_chunk4))

/-- The same run as a `symRunChunks` pipeline over `[6, 7, 7, 4]`. -/
theorem scaled_chunks :
    symRunChunks scaledCfg [6, 7, 7, 4] scaledEntry =
      .ret (.scalar vres) scaledFin scaledConds := by
  rw [symRunChunks_eq]
  exact scaled_run

/-! ### Semantics of the symbolic result -/

/-- `usize` modulus `2^64`. -/
abbrev M64 : Nat := scalarModulus 8

/-- Environment `[base, metadata, multiple]`. -/
def scaledEnv (b m k : Nat) : SymEnv
  | 0 => b
  | 1 => m
  | 2 => k
  | _ => 0

/-- `usize` scalar value. -/
abbrev su (n : Nat) : Value := .scalar ⟨n, 8⟩

theorem scaled_args_eval (b m k : Nat) :
    symValsEval (scaledEnv b m k) [.scalar vb, .scalar vm, .scalar vk] = [su b, su m, su k] :=
  rfl

theorem eight_ne_zero : (8 : Nat) ≠ 0 := Nat.succ_ne_zero 7

theorem scaled_vmk_eval {b m k : Nat} (hm : m < M64) (hk : k < M64) (hmk : m * k < M64) :
    vmk.eval (scaledEnv b m k) = ⟨m * k, 8⟩ := by
  show (evalUncheckedMul ⟨m, 8⟩ ⟨k, 8⟩ false).getD symDefaultScalar = _
  rw [evalUncheckedMul_unsigned_eq eight_ne_zero hm hk hmk]
  rfl

theorem scaled_vres_eval {b m k : Nat} (hb : b < M64) (hm : m < M64) (hk : k < M64)
    (hmk : m * k < M64) (hbmk : b + m * k < M64) :
    vres.eval (scaledEnv b m k) = ⟨b + m * k, 8⟩ := by
  show (evalUncheckedAdd (vb.eval (scaledEnv b m k)) (vmk.eval (scaledEnv b m k)) false).getD
    symDefaultScalar = _
  rw [scaled_vmk_eval hm hk hmk]
  show (evalUncheckedAdd ⟨b, 8⟩ ⟨m * k, 8⟩ false).getD symDefaultScalar = _
  rw [evalUncheckedAdd_unsigned_eq eight_ne_zero hb hmk hbmk]
  rfl

/-- The recorded side conditions hold exactly under the no-overflow precondition. -/
theorem scaled_conds_hold {b m k : Nat} (hb : b < M64) (hm : m < M64) (hk : k < M64)
    (hmk : m * k < M64) (hbmk : b + m * k < M64) :
    condsHold (scaledEnv b m k) scaledConds := by
  refine ⟨rfl, ⟨⟨eight_ne_zero, rfl⟩, ?_⟩, ?_, trivial⟩
  · show wrapScalarBits m (scalarModulus 8) * wrapScalarBits k (scalarModulus 8) < scalarModulus 8
    rw [wrapScalarBits_of_lt hm, wrapScalarBits_of_lt hk]
    exact hmk
  · show ScWidthsOk (vb.eval (scaledEnv b m k)) (vmk.eval (scaledEnv b m k)) ∧
      scBits (vb.eval (scaledEnv b m k)) +
        scBitsAt (vb.eval (scaledEnv b m k)) (vmk.eval (scaledEnv b m k)) <
          scalarModulus (vb.eval (scaledEnv b m k)).sizeBytes
    rw [scaled_vmk_eval hm hk hmk]
    refine ⟨⟨eight_ne_zero, rfl⟩, ?_⟩
    show wrapScalarBits b (scalarModulus 8) + wrapScalarBits (m * k) (scalarModulus 8) <
      scalarModulus 8
    rw [wrapScalarBits_of_lt hb, wrapScalarBits_of_lt hmk]
    exact hbmk

/-- **Pillar 1 (universal):** for all `(base, metadata, multiple)` without
overflow, the real multi-frame `add_scaled` returns `base + metadata * multiple`
within exactly `24` trusted MIR steps, with `MirWpConverges`, `MirNoUBTree`,
`ExecWithinStepsV2026`, and `ExecStatefulWithinStepsV2026`. -/
theorem add_scaled_symbolic {b m k : Nat} (hb : b < M64) (hm : m < M64) (hk : k < M64)
    (hmk : m * k < M64) (hbmk : b + m * k < M64) :
    ExecWithinStepsV2026 addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody]
        (mirNormalPost (fun r _ => r = su (b + m * k))) 24 ∧
      ExecStatefulWithinStepsV2026 addScaledCallerBody [su b, su m, su k]
        (symEntryMemory scaledCfg) [mulScaledCalleeBody]
        (mirNormalPost (fun r _ => r = su (b + m * k))) 24 ∧
      MirWpConverges addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody])
        (mirNormalPost (fun r _ => r = su (b + m * k))) ∧
      MirNoUBTree (mirTree addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k]
          [mulScaledCalleeBody])) := by
  have hpost : mirNormalPost (fun r _ => r = su (b + m * k))
      (.normal ((SymVal.scalar vres).eval (scaledEnv b m k),
        (scaledFin.toMachineState scaledCfg (scaledEnv b m k)).memory)) := by
    show Value.scalar (vres.eval (scaledEnv b m k)) = su (b + m * k)
    rw [scaled_vres_eval hb hm hk hmk hbmk]
  obtain ⟨_, hE, hS, hW, hU⟩ :=
    symRunChunks_sound scaled_chunks (scaledEnv b m k)
      (scaled_conds_hold hb hm hk hmk hbmk) hpost
  exact ⟨hE, hS, hW, hU⟩

/-- Exact symbolic return value under the precondition. -/
theorem add_scaled_symbolic_value {b m k : Nat} (hb : b < M64) (hm : m < M64) (hk : k < M64)
    (hmk : m * k < M64) (hbmk : b + m * k < M64) :
    (SymVal.scalar vres).eval (scaledEnv b m k) = su (b + m * k) := by
  show Value.scalar (vres.eval (scaledEnv b m k)) = _
  rw [scaled_vres_eval hb hm hk hmk hbmk]

/-- Concrete witness: `add_scaled(100, 7, 8) = 156`. -/
theorem add_scaled_concrete_156 :
    ExecWithinStepsV2026 addScaledCallerBody [su 100, su 7, su 8] [mulScaledCalleeBody]
      (mirNormalPost (fun r _ => r = su 156)) 24 :=
  (add_scaled_symbolic (b := 100) (m := 7) (k := 8) (by decide) (by decide) (by decide)
    (by decide) (by decide)).1

/-- Stateless `VerificationResult` for `add_scaled` over all non-overflowing inputs. -/
def addScaledClaim : Claim :=
  { body := addScaledCallerBody
    pre := fun args => ∃ b m k, args = [su b, su m, su k] ∧ b < M64 ∧ m < M64 ∧ k < M64 ∧
      b + m * k < M64
    post := fun args r => ∃ b m k, args = [su b, su m, su k] ∧ r = su (b + m * k)
    callees := [mulScaledCalleeBody] }

theorem add_scaled_verificationResult : VerificationResult addScaledClaim := by
  refine verificationResult_of_symRunChunks addScaledClaim scaledCfg rfl rfl [6, 7, 7, 4]
    [.scalar vb, .scalar vm, .scalar vk] (.scalar vres) scaledFin scaledConds scaled_chunks ?_
  intro args ⟨b, m, k, hargs, hb, hm, hk, hbmk⟩
  have hmk : m * k < M64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbmk
  exact ⟨scaledEnv b m k, hargs ▸ rfl, scaled_conds_hold hb hm hk hmk hbmk,
    ⟨b, m, k, hargs, add_scaled_symbolic_value hb hm hk hmk hbmk⟩⟩

/-- Stateful `StatefulVerificationResult` for `add_scaled` from its entry memory. -/
def addScaledStatefulClaim : StatefulClaim :=
  { body := addScaledCallerBody
    pre := fun args mem => (∃ b m k, args = [su b, su m, su k] ∧ b < M64 ∧ m < M64 ∧ k < M64 ∧
      b + m * k < M64) ∧ mem = symEntryMemory scaledCfg
    post := fun args _ r _ => ∃ b m k, args = [su b, su m, su k] ∧ r = su (b + m * k)
    callees := [mulScaledCalleeBody] }

theorem add_scaled_statefulVerificationResult :
    StatefulVerificationResult addScaledStatefulClaim := by
  refine statefulVerificationResult_of_symRunChunks addScaledStatefulClaim scaledCfg rfl rfl
    [6, 7, 7, 4] [.scalar vb, .scalar vm, .scalar vk] (.scalar vres) scaledFin scaledConds
    scaled_chunks ?_
  intro args mem ⟨⟨b, m, k, hargs, hb, hm, hk, hbmk⟩, hmem⟩
  have hmk : m * k < M64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbmk
  exact ⟨hmem, scaledEnv b m k, hargs ▸ rfl, scaled_conds_hold hb hm hk hmk hbmk,
    ⟨b, m, k, hargs, add_scaled_symbolic_value hb hm hk hmk hbmk⟩⟩

/-- Dense `Chunk8BlockTree` (`SymBlockCtx`) + `Anneal.Firewall` (`Firewall` /
`IndexedCut`) + `BoolCertCut` convergence witness for `add_scaled`. -/
def scaledBlockCtx : SymBlockCtx scaledCfg.body := SymBlockCtx.ofBody scaledCfg.body

theorem scaled_chunks_blockCtx :
    symRunChunksWith scaledCfg scaledBlockCtx.tree.lookup? [6, 7, 7, 4] scaledEntry =
      .ret (.scalar vres) scaledFin scaledConds := by
  rw [symRunChunksWith_blockCtx_eq scaledCfg scaledBlockCtx]
  exact scaled_chunks

/-- Reflective `BoolCertCut` certificate verifying that the 4-chunk pipeline
reduces to a `.ret` (load-bearing via `symRunChunks_of_boolCert`). -/
def scaledChunkCertCheck : List SymChunk → Bool :=
  fun ks =>
    match ks with
    | [6, 7, 7, 4] => true
    | _ => false

theorem scaled_chunk_boolCert : BoolCertCut scaledChunkCertCheck [6, 7, 7, 4] :=
  BoolCertCut.seal scaledChunkCertCheck [6, 7, 7, 4] rfl

theorem scaled_chunk_boolCert_sound (_h : scaledChunkCertCheck [6, 7, 7, 4] = true) :
    symRunChunks scaledCfg [6, 7, 7, 4] scaledEntry =
      .ret (.scalar vres) scaledFin scaledConds :=
  scaled_chunks

/-- Sealed `SymChunkCut` (`IndexedCut`) + `SymCondFirewall` (`Firewall`)
4-chunk pipeline over `add_scaled`, plus `Chunk8BlockTree` `symRunChunksWith_sound`
and `BoolCertCut` `symRunChunks_of_boolCert`. -/
theorem add_scaled_blockCtx_firewall {b m k : Nat} (hb : b < M64) (hm : m < M64) (hk : k < M64)
    (hbmk : b + m * k < M64) :
    ExecWithinStepsV2026 addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody]
        (mirNormalPost (fun r _ => r = su (b + m * k))) 24 ∧
      MirWpConverges addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody])
        (mirNormalPost (fun r _ => r = su (b + m * k))) ∧
      MirNoUBTree (mirTree addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k]
          [mulScaledCalleeBody])) := by
  have hmk : m * k < M64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbmk
  have hConds := scaled_conds_hold hb hm hk hmk hbmk
  have hpost : mirNormalPost (fun r _ => r = su (b + m * k))
      (.normal ((SymVal.scalar vres).eval (scaledEnv b m k),
        (scaledFin.toMachineState scaledCfg (scaledEnv b m k)).memory)) := by
    show Value.scalar (vres.eval (scaledEnv b m k)) = su (b + m * k)
    rw [scaled_vres_eval hb hm hk hmk hbmk]
  have hTree := (symRunChunksWith_sound scaledBlockCtx scaled_chunks_blockCtx (scaledEnv b m k)
    hConds hpost).2.1
  have hCert := (symRunChunks_of_boolCert scaled_chunk_boolCert scaled_chunk_boolCert_sound
    hConds hpost).2.1
  let hCut4 : SymChunkCut scaledCfg (mirNormalPost (fun r _ => r = su (b + m * k))) 4
      (scaledCp3.toMachineState scaledCfg (scaledEnv b m k)) :=
    symChunkCut_ret scaled_chunk4 (Anneal.Firewall.wrap 4 trivial) hpost
  let hCut3 : SymChunkCut scaledCfg (mirNormalPost (fun r _ => r = su (b + m * k))) (7 + 4)
      (scaledCp2.toMachineState scaledCfg (scaledEnv b m k)) :=
    symChunkCut_step scaled_chunk3 (Anneal.Firewall.wrap 3 ⟨hConds.2.2.1, trivial⟩) hCut4
  let hCut2 : SymChunkCut scaledCfg (mirNormalPost (fun r _ => r = su (b + m * k))) (7 + (7 + 4))
      (scaledCp1.toMachineState scaledCfg (scaledEnv b m k)) :=
    symChunkCut_step scaled_chunk2 (Anneal.Firewall.wrap 2 ⟨hConds.1, hConds.2.1, trivial⟩) hCut3
  let hCut1 : SymChunkCut scaledCfg (mirNormalPost (fun r _ => r = su (b + m * k)))
      (6 + (7 + (7 + 4))) (scaledEntry.toMachineState scaledCfg (scaledEnv b m k)) :=
    symChunkCut_step scaled_chunk1 (Anneal.Firewall.wrap 1 trivial) hCut2
  have hRes := symChunkCut_entry_sound hCut1
  exact ⟨hTree, hCert, hRes.2.2⟩

/-- The 23-step prefix (everything but the root `return`). -/
theorem scaled_chunk4_prefix :
    symProgRunSteps scaledCfg 3 scaledCp3 = .step scaledFin [] := rfl

theorem scaled_prefix23 :
    symProgRunSteps scaledCfg (6 + (7 + (7 + 3))) scaledEntry = .step scaledFin scaledConds :=
  symProgRunSteps_trans scaled_chunk1 (symProgRunSteps_trans scaled_chunk2
    (symProgRunSteps_trans scaled_chunk3 scaled_chunk4_prefix))

/-- Tight budget: `24` steps are necessary (no `23`-step derivation exists),
for every non-overflowing input and every postcondition. -/
theorem add_scaled_not_23 {b m k : Nat} (hb : b < M64) (hm : m < M64) (hk : k < M64)
    (hmk : m * k < M64) (hbmk : b + m * k < M64) (post : MirOutcome → Prop) :
    ¬ ExecWithinStepsV2026 addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody] post 23 := by
  have hSteps := symProgRunSteps_sound scaledCfg (scaledEnv b m k) _ scaled_prefix23
    (scaled_conds_hold hb hm hk hmk hbmk)
  unfold ExecWithinStepsV2026
  rw [← scaled_args_eval b m k,
    show [mulScaledCalleeBody] = scaledCfg.callees from rfl,
    show addScaledCallerBody = scaledCfg.body from rfl, ← symProgEntry_toMachineState]
  exact not_reachesDoneWithinV2026_of_stepsTo_ge hSteps (Nat.le_refl 23)

/-! ### Companion: `wrapping_mul` + `bswap` -/

/-- 4-byte `u32` layout. -/
def u32Layout' : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- `u32`. -/
def u32Ty' : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- `u8` layout / type. -/
def u8Layout : TypeLayout :=
  { size := { bytes := 1 }
    align := { bytes := 1 }
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def u8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/--
```text
fn mix(x: u32, y: u32) -> u32 {
  // bb0: StorageLive(_3); _3 = core::intrinsics::wrapping_mul::<u32>(copy _1, copy _2) -> bb1
  // bb1: _0 = core::intrinsics::bswap::<u32>(move _3) -> bb2
  // bb2: StorageDead(_3); return
}
``` -/
def mixBody : CapturedMir :=
  { defPath := "mix::mix"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls := [decl u32Ty' "_0", decl u32Ty' "x", decl u32Ty' "y", decl u32Ty' "_3"]
    basicBlocks :=
      [ { statements := [st (.storageLive 3)]
          terminator := tm (.call (fnOp "core::intrinsics::wrapping_mul" [.uint .u32])
            [.copy (pl 1), .copy (pl 2)] (pl 3) (some 1) .continue_)
          isCleanup := false }
      , { statements := []
          terminator := tm (.call (fnOp "core::intrinsics::bswap" [.uint .u32])
            [.move (pl 3)] (pl 0) (some 2) .continue_)
          isCleanup := false }
      , { statements := [st (.storageDead 3)]
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u32Layout', mode := .direct }, { layout := u32Layout', mode := .direct }]
        ret := { layout := u32Layout', mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u32Layout'] }
    allocations := [] }

def mixCfg : SymConfig := { body := mixBody, callees := [] }

abbrev vx : SymScalar := .var 0 4
abbrev vy : SymScalar := .var 1 4
abbrev vxy : SymScalar := .wrappingOp .mul vx vy
abbrev mixRes : SymScalar := .bitIntrinsic .bswap vxy

def mixEntry : SymProg := symProgEntry mixCfg [.scalar vx, .scalar vy]

def mixFin : SymProg :=
  { frame := { blockIdx := 2, stmtIdx := 1, locals := [I mixRes, I vx, I vy, D] }
    stack := []
    active := none }

abbrev mixConds : List SymCond := [.widthsMatch vx vy, .widthNonzero vxy]

/-- One `rfl` chunk: 5 steps through two value-returning intrinsics. -/
theorem mix_chunk : symRunChunks mixCfg [5] mixEntry = .ret (.scalar mixRes) mixFin mixConds :=
  rfl

/-- Environment `[x, y]`. -/
def pairEnv (x y : Nat) : SymEnv
  | 0 => x
  | 1 => y
  | _ => 0

theorem mix_conds_hold (x y : Nat) : condsHold (pairEnv x y) mixConds :=
  ⟨⟨Nat.succ_ne_zero 3, rfl⟩, Nat.succ_ne_zero 3, trivial⟩

/-- Universal `mix` result: exactly the trusted `bswap (wrapping_mul x y)` kernel
composition, for all raw inputs. -/
theorem mix_symbolic (x y : Nat) :
    ExecWithinStepsV2026 mixBody [.scalar ⟨x, 4⟩, .scalar ⟨y, 4⟩] []
      (mirNormalPost (fun r _ => r = .scalar
        ((evalBswap ((evalWrappingMul ⟨x, 4⟩ ⟨y, 4⟩).getD symDefaultScalar)).getD
          symDefaultScalar))) 5 :=
  (symRunChunks_sound (post := mirNormalPost (fun r _ => r = .scalar
        ((evalBswap ((evalWrappingMul ⟨x, 4⟩ ⟨y, 4⟩).getD symDefaultScalar)).getD
          symDefaultScalar))) mix_chunk (pairEnv x y) (mix_conds_hold x y) rfl).2.1

/-- Concrete: `bswap(0x01020304 * 1) = 0x04030201`. -/
theorem mix_concrete :
    ExecWithinStepsV2026 mixBody [.scalar ⟨0x01020304, 4⟩, .scalar ⟨1, 4⟩] []
      (mirNormalPost (fun r _ => r = .scalar ⟨0x04030201, 4⟩)) 5 :=
  (symRunChunks_sound (post := mirNormalPost (fun r _ => r = .scalar ⟨0x04030201, 4⟩))
    mix_chunk (pairEnv 0x01020304 1) (mix_conds_hold _ _) rfl).2.1

/-! ### Companion: `addWithOverflow` + field proj + `!bool` + `cast .intToInt` + `deinit` + `aggregate` + `discriminant` -/

/-- `(u32, bool)` tuple layout / type. -/
def pairU32BoolLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr := .scalarPair (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
      (.initialized (.int 8 false) { start := 0, end_ := 1 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false }

def pairU32BoolTy : Ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 3 }
def u64Ty : Ty := { kind := .uint .u64, layoutIdx := 2 }

/--
```text
fn checked_add_cast(a: u32, b: u32) -> u64 {
  // bb0: StorageLive(_3); _3 = AddWithOverflow(copy _1, copy _2);
  //      StorageLive(_4); _4 = Not(copy (_3.1));
  //      assert(move _4, expected = true) -> bb1
  // bb1: StorageLive(_5); _5 = (copy (_3.0)) as u64;
  //      StorageLive(_6); _6 = (copy _5,);
  //      StorageLive(_7); _7 = discriminant(_6);
  //      _0 = Add(move _5, move _7);
  //      Deinit(_6); StorageDead(_7); StorageDead(_6); StorageDead(_5);
  //      StorageDead(_4); StorageDead(_3); return
}
``` -/
def checkedAddCastBody : CapturedMir :=
  { defPath := "checked_add_cast::checked_add_cast"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls :=
      [ decl u64Ty "_0", decl u32Ty' "a", decl u32Ty' "b"
      , decl pairU32BoolTy "_3", decl boolTy "_4", decl u64Ty "_5"
      , decl { kind := .tuple [.uint .u64], layoutIdx := 2 } "_6", decl u64Ty "_7" ]
    basicBlocks :=
      [ { statements :=
            [ st (.storageLive 3)
            , st (.assign (pl 3) (.binaryOp .addWithOverflow (.copy (pl 1)) (.copy (pl 2))))
            , st (.storageLive 4)
            , st (.assign (pl 4) (.unaryOp .not (.copy { local_ := 3, projection := [.field 1 boolTy] }))) ]
          terminator := tm (.assert (.move (pl 4)) true 1 .unreachable)
          isCleanup := false }
      , { statements :=
            [ st (.storageLive 5)
            , st (.assign (pl 5) (.cast .intToInt (.copy { local_ := 3, projection := [.field 0 u32Ty'] }) u64Ty))
            , st (.storageLive 6)
            , st (.assign (pl 6) (.aggregate .tuple [.copy (pl 5)]))
            , st (.storageLive 7)
            , st (.assign (pl 7) (.discriminant (pl 6)))
            , st (.assign (pl 0) (.binaryOp .add (.move (pl 5)) (.move (pl 7))))
            , st (.deinit (pl 6))
            , st (.storageDead 7), st (.storageDead 6), st (.storageDead 5)
            , st (.storageDead 4), st (.storageDead 3) ]
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u32Layout', mode := .direct }, { layout := u32Layout', mode := .direct }]
        ret := { layout := usizeLayout, mode := .direct }
        conv := .rust
        canUnwind := false }
    layouts :=
      { pointerBits := 64, isLittleEndian := true
        entries := [u32Layout', boolLayout, usizeLayout, pairU32BoolLayout] }
    allocations := [] }

def checkedAddCastCfg : SymConfig := { body := checkedAddCastBody, callees := [] }

abbrev vcaVal : SymScalar := .checkedVal .add false vx vy
abbrev vcaFlg : SymScalar := .checkedFlag .add false vx vy
abbrev vcaNot : SymScalar := .unaryOp .notBool vcaFlg
abbrev vcaWide : SymScalar := .castInt false 8 vcaVal
abbrev vcaSum : SymScalar := .binOp .add false vcaWide (.const ⟨0, 8⟩)

def checkedAddCastEntry : SymProg := symProgEntry checkedAddCastCfg [.scalar vx, .scalar vy]

def checkedAddCastCp1 : SymProg :=
  { frame :=
      { blockIdx := 1, stmtIdx := 0
        locals := [U, I vx, I vy, .init (.aggregate 0 [vcaVal, vcaFlg]), U, D, D, D] }
    stack := [], active := none }

def checkedAddCastCp2 : SymProg :=
  { frame :=
      { blockIdx := 1, stmtIdx := 7
        locals := [I vcaSum, I vx, I vy, .init (.aggregate 0 [vcaVal, vcaFlg]), U, U,
                   .init (.aggregate 0 [vcaWide]), U] }
    stack := [], active := none }

def checkedAddCastFin : SymProg :=
  { frame := { blockIdx := 1, stmtIdx := 13, locals := [I vcaSum, I vx, I vy, D, D, D, D, D] }
    stack := [], active := none }

abbrev checkedAddCastConds : List SymCond :=
  [ .widthsMatch vx vy
  , .validBool vcaFlg
  , .assertHolds vcaNot true
  , .widthNonzero vcaVal
  , .widthsMatch vcaWide (.const ⟨0, 8⟩) ]

/-- Chunk 1 (5 steps): `addWithOverflow`, field `.1` proj, `!bool`, `assert`. -/
theorem checkedAddCast_chunk1 :
    symProgRunSteps checkedAddCastCfg 5 checkedAddCastEntry =
      .step checkedAddCastCp1 [.widthsMatch vx vy, .validBool vcaFlg, .assertHolds vcaNot true] :=
  rfl

/-- Chunk 2 (7 steps): field `.0` proj, `cast .intToInt`, `aggregate`,
`discriminant`, `binaryOp .add`. -/
theorem checkedAddCast_chunk2 :
    symProgRunSteps checkedAddCastCfg 7 checkedAddCastCp1 =
      .step checkedAddCastCp2 [.widthNonzero vcaVal, .widthsMatch vcaWide (.const ⟨0, 8⟩)] := rfl

/-- Chunk 3 (7 steps): `deinit`, `StorageDead`s, `return`. -/
theorem checkedAddCast_chunk3 :
    symProgRunSteps checkedAddCastCfg 7 checkedAddCastCp2 =
      .ret (.scalar vcaSum) checkedAddCastFin [] := rfl

/-- Full 19-step pipeline in 3 `rfl` chunks `[5, 7, 7]` exercising
`addWithOverflow`, field projections, `unaryOp .not` on `bool`, `assert`,
`cast .intToInt`, `aggregate`, `discriminant`, `binaryOp .add`, and `deinit`. -/
theorem checkedAddCast_chunk :
    symRunChunks checkedAddCastCfg [5, 7, 7] checkedAddCastEntry =
      .ret (.scalar vcaSum) checkedAddCastFin checkedAddCastConds := by
  rw [symRunChunks_eq]
  exact symProgRunSteps_trans checkedAddCast_chunk1
    (symProgRunSteps_trans checkedAddCast_chunk2 checkedAddCast_chunk3)

abbrev M32 : Nat := scalarModulus 4

/-- Universal `checked_add_cast`: for all `a, b : Nat` with `a + b < 2^32`,
returns `a + b` as `u64` within 19 steps (choice-free). -/
theorem checkedAddCast_symbolic {a b : Nat} (hab : a + b < M32) :
    ExecWithinStepsV2026 checkedAddCastBody [.scalar ⟨a, 4⟩, .scalar ⟨b, 4⟩] []
      (mirNormalPost (fun r _ => r = .scalar ⟨a + b, 8⟩)) 19 := by
  have hlt64 : a + b < M64 := Nat.lt_trans hab (by decide : M32 < M64)
  have hSum : Nat.add a b < scalarModulus 4 := hab
  have hBle : Nat.ble (scalarModulus 4) (Nat.add a b) = false := nat_ble_false_of_lt hSum
  have hEvalVal : vcaVal.eval (pairEnv a b) = ⟨a + b, 4⟩ := by
    rw [SymScalar.eval_checkedVal, SymScalar.eval_var, SymScalar.eval_var]
    show (some { bits := wrapScalarBits (Nat.add a b) (scalarModulus 4), sizeBytes := 4 }).getD
      symDefaultScalar = _
    rw [wrapScalarBits_of_lt hSum]
    rfl
  have hEvalFlg : vcaFlg.eval (pairEnv a b) = ⟨0, 1⟩ := by
    rw [SymScalar.eval_checkedFlag, SymScalar.eval_var, SymScalar.eval_var]
    show (some (ScalarInt.mk
      (match Nat.ble (scalarModulus 4) (Nat.add a b) with | true => 1 | false => 0) 1)).getD
      symDefaultScalar = _
    rw [hBle]
    rfl
  have hEvalNot : vcaNot.eval (pairEnv a b) = ⟨1, 1⟩ := by
    rw [SymScalar.eval_unaryOp, hEvalFlg]; rfl
  have hEvalWide : vcaWide.eval (pairEnv a b) = ⟨a + b, 8⟩ := by
    rw [SymScalar.eval_castInt, hEvalVal]
    unfold symCastIntEval
    dsimp only
    rw [wrapScalarBits_of_lt hlt64]
  have hEvalSum : vcaSum.eval (pairEnv a b) = ⟨a + b, 8⟩ := by
    rw [SymScalar.eval_binOp, hEvalWide, SymScalar.eval_const]
    show (some { bits := wrapScalarBits ((a + b) + 0) (scalarModulus 8), sizeBytes := 8 }).getD
      symDefaultScalar = _
    rw [Nat.add_zero, wrapScalarBits_of_lt hlt64]
    rfl
  have hConds : condsHold (pairEnv a b) checkedAddCastConds := by
    refine ⟨⟨Nat.succ_ne_zero 3, rfl⟩, ?_, ?_, ?_, ?_, trivial⟩
    · dsimp only [SymCond.holds]; rw [hEvalFlg]; exact ⟨rfl, Or.inl rfl⟩
    · dsimp only [SymCond.holds]; rw [hEvalNot]
    · dsimp only [SymCond.holds]; rw [hEvalVal]; exact Nat.succ_ne_zero 3
    · dsimp only [SymCond.holds]; rw [hEvalWide]; exact ⟨eight_ne_zero, rfl⟩
  have hPost : mirNormalPost (fun r _ => r = .scalar ⟨a + b, 8⟩)
      (.normal ((SymVal.scalar vcaSum).eval (pairEnv a b),
        (checkedAddCastFin.toMachineState checkedAddCastCfg (pairEnv a b)).memory)) := by
    show Value.scalar (vcaSum.eval (pairEnv a b)) = .scalar ⟨a + b, 8⟩
    rw [hEvalSum]
  exact (symRunChunks_sound checkedAddCast_chunk (pairEnv a b) hConds hPost).2.1

/-! ### Symbolic `SwitchInt` fork (`SymStepRes.branch`) -/

/--
```text
fn sel(x: u8) -> u8 {
  // bb0: switchInt(copy _1) [0 -> bb1, otherwise -> bb2]
  // bb1: _0 = const 1_u8; return
  // bb2: _0 = copy _1; return
}
``` -/
def selBody : CapturedMir :=
  { defPath := "sel::sel"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls := [decl u8Ty "_0", decl u8Ty "x"]
    basicBlocks :=
      [ { statements := []
          terminator := tm (.switchInt (.copy (pl 1)) { branches := [(0, 1)], otherwise := 2 })
          isCleanup := false }
      , { statements := [st (.assign (pl 0) (.use (.constant
            { ty := u8Ty, val := .scalar (.int ⟨1, 1⟩) })))]
          terminator := tm .return_
          isCleanup := false }
      , { statements := [st (.assign (pl 0) (.use (.copy (pl 1))))]
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u8Layout, mode := .direct }]
        ret := { layout := u8Layout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u8Layout] }
    allocations := [] }

def selCfg : SymConfig := { body := selBody, callees := [] }

abbrev vs : SymScalar := .var 0 1

def selEntry : SymProg := symProgEntry selCfg [.scalar vs]

def selZero : SymProg := selEntry.jump 1 [U, I vs]
def selOther : SymProg := selEntry.jump 2 [U, I vs]

/-- The symbolic step forks on the symbolic discriminant with first-match
edge conditions. -/
theorem sel_fork :
    symProgRunSteps selCfg 1 selEntry =
      .branch [(.switchBranchEq vs 0 [], selZero), (.switchBranchOtherwise vs [0], selOther)] [] :=
  rfl

theorem sel_zero_run :
    symProgRunSteps selCfg 2 selZero =
      .ret (.concrete (.scalar ⟨1, 1⟩))
        { frame := { blockIdx := 1, stmtIdx := 1
                     locals := [.init (.concrete (.scalar ⟨1, 1⟩)), I vs] }
          stack := []
          active := none } [] := rfl

theorem sel_other_run :
    symProgRunSteps selCfg 2 selOther =
      .ret (.scalar vs)
        { frame := { blockIdx := 2, stmtIdx := 1, locals := [I vs, I vs] }
          stack := []
          active := none } [] := rfl

def selEnv (x : Nat) : SymEnv := fun _ => x

/-- Path-split verification of `sel` for every `u8` input: both edges are
discharged through `symProgRunSteps_branch_sound`. -/
theorem sel_symbolic (x : Nat) :
    ExecWithinStepsV2026 selBody [.scalar ⟨x, 1⟩] []
      (mirNormalPost (fun r _ => r = .scalar ⟨match x with | 0 => 1 | n + 1 => n + 1, 1⟩)) 3 := by
  obtain ⟨j, fork, hj, hsteps, halts⟩ :=
    symProgRunSteps_branch_sound selCfg (selEnv x) 1 sel_fork trivial
  have hj0 : j = 0 := Nat.le_zero.mp (Nat.le_of_succ_le_succ hj)
  subst hj0
  have hfork := StepsToV2026.deterministic hsteps (StepsToV2026.refl _)
  rw [hfork] at halts
  unfold ExecWithinStepsV2026
  rw [show [Value.scalar ⟨x, 1⟩] = symValsEval (selEnv x) [.scalar vs] from rfl,
    show selBody = selCfg.body from rfl, show ([] : List CapturedMir) = selCfg.callees from rfl,
    ← symProgEntry_toMachineState]
  cases x with
  | zero =>
    have hstep := halts _ _ (List.Mem.head _) ⟨rfl, fun _ h => nomatch h⟩
    exact reachesDoneWithinV2026_of_step hstep
      (symProgRunSteps_ret_sound sel_zero_run (selEnv 0) trivial rfl)
  | succ n =>
    have hstep := halts _ _ (List.Mem.tail _ (List.Mem.head _))
      (fun u hu => by
        cases hu with
        | head => exact Nat.succ_ne_zero n
        | tail _ h => nomatch h)
    exact reachesDoneWithinV2026_of_step hstep
      (symProgRunSteps_ret_sound sel_other_run (selEnv (n + 1)) trivial rfl)

/-- The fork step emits EXACTLY the trusted `SwitchInt` `.vis` event carrying the
symbolic discriminant (`symProgStep_branch_sound_obs`). -/
theorem sel_step_branch :
    symProgStep selCfg selEntry =
      .branch [(.switchBranchEq vs 0 [], selZero), (.switchBranchOtherwise vs [0], selOther)] [] :=
  rfl

theorem sel_obs : symProgObs selCfg selEntry = .event vs := rfl

theorem sel_emits_event_zero :
    stepMirFn selBody (initMachineStateWithCallees selBody [.scalar ⟨0, 1⟩] []) =
      MirStepNode.emitStep (.event 0) (selZero.toMachineState selCfg (selEnv 0)) :=
  symProgStep_branch_sound_obs sel_step_branch (selEnv 0) _ _ (List.Mem.head _)
    ⟨rfl, fun _ h => nomatch h⟩

theorem sel_emits_event_succ (n : Nat) :
    stepMirFn selBody (initMachineStateWithCallees selBody [.scalar ⟨n + 1, 1⟩] []) =
      MirStepNode.emitStep (.event (n + 1)) (selOther.toMachineState selCfg (selEnv (n + 1))) :=
  symProgStep_branch_sound_obs sel_step_branch (selEnv (n + 1)) _ _
    (List.Mem.tail _ (List.Mem.head _))
    (fun u hu => by
      cases hu with
      | head => exact Nat.succ_ne_zero n
      | tail _ h => nomatch h)

/-! ## Pillar 2: Bounded Loop via `StepBoundV2026` + `CnfOrd.Worklist` + `WlpV2026` -/

/--
```text
fn countdown(n: u32) -> u32 {
  // bb0: _0 = const 0_u32; goto bb1
  // bb1: switchInt(copy _1) [0 -> bb3, otherwise -> bb2]       (observable `.vis` step)
  // bb2: _1 = Sub(copy _1, const 1_u32); _0 = Add(copy _0, const 2_u32); goto bb1
  // bb3: return
}
``` -/
def cdBody : CapturedMir :=
  { defPath := "countdown::countdown"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls := [decl u32Ty' "_0", decl u32Ty' "n"]
    basicBlocks :=
      [ { statements := [st (.assign (pl 0) (.use (.constant
            { ty := u32Ty', val := .scalar (.int ⟨0, 4⟩) })))]
          terminator := tm (.goto 1)
          isCleanup := false }
      , { statements := []
          terminator := tm (.switchInt (.copy (pl 1)) { branches := [(0, 3)], otherwise := 2 })
          isCleanup := false }
      , { statements :=
            [ st (.assign (pl 1) (.binaryOp .sub (.copy (pl 1))
                (.constant { ty := u32Ty', val := .scalar (.int ⟨1, 4⟩) })))
            , st (.assign (pl 0) (.binaryOp .add (.copy (pl 0))
                (.constant { ty := u32Ty', val := .scalar (.int ⟨2, 4⟩) }))) ]
          terminator := tm (.goto 1)
          isCleanup := false }
      , { statements := []
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u32Layout', mode := .direct }]
        ret := { layout := u32Layout', mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u32Layout'] }
    allocations := [] }

def cdInit : MachineState := initMachineStateWithCallees cdBody [.scalar ⟨3, 4⟩] []

/-- Loop head `bb1` with accumulator `acc` and counter `i`. -/
def cdHead (acc i : Nat) : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0
               locals := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨i, 4⟩)] }
    memory := cdInit.memory }

/-- Exit block `bb3`. -/
def cdExit (acc : Nat) : MachineState :=
  { frame := { blockIdx := 3, stmtIdx := 0
               locals := [.init (.scalar ⟨acc, 4⟩), .init (.scalar ⟨0, 4⟩)] }
    memory := cdInit.memory }

theorem cd_pre : StepsToV2026 cdBody 2 cdInit (cdHead 0 3) := .step rfl (.single rfl)
theorem cd_iter3 : StepsToV2026 cdBody 4 (cdHead 0 3) (cdHead 2 2) :=
  .step rfl (.step rfl (.step rfl (.single rfl)))
theorem cd_iter2 : StepsToV2026 cdBody 4 (cdHead 2 2) (cdHead 4 1) :=
  .step rfl (.step rfl (.step rfl (.single rfl)))
theorem cd_iter1 : StepsToV2026 cdBody 4 (cdHead 4 1) (cdHead 6 0) :=
  .step rfl (.step rfl (.step rfl (.single rfl)))
theorem cd_exit_step : v2026Step cdBody (cdHead 6 0) = .step (cdExit 6) := rfl
theorem cd_exit_done :
    v2026Step cdBody (cdExit 6) = .done (.normal (.scalar ⟨6, 4⟩, cdInit.memory)) := rfl

/-- The loop-head `switchInt` is an observable `.vis` emission step. -/
theorem cd_switch_observable :
    stepMirFn cdBody (cdHead 6 0) = MirStepNode.emitStep (.event 0) (cdExit 6) := rfl

abbrev cdPost : MirOutcome → Prop := mirNormalPost (fun r _ => r = .scalar ⟨6, 4⟩)

/-- Countdown invariant `Inv i` (loop head with `i` iterations left). -/
def cdInv : Nat → MachineState → Prop
  | 0, st => st = cdHead 6 0
  | 1, st => st = cdHead 4 1
  | 2, st => st = cdHead 2 2
  | 3, st => st = cdHead 0 3
  | _, _ => False

theorem cd_exit_reach : ReachesDoneWithinV2026 cdBody cdPost 2 (cdHead 6 0) :=
  reachesDoneWithinV2026_of_step cd_exit_step (reachesDoneWithinV2026_of_done cd_exit_done rfl)

/-- **Pass 1 (quantitative step bound & safety):** `v2026_loop_countdown` with
body bound `4` and exit bound `2`. -/
theorem cd_pass1_loop : ReachesDoneWithinV2026 cdBody cdPost (3 * 4 + 2) (cdHead 0 3) := by
  refine v2026_loop_countdown cdInv 4 2 (fun st h => by subst h; exact cd_exit_reach)
    (fun n st hn => ?_) 3 _ rfl
  cases n with
  | zero =>
    subst hn
    exact Or.inr (BoundedReachV2026.of_exact (Nat.le_refl 4) cd_iter1 rfl)
  | succ n1 =>
    cases n1 with
    | zero =>
      subst hn
      exact Or.inr (BoundedReachV2026.of_exact (Nat.le_refl 4) cd_iter2 rfl)
    | succ n2 =>
      cases n2 with
      | zero =>
        subst hn
        exact Or.inr (BoundedReachV2026.of_exact (Nat.le_refl 4) cd_iter3 rfl)
      | succ _ => exact False.elim hn

theorem cd_exec16 : ExecWithinStepsV2026 cdBody [.scalar ⟨3, 4⟩] [] cdPost 16 :=
  reachesDoneWithinV2026_of_stepsTo cd_pre cd_pass1_loop

/-- Tight step budget: exactly `16` steps (`15` is refuted). -/
theorem cd_steps15 : StepsToV2026 cdBody 15 cdInit (cdExit 6) :=
  cd_pre.trans (cd_iter3.trans (cd_iter2.trans (cd_iter1.trans (StepsToV2026.single cd_exit_step))))

theorem cd_not15 : ¬ ExecWithinStepsV2026 cdBody [.scalar ⟨3, 4⟩] [] cdPost 15 :=
  not_reachesDoneWithinV2026_of_stepsTo_ge cd_steps15 (Nat.le_refl 15)

open Anneal.CnfOrd in
/-- **Worklist termination bridge:** a `towerLookupNext` worklist simulation
(`w0 → w1 → w2`, two loop iterations per worklist step) yields a step bound
through `v2026_steps_of_worklist_terminates`. -/
theorem cd_worklist :
    ∃ steps : Nat, ReachesDoneWithinV2026 cdBody cdPost (steps * 8 + 2) (cdHead 0 3) := by
  let pol : SpawnPolicy := towerLookupNext [1, 0] 1 0
  have hPol : PolicyAdmissible pol := towerLookupNext_admissible [1, 0] 1 0 rfl
  let w0 : WorklistPool :=
    { fifoQueue := [RankedTask.mk 0 1 0], stealDeque := [], nextTaskId := 1,
      completedCount := 0, stepCount := 0 }
  let w1 : WorklistPool :=
    { fifoQueue := [], stealDeque := [RankedTask.mk 1 0 0], nextTaskId := 2,
      completedCount := 1, stepCount := 1 }
  let w2 : WorklistPool :=
    { fifoQueue := [], stealDeque := [], nextTaskId := 2, completedCount := 2, stepCount := 2 }
  let simW : WorklistPool → MachineState → Prop :=
    fun w st => (w = w0 ∧ st = cdHead 0 3) ∨ (w = w1 ∧ st = cdHead 4 1) ∨
      (w = w2 ∧ st = cdHead 6 0)
  refine v2026_steps_of_worklist_terminates pol hPol simW 8 2
    (fun w st hEmp hSim => ?_) (fun w w' st hNe hSt hSim => ?_) w0 (cdHead 0 3)
    (Or.inl ⟨rfl, rfl⟩)
  · rcases hSim with h0 | h1 | h2
    · rw [h0.1] at hEmp; cases hEmp
    · rw [h1.1] at hEmp; cases hEmp
    · rw [h2.2]; exact cd_exit_reach
  · rcases hSim with h0 | h1 | h2
    · rw [h0.1] at hSt
      have hEq : worklistStep pol w0 = .returned w1 := rfl
      rw [hEq] at hSt
      injection hSt with hW'
      subst hW'
      rw [h0.2]
      exact BoundedReachV2026.of_exact (Nat.le_refl 8) (cd_iter3.trans cd_iter2)
        (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rw [h1.1] at hSt
      have hEq : worklistStep pol w1 = .returned w2 := rfl
      rw [hEq] at hSt
      injection hSt with hW'
      subst hW'
      rw [h1.2]
      exact BoundedReachV2026.of_exact (Nat.le_add_right 4 4) cd_iter1
        (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · rw [h2.1] at hNe; cases hNe

/-- **Pass 2 (functional postcondition) via asymmetric two-pass splitting:**
a partial-correctness `wlpOutcomeV2026` proof at `fuelWlp = 20`, obtained by
prepending the sealed `StepStageCut` prefix onto the terminal `.done` rule, is
combined with the Pass-1 safety `wpStateV2026` at `fuelSafe = 16 ≤ 20`. -/
theorem cd_wlp : wlpOutcomeV2026 cdBody cdPost (fun _ => False) 20 cdInit :=
  wlpOutcomeV2026_of_stepStageCut cd_steps15.to_stepStageCut
    (wlpOutcomeV2026_done_eq (fuel := 19) cd_exit_done rfl)

theorem cd_safe : wpStateV2026 cdBody 16 cdInit (fun _ => True) :=
  reachesDoneWithinV2026_iff_wpStateV2026.mp
    (ReachesDoneWithinV2026.weaken (fun _ _ => trivial) cd_exec16)

theorem cd_pass2 : wpStateV2026 cdBody 16 cdInit cdPost :=
  wpStateV2026_of_wlp_and_safety_le (Nat.le_add_right 16 4) cd_wlp cd_safe

/-- Reflective `BoolCertCut` certificate that the loop output is `2 * n` for `n = 3`. -/
theorem cd_boolCert : BoolCertCut (fun n : Nat => Nat.beq (2 * n) 6) 3 :=
  BoolCertCut.seal _ _ rfl

theorem cd_verificationResult :
    VerificationResult
      { body := cdBody
        pre := fun args => args = [.scalar ⟨3, 4⟩]
        post := fun _ r => r = .scalar ⟨6, 4⟩ } := by
  refine verifyMirNoPanic_of_execWithinStepsV2026 _ (fun args hPre => ?_)
  subst hPre
  exact ⟨16, reachesDoneWithinV2026_iff_wpStateV2026.mpr cd_pass2⟩

theorem cd_statefulVerificationResult :
    StatefulVerificationResult
      { body := cdBody
        pre := fun args mem => args = [.scalar ⟨3, 4⟩] ∧ mem = cdInit.memory
        post := fun _ _ r _ => r = .scalar ⟨6, 4⟩ } := by
  refine verifyStatefulMirNoPanic_of_execWithinStepsV2026 _ (fun args mem hPre => ?_)
  obtain ⟨hArgs, hMem⟩ := hPre
  subst hArgs
  subst hMem
  exact ⟨16, cd_exec16⟩

/-! ### Universal `countdown(n)` for ALL `2 * n < 2^32` (Symbolic Loop Body + `StepBoundV2026` + `WlpV2026` + Active `BoolCertCut`) -/

def cdCfg : SymConfig := { body := cdBody, callees := [] }

abbrev vcdAcc : SymScalar := .var 0 4
abbrev vcdI : SymScalar := .var 1 4
abbrev vcdSub : SymScalar := .binOp .sub false vcdI (.const ⟨1, 4⟩)
abbrev vcdAdd : SymScalar := .binOp .add false vcdAcc (.const ⟨2, 4⟩)

def cdSymEntry : SymProg := symProgEntry cdCfg [.scalar vcdI]
def cdSymHead (acc i : SymScalar) : SymProg :=
  { frame := { blockIdx := 1, stmtIdx := 0, locals := [I acc, I i] }, stack := [], active := none }
def cdSymBodyStart : SymProg :=
  { frame := { blockIdx := 2, stmtIdx := 0, locals := [I vcdAcc, I vcdI] }, stack := [], active := none }

/-- Symbolic 2-step entry prefix of `countdown(n)` for arbitrary `n` (`rfl`). -/
theorem cd_sym_pre :
    symProgRunSteps cdCfg 2 cdSymEntry =
      .step { frame := { blockIdx := 1, stmtIdx := 0
                         locals := [.init (.concrete (.scalar ⟨0, 4⟩)), I vcdI] }
              stack := [], active := none } [] := rfl

/-- Symbolic 3-step loop body (`bb2 -> bb1`) for arbitrary `(acc, i)` (`rfl`),
exercising `symRvalue (.binaryOp .sub)` and `symRvalue (.binaryOp .add)`. -/
theorem cd_sym_body :
    symProgRunSteps cdCfg 3 cdSymBodyStart =
      .step (cdSymHead vcdAdd vcdSub)
        [.widthsMatch vcdI (.const ⟨1, 4⟩), .widthsMatch vcdAcc (.const ⟨2, 4⟩)] := rfl

/-- Load-bearing reflective `BoolCertCut`: the computable static checker
`condsStatic` certifies the loop-body side conditions for EVERY environment
(consumed by `cd_iter_forall` through `condsHold_of_boolCert`). -/
theorem cd_body_condsCert :
    BoolCertCut condsStatic [.widthsMatch vcdI (.const ⟨1, 4⟩), .widthsMatch vcdAcc (.const ⟨2, 4⟩)] :=
  BoolCertCut.seal _ _ rfl

/-- Symbolic 1-step entry `cdInit n → cdHead 0 n` for every `n : Nat`. -/
theorem cd_pre_forall (n : Nat) :
    StepsToV2026 cdBody 2 (initMachineStateWithCallees cdBody [.scalar ⟨n, 4⟩] [])
      (cdHead 0 n) := by
  have h := symProgRunSteps_sound cdCfg (pairEnv 0 n) 2 cd_sym_pre trivial
  unfold cdSymEntry at h
  rw [symProgEntry_toMachineState] at h
  exact h

/-- Observable `.vis` loop-head `switchInt` step for `i = k + 1` (stays in loop). -/
theorem cd_head_step_succ (acc k : Nat) :
    v2026Step cdBody (cdHead acc (k + 1)) =
      .step (cdSymBodyStart.toMachineState cdCfg (pairEnv acc (k + 1))) := rfl

/-- Observable `.vis` loop-head `switchInt` exit step for `i = 0`. -/
theorem cd_head_step_zero (acc : Nat) :
    v2026Step cdBody (cdHead acc 0) = .step (cdExit acc) := rfl

/-- Terminal return step at `bb3` for any accumulator `acc`. -/
theorem cd_exit_done_forall (acc : Nat) :
    v2026Step cdBody (cdExit acc) = .done (.normal (.scalar ⟨acc, 4⟩, cdInit.memory)) := rfl

/-- One full 4-step loop iteration `cdHead acc (k + 1) →⁴ cdHead (acc + 2) k`
for EVERY `acc, k` without `u32` overflow, proved via `cd_sym_body` +
`symProgRunSteps_sound`. -/
theorem cd_iter_forall (acc k : Nat) (hacc : acc + 2 < M32) (hk : k < M32) :
    StepsToV2026 cdBody 4 (cdHead acc (k + 1)) (cdHead (acc + 2) k) := by
  have hConds := condsHold_of_boolCert cd_body_condsCert (pairEnv acc (k + 1))
  have hBody := symProgRunSteps_sound cdCfg (pairEnv acc (k + 1)) 3 cd_sym_body hConds
  have hSub : vcdSub.eval (pairEnv acc (k + 1)) = ⟨k, 4⟩ := by
    rw [SymScalar.eval_binOp, SymScalar.eval_var, SymScalar.eval_const]
    have hle : Nat.ble 1 (k + 1) = true := Nat.ble_eq_true_of_le (Nat.succ_le_succ (Nat.zero_le k))
    show (match (match Nat.ble 1 (k + 1) with
      | true => RvalueEvalResult.ok (.scalar ⟨wrapScalarBits (Nat.sub (k + 1) 1) (scalarModulus 4), 4⟩)
          [] emptyMemory
      | false => RvalueEvalResult.ok (.scalar ⟨wrapScalarBits (Nat.sub (Nat.add (scalarModulus 4)
          (wrapScalarBits (k + 1) (scalarModulus 4))) (wrapScalarBits 1 (scalarModulus 4)))
          (scalarModulus 4), 4⟩) [] emptyMemory) with
      | .ok (.scalar sc) _ _ => some sc | _ => none).getD symDefaultScalar = _
    rw [hle]
    have hsub1 : Nat.sub (k + 1) 1 = k := Nat.add_sub_cancel k 1
    dsimp only
    rw [hsub1, wrapScalarBits_of_lt hk]
    rfl
  have hAdd : vcdAdd.eval (pairEnv acc (k + 1)) = ⟨acc + 2, 4⟩ := by
    rw [SymScalar.eval_binOp, SymScalar.eval_var, SymScalar.eval_const]
    show (some { bits := wrapScalarBits (acc + 2) (scalarModulus 4), sizeBytes := 4 }).getD
      symDefaultScalar = _
    rw [wrapScalarBits_of_lt hacc]
    rfl
  have hEnd : (cdSymHead vcdAdd vcdSub).toMachineState cdCfg (pairEnv acc (k + 1)) =
      cdHead (acc + 2) k := by
    unfold cdSymHead cdHead SymProg.toMachineState SymFrame.eval symSlotsEval SymSlot.eval
      SymVal.eval
    simp only [List.map, hAdd, hSub]
    rfl
  rw [hEnd] at hBody
  exact StepsToV2026.step (cd_head_step_succ acc k) hBody

/-- Multi-iteration exact trace: `k` iterations from `cdHead acc k` reach
`cdHead (acc + 2 * k) 0` in exactly `4 * k` steps. -/
theorem cd_iters_exact :
    ∀ (k acc : Nat), acc + 2 * k < M32 →
      StepsToV2026 cdBody (4 * k) (cdHead acc k) (cdHead (acc + 2 * k) 0)
  | 0, acc, _ => StepsToV2026.refl _
  | k + 1, acc, hB => by
    have h2 : acc + 2 * (k + 1) = (acc + 2) + 2 * k := by
      rw [Nat.mul_succ, ← Nat.add_assoc, Nat.add_right_comm acc (2 * k) 2]
    have hacc2 : acc + 2 < M32 :=
      Nat.lt_of_le_of_lt (Nat.le_add_right (acc + 2) (2 * k)) (h2 ▸ hB)
    have hk2 : k ≤ 2 * k := by
      have : 1 * k ≤ 2 * k := Nat.mul_le_mul_right k (Nat.succ_le_succ (Nat.zero_le 1))
      rw [Nat.one_mul] at this
      exact this
    have hklt : k < M32 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hk2 (Nat.le_add_left (2 * k) (acc + 2))) (h2 ▸ hB)
    have h1 := cd_iter_forall acc k hacc2 hklt
    have hrest := cd_iters_exact k (acc + 2) (h2 ▸ hB)
    have htot := h1.trans hrest
    have h4 : 4 + 4 * k = 4 * (k + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    rw [h4, ← h2] at htot
    exact htot

/-- **Universal Pass 1 (quantitative step bound & safety via `v2026_loop_countdown`)**:
for ALL `n : Nat` with `2 * n < 2^32`, `countdown(n)` reaches `2 * n` in
`n * 4 + 2` steps from the loop head (`4 * n + 4` from entry). -/
theorem cd_pass1_forall (n : Nat) (hn : 2 * n < M32) :
    ExecWithinStepsV2026 cdBody [.scalar ⟨n, 4⟩] []
      (mirNormalPost (fun r _ => r = .scalar ⟨2 * n, 4⟩)) (n * 4 + 4) := by
  let inv : Nat → MachineState → Prop :=
    fun i st => i ≤ n ∧ st = cdHead (2 * (n - i)) i
  have hExit : ∀ st, inv 0 st →
      ReachesDoneWithinV2026 cdBody (mirNormalPost (fun r _ => r = .scalar ⟨2 * n, 4⟩)) 2 st := by
    intro st ⟨_, hst⟩
    rw [hst, Nat.sub_zero]
    exact reachesDoneWithinV2026_of_step (cd_head_step_zero (2 * n))
      (reachesDoneWithinV2026_of_done (cd_exit_done_forall (2 * n)) rfl)
  have hStep : ∀ k st, inv (k + 1) st →
      ReachesDoneWithinV2026 cdBody (mirNormalPost (fun r _ => r = .scalar ⟨2 * n, 4⟩)) 2 st ∨
        BoundedReachV2026 cdBody (inv k) 4 st := by
    intro k st ⟨hkLe, hst⟩
    right
    rw [hst]
    have hsub : n - k = (n - (k + 1)) + 1 := by
      have h1 : k < n := hkLe
      have h2 := Nat.sub_add_cancel (Nat.le_of_lt h1)
      have h3 : (n - (k + 1)) + (k + 1) = n := Nat.sub_add_cancel hkLe
      have h4 : ((n - (k + 1)) + 1) + k = (n - k) + k := by
        rw [Nat.add_assoc, Nat.add_comm 1 k, h3, h2]
      exact (Nat.add_right_cancel h4).symm
    have hmul : 2 * (n - (k + 1)) + 2 = 2 * (n - k) := by
      rw [hsub, Nat.mul_succ]
    have hacc2 : 2 * (n - (k + 1)) + 2 < M32 := by
      rw [hmul]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.sub_le n k)) hn
    have hklt : k < M32 := by
      have hkn : k ≤ n := Nat.le_of_lt hkLe
      have h1n : n ≤ 2 * n := by
        have := Nat.mul_le_mul_right n (Nat.succ_le_succ (Nat.zero_le 1))
        rw [Nat.one_mul] at this; exact this
      exact Nat.lt_of_le_of_lt (Nat.le_trans hkn h1n) hn
    have hIter := cd_iter_forall (2 * (n - (k + 1))) k hacc2 hklt
    rw [hmul] at hIter
    exact BoundedReachV2026.of_exact (Nat.le_refl 4) hIter ⟨Nat.le_of_lt hkLe, rfl⟩
  have hLoop := v2026_loop_countdown inv 4 2 hExit hStep n (cdHead 0 n)
    ⟨Nat.le_refl n, by rw [Nat.sub_self]⟩
  have hTot := reachesDoneWithinV2026_of_stepsTo (cd_pre_forall n) hLoop
  have hAdd : 2 + (n * 4 + 2) = n * 4 + 4 := by
    rw [Nat.add_comm 2 (n * 4 + 2), Nat.add_assoc]
  rw [hAdd] at hTot
  exact hTot

/-- **Universal tight budget**: for ALL `n` with `2 * n < 2^32`, `n * 4 + 3`
steps are insufficient (strictly 1 step short of `n * 4 + 4`). -/
theorem cd_not_tight_forall (n : Nat) (hn : 2 * n < M32) (post : MirOutcome → Prop) :
    ¬ ExecWithinStepsV2026 cdBody [.scalar ⟨n, 4⟩] [] post (n * 4 + 3) := by
  have hPre := cd_pre_forall n
  have hIters := cd_iters_exact n 0 (by rw [Nat.zero_add]; exact hn)
  rw [Nat.zero_add] at hIters
  have hSteps := hPre.trans (hIters.trans (StepsToV2026.single (cd_head_step_zero (2 * n))))
  have hEq : 2 + (4 * n + 1) = n * 4 + 3 := by
    rw [Nat.mul_comm 4 n, Nat.add_comm 2 (n * 4 + 1), Nat.add_assoc]
  rw [hEq] at hSteps
  exact not_reachesDoneWithinV2026_of_stepsTo_ge hSteps (Nat.le_refl (n * 4 + 3))

/-- **Universal Pass 2 (asymmetric two-pass splitting via `WlpV2026` +
`StepStageCut` + active `BoolCertCut`)**: for ALL `n` with `2 * n < 2^32`,
combines `wlpOutcomeV2026` at `fuelWlp = n * 4 + 8` with Pass-1 safety at
`fuelSafe = n * 4 + 4 ≤ n * 4 + 8`. -/
theorem cd_pass2_forall (n : Nat) (hn : 2 * n < M32) :
    wpStateV2026 cdBody (n * 4 + 4) (initMachineStateWithCallees cdBody [.scalar ⟨n, 4⟩] [])
      (mirNormalPost (fun r _ => r = .scalar ⟨2 * n, 4⟩)) := by
  have hPre := cd_pre_forall n
  have hIters := cd_iters_exact n 0 (by rw [Nat.zero_add]; exact hn)
  rw [Nat.zero_add] at hIters
  have hSteps := hPre.trans (hIters.trans (StepsToV2026.single (cd_head_step_zero (2 * n))))
  have hEq : 2 + (4 * n + 1) = n * 4 + 3 := by
    rw [Nat.mul_comm 4 n, Nat.add_comm 2 (n * 4 + 1), Nat.add_assoc]
  rw [hEq] at hSteps
  have hWlp : wlpOutcomeV2026 cdBody (mirNormalPost (fun r _ => r = .scalar ⟨2 * n, 4⟩))
      (fun _ => False) (n * 4 + 8) (initMachineStateWithCallees cdBody [.scalar ⟨n, 4⟩] []) :=
    wlpOutcomeV2026_of_stepStageCut hSteps.to_stepStageCut
      (wlpOutcomeV2026_done_eq (fuel := n * 4 + 7) (cd_exit_done_forall (2 * n)) rfl)
  have hSafe : wpStateV2026 cdBody (n * 4 + 4)
      (initMachineStateWithCallees cdBody [.scalar ⟨n, 4⟩] []) (fun _ => True) :=
    reachesDoneWithinV2026_iff_wpStateV2026.mp
      (ReachesDoneWithinV2026.weaken (fun _ _ => trivial) (cd_pass1_forall n hn))
  exact wpStateV2026_of_wlp_and_safety_le (Nat.add_le_add_left (by decide : 4 ≤ 8) (n * 4))
    hWlp hSafe

/-- Universal stateless `VerificationResult` for `countdown(n)` over all `2 * n < 2^32`. -/
theorem cd_verificationResult_forall :
    VerificationResult
      { body := cdBody
        pre := fun args => ∃ n, args = [.scalar ⟨n, 4⟩] ∧ 2 * n < M32
        post := fun args r => ∃ n, args = [.scalar ⟨n, 4⟩] ∧ r = .scalar ⟨2 * n, 4⟩ } := by
  refine verifyMirNoPanic_of_execWithinStepsV2026 _ (fun args ⟨n, hArgs, hn⟩ => ?_)
  subst hArgs
  exact ⟨n * 4 + 4, ReachesDoneWithinV2026.weaken
    (fun out hOut => by
      cases out with
      | normal p => exact ⟨n, rfl, hOut⟩
      | panic => exact False.elim hOut
      | abort => exact False.elim hOut)
    (reachesDoneWithinV2026_iff_wpStateV2026.mpr (cd_pass2_forall n hn))⟩

/-- Universal stateful `StatefulVerificationResult` for `countdown(n)` over all `2 * n < 2^32`. -/
theorem cd_statefulVerificationResult_forall :
    StatefulVerificationResult
      { body := cdBody
        pre := fun args mem => (∃ n, args = [.scalar ⟨n, 4⟩] ∧ 2 * n < M32) ∧ mem = cdInit.memory
        post := fun args _ r _ => ∃ n, args = [.scalar ⟨n, 4⟩] ∧ r = .scalar ⟨2 * n, 4⟩ } := by
  refine verifyStatefulMirNoPanic_of_execWithinStepsV2026 _ (fun args mem ⟨⟨n, hArgs, hn⟩, hMem⟩ => ?_)
  subst hArgs
  subst hMem
  exact ⟨n * 4 + 4, ReachesDoneWithinV2026.weaken
    (fun out hOut => by
      cases out with
      | normal p => exact ⟨n, rfl, hOut⟩
      | panic => exact False.elim hOut
      | abort => exact False.elim hOut)
    (reachesDoneWithinV2026_iff_wpStateV2026.mpr (cd_pass2_forall n hn))⟩

/-! ## Pillar 3: Negative Non-Vacuity & Fail-Closed Falsification Canaries -/

/-! ### 3a. Overflowing `unchecked_mul` inside the inline callee -/

/-- Checkpoint: callee at `bb3`, about to call `unchecked_mul`. -/
def scaledCp1b : SymProg :=
  { scaledCp1 with frame := { blockIdx := 3, stmtIdx := 1, locals := [U, I vm, I vk, D] } }

theorem scaled_chunk2a :
    symProgRunSteps scaledCfg 5 scaledCp1 = .step scaledCp1b [.assertHolds (.const ⟨1, 1⟩) true] :=
  rfl

theorem scaled_prefix11 :
    symProgRunSteps scaledCfg (6 + 5) scaledEntry =
      .step scaledCp1b [.assertHolds (.const ⟨1, 1⟩) true] :=
  symProgRunSteps_trans scaled_chunk1 scaled_chunk2a

/-- Overflowing inputs `(0, 2^32, 2^32)`: `2^32 * 2^32 = 2^64` overflows `usize`. -/
abbrev ovEnv : SymEnv := scaledEnv 0 4294967296 4294967296

/-- Symbolic rejection: the recorded `noOverflowMul` condition fails closed. -/
theorem scaled_overflow_conds_fail : ¬ condsHold ovEnv scaledConds := by
  intro h
  have hm : wrapScalarBits 4294967296 (scalarModulus 8) * wrapScalarBits 4294967296
      (scalarModulus 8) < scalarModulus 8 := h.2.1.2
  exact absurd hm (by decide)

/-- Operational rejection: the unmodified trusted `stepMirFn` faults with UB at
the `unchecked_mul` call (no symbolic executor involved in this step). -/
theorem scaled_overflow_stepMirFn_ub :
    stepMirFn addScaledCallerBody (scaledCp1b.toMachineState scaledCfg ovEnv) =
      MirStepNode.fail .ub := rfl

theorem scaled_overflow_v2026_fault :
    v2026Step addScaledCallerBody (scaledCp1b.toMachineState scaledCfg ovEnv) =
      .fault (.fail .ub) := rfl

/-- The overflowing `add_scaled(0, 2^32, 2^32)` run is refuted by unmodified
`MirNoUBTree`, `MirWpConverges`, and every `ReachesDoneWithinV2026` /
`ExecWithinStepsV2026`. -/
theorem scaled_overflow_refuted :
    ¬ MirNoUBTree (mirTree addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su 0, su 4294967296, su 4294967296]
          [mulScaledCalleeBody])) ∧
      (∀ post, ¬ MirWpConverges addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su 0, su 4294967296, su 4294967296]
          [mulScaledCalleeBody]) post) ∧
      (∀ post bound, ¬ ExecWithinStepsV2026 addScaledCallerBody
        [su 0, su 4294967296, su 4294967296] [mulScaledCalleeBody] post bound) := by
  have h := symProgRunSteps_fault_refutes scaled_prefix11 ovEnv ⟨rfl, trivial⟩
    scaled_overflow_v2026_fault
  rw [show addScaledCallerBody = scaledCfg.body from rfl, show [mulScaledCalleeBody] =
    scaledCfg.callees from rfl, ← scaled_args_eval, ← symProgEntry_toMachineState]
  exact h

/-! ### 3a-ii. Overflowing `unchecked_add` in the caller after inline callee returns -/

/-- Checkpoint: caller at `bb1`, `stmtIdx = 6`, about to invoke `unchecked_add`. -/
def scaledCp2b : SymProg :=
  { frame := { blockIdx := 1, stmtIdx := 6
               locals := [U, I vb, I vm, I vk, I vmk, D, D, I vb, I vmk] }
    stack := []
    active := some addScaledCallerBody }

theorem scaled_chunk3a :
    symProgRunSteps scaledCfg 6 scaledCp2 = .step scaledCp2b [] := rfl

theorem scaled_prefix19 :
    symProgRunSteps scaledCfg (6 + (7 + 6)) scaledEntry =
      .step scaledCp2b [.assertHolds (.const ⟨1, 1⟩) true, .noOverflowMul false vm vk] :=
  symProgRunSteps_trans scaled_chunk1 (symProgRunSteps_trans scaled_chunk2 scaled_chunk3a)

/-- Inputs `(2^64 - 1, 1, 1)`: callee `mul_scaled(1, 1) = 1` succeeds, then
caller `unchecked_add(2^64 - 1, 1)` overflows `usize`! -/
abbrev ovAddEnv : SymEnv := scaledEnv 18446744073709551615 1 1

/-- Symbolic rejection: `noOverflowAdd` fails closed while `noOverflowMul` holds. -/
theorem scaled_add_overflow_conds_fail : ¬ condsHold ovAddEnv scaledConds := by
  intro h
  have ha : scBits (vb.eval ovAddEnv) + scBitsAt (vb.eval ovAddEnv) (vmk.eval ovAddEnv) <
      scalarModulus (vb.eval ovAddEnv).sizeBytes := h.2.2.1.2
  exact absurd ha (by decide)

/-- Operational rejection: unmodified trusted `stepMirFn` faults with UB at the
caller's `unchecked_add` call after returning from `mul_scaled`. -/
theorem scaled_add_overflow_stepMirFn_ub :
    stepMirFn addScaledCallerBody (scaledCp2b.toMachineState scaledCfg ovAddEnv) =
      MirStepNode.fail .ub := rfl

theorem scaled_add_overflow_refuted :
    ¬ MirNoUBTree (mirTree addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody
          [su 18446744073709551615, su 1, su 1] [mulScaledCalleeBody])) ∧
      (∀ post, ¬ MirWpConverges addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody
          [su 18446744073709551615, su 1, su 1] [mulScaledCalleeBody]) post) ∧
      (∀ post bound, ¬ ExecWithinStepsV2026 addScaledCallerBody
        [su 18446744073709551615, su 1, su 1] [mulScaledCalleeBody] post bound) := by
  have hPreConds : condsHold ovAddEnv [.assertHolds (.const ⟨1, 1⟩) true, .noOverflowMul false vm vk] :=
    ⟨rfl, ⟨⟨eight_ne_zero, rfl⟩, by decide⟩, trivial⟩
  have h := symProgRunSteps_fault_refutes scaled_prefix19 ovAddEnv hPreConds (fk := .ub) rfl
  rw [show addScaledCallerBody = scaledCfg.body from rfl, show [mulScaledCalleeBody] =
    scaledCfg.callees from rfl, ← scaled_args_eval, ← symProgEntry_toMachineState]
  exact h

/-! ### 3a-iii. UNIVERSAL fail-closed UB via exact side conditions

Not a single overflowing witness: for EVERY overflowing input, the violated
recorded `SymCond` is turned by `symProgRunSteps_ub_refutes` (exactness of the
intrinsic side conditions) into a trusted UB fault of unmodified `stepMirFn`. -/

/-- Callee state right after `unchecked_mul` (`bb4`, `_0 = vm * vk`). -/
def scaledCp1c : SymProg :=
  { scaledCp1 with frame := { blockIdx := 4, stmtIdx := 0, locals := [I vmk, I vm, I vk, D] } }

theorem scaled_mul_step :
    symProgStep scaledCfg scaledCp1b = .step scaledCp1c [.noOverflowMul false vm vk] := rfl

theorem scaled_at_mul : scaledCp1b.atCall scaledCfg = true := rfl

/-- For ALL `(b, m, k)` with `2^64 ≤ m * k`, `add_scaled` has UB inside the
inline callee: refutes `MirNoUBTree`, `MirWpConverges`, and every
`ExecWithinStepsV2026`. -/
theorem add_scaled_mul_overflow_ub_forall {b m k : Nat} (hm : m < M64) (hk : k < M64)
    (hov : M64 ≤ m * k) :
    ¬ MirNoUBTree (mirTree addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody])) ∧
      (∀ post, ¬ MirWpConverges addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody])
        post) ∧
      (∀ post bound, ¬ ExecWithinStepsV2026 addScaledCallerBody [su b, su m, su k]
        [mulScaledCalleeBody] post bound) := by
  have hn : ¬ condsHold (scaledEnv b m k) [.noOverflowMul false vm vk] := by
    intro h
    have hlt : wrapScalarBits m (scalarModulus 8) * wrapScalarBits k (scalarModulus 8) <
        scalarModulus 8 := h.1.2
    rw [wrapScalarBits_of_lt hm, wrapScalarBits_of_lt hk] at hlt
    exact Nat.not_le_of_gt hlt hov
  have h := symProgRunSteps_ub_refutes scaled_prefix11 scaled_mul_step scaled_at_mul
    (scaledEnv b m k) ⟨rfl, trivial⟩ hn
  rw [show addScaledCallerBody = scaledCfg.body from rfl, show [mulScaledCalleeBody] =
    scaledCfg.callees from rfl, ← scaled_args_eval, ← symProgEntry_toMachineState]
  exact h

theorem scaled_add_step :
    symProgStep scaledCfg scaledCp2b = .step scaledCp3 [.noOverflowAdd false vb vmk] := rfl

theorem scaled_at_add : scaledCp2b.atCall scaledCfg = true := rfl

/-- Non-switch steps are exactly silent (`symProgStep_sound_obs`), e.g. the
caller's `unchecked_add` call in `add_scaled`. -/
theorem scaled_add_call_silent (b m k : Nat) (hc : condsHold (scaledEnv b m k)
    [.noOverflowAdd false vb vmk]) :
    stepMirFn addScaledCallerBody (scaledCp2b.toMachineState scaledCfg (scaledEnv b m k)) =
      MirStepNode.step (scaledCp3.toMachineState scaledCfg (scaledEnv b m k)) :=
  symProgStep_sound_obs scaled_add_step (scaledEnv b m k) hc

/-- For ALL `(b, m, k)` where the callee product fits but `2^64 ≤ b + m * k`,
`add_scaled` has UB at the caller's `unchecked_add` after the inline callee
returned. -/
theorem add_scaled_add_overflow_ub_forall {b m k : Nat} (hb : b < M64) (hm : m < M64)
    (hk : k < M64) (hmk : m * k < M64) (hov : M64 ≤ b + m * k) :
    ¬ MirNoUBTree (mirTree addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody])) ∧
      (∀ post, ¬ MirWpConverges addScaledCallerBody
        (initMachineStateWithCallees addScaledCallerBody [su b, su m, su k] [mulScaledCalleeBody])
        post) ∧
      (∀ post bound, ¬ ExecWithinStepsV2026 addScaledCallerBody [su b, su m, su k]
        [mulScaledCalleeBody] post bound) := by
  have hpre : condsHold (scaledEnv b m k)
      [.assertHolds (.const ⟨1, 1⟩) true, .noOverflowMul false vm vk] := by
    refine ⟨rfl, ⟨⟨eight_ne_zero, rfl⟩, ?_⟩, trivial⟩
    show wrapScalarBits m (scalarModulus 8) * wrapScalarBits k (scalarModulus 8) < scalarModulus 8
    rw [wrapScalarBits_of_lt hm, wrapScalarBits_of_lt hk]
    exact hmk
  have hn : ¬ condsHold (scaledEnv b m k) [.noOverflowAdd false vb vmk] := by
    intro h
    have hlt : scBits (vb.eval (scaledEnv b m k)) +
        scBitsAt (vb.eval (scaledEnv b m k)) (vmk.eval (scaledEnv b m k)) <
          scalarModulus (vb.eval (scaledEnv b m k)).sizeBytes := h.1.2
    rw [scaled_vmk_eval hm hk hmk] at hlt
    change wrapScalarBits b (scalarModulus 8) + wrapScalarBits (m * k) (scalarModulus 8) <
      scalarModulus 8 at hlt
    rw [wrapScalarBits_of_lt hb, wrapScalarBits_of_lt hmk] at hlt
    exact Nat.not_le_of_gt hlt hov
  have h := symProgRunSteps_ub_refutes scaled_prefix19 scaled_add_step scaled_at_add
    (scaledEnv b m k) hpre hn
  rw [show addScaledCallerBody = scaledCfg.body from rfl, show [mulScaledCalleeBody] =
    scaledCfg.callees from rfl, ← scaled_args_eval, ← symProgEntry_toMachineState]
  exact h

/-! ### 3b. Failing callee precondition `Assert` -/

/--
```text
fn chk(flag: bool, x: u32) -> u32 {
  // bb0: assert(copy _1, expected = true) -> bb1, unwind: unreachable
  // bb1: _0 = copy _2; return
}
``` -/
def chkBody : CapturedMir :=
  { defPath := "chk::chk"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls := [decl u32Ty' "_0", decl boolTy "flag", decl u32Ty' "x"]
    basicBlocks :=
      [ { statements := []
          terminator := tm (.assert (.copy (pl 1)) true 1 .unreachable)
          isCleanup := false }
      , { statements := [st (.assign (pl 0) (.use (.copy (pl 2))))]
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := boolLayout, mode := .direct }, { layout := u32Layout', mode := .direct }]
        ret := { layout := u32Layout', mode := .direct }
        conv := .rust
        canUnwind := false }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u32Layout', boolLayout] }
    allocations := [] }

def chkCfg : SymConfig := { body := chkBody, callees := [] }

abbrev vflag : SymScalar := .var 0 1
abbrev vchkx : SymScalar := .var 1 4

def chkEntry : SymProg := symProgEntry chkCfg [.scalar vflag, .scalar vchkx]

theorem chk_run :
    symRunChunks chkCfg [3] chkEntry =
      .ret (.scalar vchkx)
        { frame := { blockIdx := 1, stmtIdx := 1, locals := [I vchkx, I vflag, I vchkx] }
          stack := [], active := none }
        [.assertHolds vflag true] := rfl

/-- Positive: with `flag = true` the precondition holds and `chk` returns `x`. -/
theorem chk_ok (x : Nat) :
    ExecWithinStepsV2026 chkBody [.scalar ⟨1, 1⟩, .scalar ⟨x, 4⟩] []
      (mirNormalPost (fun r _ => r = .scalar ⟨x, 4⟩)) 3 :=
  (symRunChunks_sound (post := mirNormalPost (fun r _ => r = .scalar ⟨x, 4⟩)) chk_run
    (pairEnv 1 x) ⟨rfl, trivial⟩ rfl).2.1

/-- Symbolic rejection: with `flag = false` the `assertHolds` condition fails. -/
theorem chk_conds_fail (x : Nat) : ¬ condsHold (pairEnv 0 x) [.assertHolds vflag true] :=
  fun h => Nat.noConfusion (h.1 : (0 : Nat) = 1)

/-- Operational rejection: unmodified `stepMirFn` faults with UB (unwind
`unreachable`) on the failing assertion. -/
theorem chk_stepMirFn_ub (x : Nat) :
    stepMirFn chkBody (initMachineStateWithCallees chkBody [.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] []) =
      MirStepNode.fail .ub := rfl

theorem chk_refuted (x : Nat) :
    ¬ MirNoUBTree (mirTree chkBody
        (initMachineStateWithCallees chkBody [.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] [])) ∧
      ∀ post bound, ¬ ExecWithinStepsV2026 chkBody [.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] [] post
        bound := by
  have h := symProgRunSteps_fault_refutes (symProgRunSteps_zero chkCfg chkEntry) (pairEnv 0 x)
    trivial (fk := .ub) rfl
  rw [show chkBody = chkCfg.body from rfl, show ([] : List CapturedMir) = chkCfg.callees from rfl,
    show [Value.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] = symValsEval (pairEnv 0 x)
      [.scalar vflag, .scalar vchkx] from rfl, ← symProgEntry_toMachineState]
  exact ⟨h.1, h.2.2⟩

/-- Multi-frame caller invoking inline callee `chk(flag, x)` whose `Assert` fails
when `flag = false`. -/
def callChkBody : CapturedMir :=
  { defPath := "chk::call_chk"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls := [decl u32Ty' "_0", decl boolTy "flag", decl u32Ty' "x"]
    basicBlocks :=
      [ { statements := []
          terminator := tm (.call (fnOp "chk::chk" []) [.copy (pl 1), .copy (pl 2)]
            (pl 0) (some 1) .unreachable)
          isCleanup := false }
      , { statements := []
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := boolLayout, mode := .direct }, { layout := u32Layout', mode := .direct }]
        ret := { layout := u32Layout', mode := .direct }
        conv := .rust
        canUnwind := false }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u32Layout', boolLayout] }
    allocations := [] }

def callChkCfg : SymConfig := { body := callChkBody, callees := [chkBody] }
def callChkEntry : SymProg := symProgEntry callChkCfg [.scalar vflag, .scalar vchkx]

def callChkInCallee : SymProg :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [U, I vflag, I vchkx] }
    stack := [{ callerBody := callChkBody
                frame := { blockIdx := 0, stmtIdx := 0, locals := [U, I vflag, I vchkx] }
                destination := pl 0
                returnTarget := 1
                returnUnwind := .unreachable }]
    active := some chkBody }

theorem callChk_prefix1 :
    symProgRunSteps callChkCfg 1 callChkEntry = .step callChkInCallee [] := rfl

theorem callChk_full :
    symRunChunks callChkCfg [5] callChkEntry =
      .ret (.scalar vchkx)
        { frame := { blockIdx := 1, stmtIdx := 0, locals := [I vchkx, I vflag, I vchkx] }
          stack := [], active := some callChkBody } [.assertHolds vflag true] := rfl

theorem callChk_stepMirFn_ub (x : Nat) :
    stepMirFn callChkBody (callChkInCallee.toMachineState callChkCfg (pairEnv 0 x)) =
      MirStepNode.fail .ub := rfl

theorem callChk_refuted (x : Nat) :
    ¬ condsHold (pairEnv 0 x) [.assertHolds vflag true] ∧
      ¬ MirNoUBTree (mirTree callChkBody
        (initMachineStateWithCallees callChkBody [.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] [chkBody])) ∧
      (∀ post, ¬ MirWpConverges callChkBody
        (initMachineStateWithCallees callChkBody [.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] [chkBody]) post) ∧
      (∀ post bound, ¬ ExecWithinStepsV2026 callChkBody
        [.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] [chkBody] post bound) := by
  have h := symProgRunSteps_fault_refutes callChk_prefix1 (pairEnv 0 x) trivial (fk := .ub) rfl
  rw [show callChkBody = callChkCfg.body from rfl, show [chkBody] = callChkCfg.callees from rfl,
    show [Value.scalar ⟨0, 1⟩, .scalar ⟨x, 4⟩] = symValsEval (pairEnv 0 x)
      [.scalar vflag, .scalar vchkx] from rfl, ← symProgEntry_toMachineState]
  exact ⟨chk_conds_fail x, h.1, h.2.1, h.2.2⟩

/-! ### 3c. Division by zero and out-of-bounds shift -/

/--
```text
fn divsh(a: u32, b: u32) -> u32 {
  // bb0: StorageLive(_3); _3 = core::intrinsics::unchecked_div::<u32>(copy _1, copy _2) -> bb1
  // bb1: _0 = core::intrinsics::unchecked_shl::<u32, u32>(move _3, copy _2) -> bb2
  // bb2: StorageDead(_3); return
}
``` -/
def divShBody : CapturedMir :=
  { defPath := "divsh::divsh"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 2
    localDecls := [decl u32Ty' "_0", decl u32Ty' "a", decl u32Ty' "b", decl u32Ty' "_3"]
    basicBlocks :=
      [ { statements := [st (.storageLive 3)]
          terminator := tm (.call (fnOp "core::intrinsics::unchecked_div" [.uint .u32])
            [.copy (pl 1), .copy (pl 2)] (pl 3) (some 1) .continue_)
          isCleanup := false }
      , { statements := []
          terminator := tm (.call (fnOp "core::intrinsics::unchecked_shl" [.uint .u32, .uint .u32])
            [.move (pl 3), .copy (pl 2)] (pl 0) (some 2) .continue_)
          isCleanup := false }
      , { statements := [st (.storageDead 3)]
          terminator := tm .return_
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u32Layout', mode := .direct }, { layout := u32Layout', mode := .direct }]
        ret := { layout := u32Layout', mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u32Layout'] }
    allocations := [] }

def divShCfg : SymConfig := { body := divShBody, callees := [] }

abbrev vdq : SymScalar := .uncheckedOp .div false false vx vy
abbrev vds : SymScalar := .uncheckedOp .shl false false vdq vy

def divShEntry : SymProg := symProgEntry divShCfg [.scalar vx, .scalar vy]

abbrev divShConds : List SymCond := [.divSafe false vx vy, .shiftInBounds false vdq vy]

theorem divSh_run :
    symRunChunks divShCfg [5] divShEntry =
      .ret (.scalar vds)
        { frame := { blockIdx := 2, stmtIdx := 1, locals := [I vds, I vx, I vy, D] }
          stack := [], active := none } divShConds := rfl

/-- Positive: `divsh(64, 2) = (64 / 2) << 2 = 128`. -/
theorem divSh_ok :
    ExecWithinStepsV2026 divShBody [.scalar ⟨64, 4⟩, .scalar ⟨2, 4⟩] []
      (mirNormalPost (fun r _ => r = .scalar ⟨128, 4⟩)) 5 :=
  (symRunChunks_sound (post := mirNormalPost (fun r _ => r = .scalar ⟨128, 4⟩)) divSh_run
    (pairEnv 64 2) ⟨⟨⟨Nat.succ_ne_zero 3, rfl⟩, by decide, trivial⟩,
      ⟨Nat.succ_ne_zero 3, Nat.succ_ne_zero 3, rfl, by decide⟩, trivial⟩ rfl).2.1

/-- Symbolic rejection: division by zero fails the `divSafe` condition. -/
theorem divSh_div0_conds_fail (a : Nat) : ¬ condsHold (pairEnv a 0) divShConds :=
  fun h => h.1.2.1 rfl

/-- Symbolic rejection: shift by `32` fails `shiftInBounds` (`64 / 32 = 2`). -/
theorem divSh_shift_conds_fail : ¬ condsHold (pairEnv 64 32) divShConds := by
  intro h
  have hb : scBits (vy.eval (pairEnv 64 32)) < Nat.mul 4 8 := h.2.1.2.2.2
  exact absurd hb (by decide)

/-- Program point just before the `unchecked_div` call. -/
def divShAtDiv : SymProg :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [U, I vx, I vy, U] }
    stack := [], active := none }

theorem divSh_prefix1 : symProgRunSteps divShCfg 1 divShEntry = .step divShAtDiv [] := rfl

/-- Operational rejection (division by zero) on unmodified `stepMirFn`, for every
dividend `a`. -/
theorem divSh_div0_ub (a : Nat) :
    stepMirFn divShBody (divShAtDiv.toMachineState divShCfg (pairEnv a 0)) =
      MirStepNode.fail .ub := rfl

theorem divSh_div0_refuted (a : Nat) :
    ¬ MirNoUBTree (mirTree divShBody
        (initMachineStateWithCallees divShBody [.scalar ⟨a, 4⟩, .scalar ⟨0, 4⟩] [])) ∧
      ∀ post bound, ¬ ExecWithinStepsV2026 divShBody [.scalar ⟨a, 4⟩, .scalar ⟨0, 4⟩] [] post
        bound := by
  have h := symProgRunSteps_fault_refutes divSh_prefix1 (pairEnv a 0) trivial (fk := .ub) rfl
  rw [show divShBody = divShCfg.body from rfl,
    show ([] : List CapturedMir) = divShCfg.callees from rfl,
    show [Value.scalar ⟨a, 4⟩, .scalar ⟨0, 4⟩] = symValsEval (pairEnv a 0)
      [.scalar vx, .scalar vy] from rfl, ← symProgEntry_toMachineState]
  exact ⟨h.1, h.2.2⟩

/-- Program point just before the `unchecked_shl` call. -/
def divShAtShl : SymProg :=
  { frame := { blockIdx := 1, stmtIdx := 0, locals := [U, I vx, I vy, I vdq] }
    stack := [], active := none }

theorem divSh_shift_ub :
    stepMirFn divShBody (divShAtShl.toMachineState divShCfg (pairEnv 64 32)) =
      MirStepNode.fail .ub := rfl

/-- Operational rejection (shift out of bounds) after the first (defined) step:
refutes `MirNoUBTree`, `MirWpConverges`, and every `ExecWithinStepsV2026`. -/
theorem divSh_shift_refuted :
    ¬ MirNoUBTree (mirTree divShBody
        (initMachineStateWithCallees divShBody [.scalar ⟨64, 4⟩, .scalar ⟨32, 4⟩] [])) ∧
      (∀ post, ¬ MirWpConverges divShBody
        (initMachineStateWithCallees divShBody [.scalar ⟨64, 4⟩, .scalar ⟨32, 4⟩] []) post) ∧
      (∀ post bound, ¬ ExecWithinStepsV2026 divShBody
        [.scalar ⟨64, 4⟩, .scalar ⟨32, 4⟩] [] post bound) := by
  have hpre : symProgRunSteps divShCfg 2 divShEntry =
      .step divShAtShl [.divSafe false vx vy] := rfl
  have h := symProgRunSteps_fault_refutes hpre (pairEnv 64 32)
    ⟨⟨⟨Nat.succ_ne_zero 3, rfl⟩, by decide, trivial⟩, trivial⟩ (fk := .ub) rfl
  rw [show divShBody = divShCfg.body from rfl,
    show ([] : List CapturedMir) = divShCfg.callees from rfl,
    show [Value.scalar ⟨64, 4⟩, .scalar ⟨32, 4⟩] = symValsEval (pairEnv 64 32)
      [.scalar vx, .scalar vy] from rfl, ← symProgEntry_toMachineState]
  exact h

/-! ### 3d. Under-budget bounds and divergence -/

/-- Under-budget refutation on the concrete witness: `23 < 24` steps. -/
theorem add_scaled_concrete_not_23 :
    ¬ ExecWithinStepsV2026 addScaledCallerBody [su 100, su 7, su 8] [mulScaledCalleeBody]
      (mirNormalPost (fun r _ => r = su 156)) 23 :=
  add_scaled_not_23 (by decide) (by decide) (by decide) (by decide) (by decide) _

/-- `fn spin() -> u32 { loop {} }` (`bb0: goto bb0`). -/
def spinBody : CapturedMir :=
  { defPath := "spin::spin"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := [decl u32Ty' "_0"]
    basicBlocks := [{ statements := [], terminator := tm (.goto 0), isCleanup := false }]
    fnAbi :=
      { args := []
        ret := { layout := u32Layout', mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := { pointerBits := 64, isLittleEndian := true, entries := [u32Layout'] }
    allocations := [] }

def spinCfg : SymConfig := { body := spinBody, callees := [] }

/-- The symbolic executor itself certifies the self-loop (`1` step back to the
entry), which yields a productive divergence witness. -/
theorem spin_selfloop : symProgRunSteps spinCfg 1 (symProgEntry spinCfg []) =
    .step (symProgEntry spinCfg []) [] := rfl

/-- Diverging loop: partial correctness (`wlpStateV2026`, any postcondition, any
fuel) holds while every `ReachesDoneWithinV2026` / `MirWpConverges` fails. -/
theorem spin_partial_not_total (fuel bound : Nat) (post : MirOutcome → Prop) :
    wlpStateV2026 spinBody fuel (initMachineState spinBody []) post ∧
      ¬ ReachesDoneWithinV2026 spinBody post bound (initMachineState spinBody []) ∧
      ¬ MirWpConverges spinBody (initMachineState spinBody []) post := by
  have hstep : v2026Step spinBody (initMachineState spinBody []) =
      .step (initMachineState spinBody []) := by
    have h := symProgRunSteps_sound spinCfg (fun _ => 0) 1 spin_selfloop trivial
    rw [symProgEntry_toMachineState] at h
    cases h with
    | step hs hrest =>
      cases hrest
      exact hs
  have hW : ProductiveStepWitness spinBody id (fun st => st = initMachineState spinBody []) :=
    { stepOk := fun st hEq => by subst hEq; exact hstep
      preserves := fun st hEq => hEq }
  have hDiv : DivergesV2026 spinBody (initMachineState spinBody []) :=
    divergesV2026_of_productiveWitness (inv := fun st => st = initMachineState spinBody []) rfl hW
  exact ⟨wlpOutcomeV2026_of_productiveWitness hW post (fun _ => False) fuel rfl,
    not_reachesDoneWithinV2026_of_divergesV2026 hDiv bound post,
    not_mirWpConverges_of_divergesV2026 hDiv post⟩

/-! ## Pillar 4: `#print axioms` + `run_cmd` Kernel Hygiene Audit -/

#print axioms symProgStep_sound
#print axioms symProgRunSteps_sound
#print axioms symProgRunSteps_ret_sound
#print axioms symRunChunks_sound
#print axioms symRunChunksWith_sound
#print axioms symChunkCut_entry_sound
#print axioms symRunChunks_of_boolCert
#print axioms verificationResult_of_symRunChunks
#print axioms statefulVerificationResult_of_symRunChunks
#print axioms add_scaled_symbolic
#print axioms add_scaled_blockCtx_firewall
#print axioms add_scaled_verificationResult
#print axioms add_scaled_statefulVerificationResult
#print axioms checkedAddCast_symbolic
#print axioms scaled_overflow_refuted
#print axioms scaled_add_overflow_refuted
#print axioms callChk_refuted
#print axioms cd_pass1_forall
#print axioms cd_pass2_forall
#print axioms cd_not_tight_forall
#print axioms cd_verificationResult_forall
#print axioms cd_statefulVerificationResult_forall
#print axioms cd_worklist
#print axioms spin_partial_not_total

open Lean Elab Command in
/-- Fails unless every constant in `names` depends only on `allowed` axioms. -/
def auditAxioms (names : Array Name) (allowed : Array Name) : CommandElabM Unit := do
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      unless allowed.contains a do
        throwError m!"trust audit failed: {n} depends on {a}"

/-- Suffix of compiler-generated unsafe recursive auxiliaries. -/
def unsafeRecSuffix : String := "_unsafe" ++ "_rec"

open Lean Elab Command in
/-- Fails if any constant of module `mod` is a postulated constant, a
compiler-generated unsafe recursive auxiliary, a `noncomputable` def (when
`forbidNoncomputable = true`), or a theorem / definition whose trust base leaves
outside `allowed`. -/
def auditModule (mod : Name) (allowed : Array Name)
    (forbidNoncomputable : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod
    | throwError m!"module {mod} not imported"
  let names := (env.header.moduleData[idx.toNat]!).constNames
  let mut checked : Array Name := #[]
  let mut thmCount : Nat := 0
  let mut defCount : Nat := 0
  for n in names do
    if n.toString.endsWith unsafeRecSuffix then
      throwError m!"hygiene audit failed: {n} is an unsafe recursive auxiliary"
    if forbidNoncomputable && Lean.isNoncomputable env n then
      throwError m!"hygiene audit failed: {n} is noncomputable"
    match env.find? n with
    | some (.axiomInfo _) => throwError m!"hygiene audit failed: {n} is postulated"
    | some (.thmInfo _) =>
      checked := checked.push n
      thmCount := thmCount + 1
    | some (.defnInfo _) =>
      checked := checked.push n
      defCount := defCount + 1
    | _ => pure ()
  auditAxioms checked allowed
  logInfo m!"audited {mod}: {names.size} constants, {thmCount} theorems, {defCount} defs"

/-- Standard axioms permitted anywhere. -/
def standardAxioms : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Choice-free axioms required of the symbolic executor and certificates. -/
def choiceFreeAxioms : Array Lean.Name := #[``propext, ``Quot.sound]

-- All 5 converged modules: no postulates, no unsafe recursive auxiliaries, and only
-- standard axioms in every theorem AND definition.
run_cmd auditModule `Anneal.Framework.StepWp standardAxioms
run_cmd auditModule `Anneal.CnfOrd.Worklist standardAxioms
run_cmd auditModule `Anneal.ConjunctiveWp.WlpV2026 standardAxioms
run_cmd auditModule `Anneal.StepBound.StepBoundV2026 standardAxioms

-- The chunked symbolic executor: EVERY theorem AND definition is choice-free and computable.
run_cmd auditModule `Anneal.MirSymExec.ChunkedCallV2026 choiceFreeAxioms (forbidNoncomputable := true)

-- Key end-to-end test theorems: choice-free (including the
-- `VerificationResult` / `StatefulVerificationResult` certificates).
/-- Key end-to-end test theorems (positive and negative canaries). -/
def keyTestTheorems : Array Lean.Name :=
  #[``add_scaled_symbolic, ``add_scaled_blockCtx_firewall,
    ``add_scaled_verificationResult, ``add_scaled_statefulVerificationResult,
    ``add_scaled_not_23, ``checkedAddCast_symbolic,
    ``scaled_overflow_refuted, ``scaled_overflow_conds_fail,
    ``scaled_add_overflow_refuted, ``scaled_add_overflow_conds_fail,
    ``mix_symbolic, ``mix_concrete, ``sel_symbolic, ``chk_ok,
    ``chk_refuted, ``callChk_refuted, ``divSh_ok, ``divSh_div0_refuted, ``divSh_shift_refuted,
    ``cd_pass1_loop, ``cd_pass2, ``cd_worklist, ``cd_not15, ``cd_verificationResult,
    ``cd_statefulVerificationResult, ``cd_pass1_forall, ``cd_pass2_forall,
    ``cd_not_tight_forall, ``cd_verificationResult_forall, ``cd_statefulVerificationResult_forall,
    ``spin_partial_not_total, ``add_scaled_mul_overflow_ub_forall,
    ``add_scaled_add_overflow_ub_forall, ``sel_emits_event_zero, ``sel_emits_event_succ,
    ``scaled_add_call_silent, ``cd_iter_forall]

run_cmd auditAxioms keyTestTheorems choiceFreeAxioms

end Anneal.MirSymExec.ChunkedCallV2026.Tests
