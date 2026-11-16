-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.LocalAccess
import Miri.Interpreter.Place
import Miri.Interpreter.Rvalue
import Miri.Interpreter.Step
import Miri.Interpreter.ControlFlow
import Trusted.MirAst
import Trusted.MirSemantics

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# MIR Correspondence Specification (`Trusted.Correspondence`)

**HUMAN COMPREHENSION PRIORITY:**
This module states the top-level MIR correspondence theorem
(`CorrespondenceClaim`), the bidirectional fault-equivalence theorem
(`FaultEquivalenceClaim`), the Miri move-deinitialization wiring theorem
(`MiriMoveDeinitWiringClaim`), and the bijective simulation invariant
(`SimulationInv`) together with all of their adapter definitions. Because this
file is the human-audited specification bridge between `Trusted.MirSemantics`
($M_{\text{anneal}}$) and `vendor/lean-miri/` ($M_{\text{ref}}$), **human
comprehension takes priority over every other concern** across
`CorrespondenceClaim` and all of its transitive dependencies
(`Trusted.Correspondence`, `Trusted.MirSemantics`, and `Trusted.MirAst`). Every
definition in this module is written to be maximally direct, self-evident to a
human auditor, and accompanied by explicit boundary documentation so any gap or
scoping restriction is immediately visible rather than subtle.

This module defines five components:

1. **Reference-indexed MIR syntax (`RefProg`):** Mirrors `Miri.MIR.Syntax` by
   replacing inline structural `MirTy` values with `TyId := Nat` indices into a
   single deduplicated program type table `RefProg.types : List MirTy`, while
   carrying `pointerWidthBits : Nat := 64` and `mirProfileVersion : Nat := 1`.
2. **Canonical type-interning codec (`encodeProg` / `decodeProg`):** Interns
   every structural `MirTy` in bottom-up topological order (pre-populating
   `TyId` `0 = .unit`, `1 = .bool`, `2 = .int .isize false` for
   `ExecutionMachine` built-in layout queries) and provides an unconditional
   left-inverse decoder `decodeProg`.
3. **Reference semantics ($M_{\text{ref}}$) and step-budget quantification:**
   Defines a hybrid reference evaluator over `RefProg` / `RefState` that
   resolves `RefProg` bodies, basic blocks, and statements over list-indexed
   frames and delegates step, statement, terminator, rvalue, operand,
   local-storage, and scalar/integer evaluation to `vendor/lean-miri` (pinned
   at `proofs-rs/lean-miri` commit `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`,
   `miri` commit `7fa591d7d4dd9af8154becbc8332f8096f8323b1`, `rustc` commit
   `8144389c895da997dbdecaa635e41d6a50be6ffd`, and `rust-lang/reference`
   commit `38da84aa1f1b4fda6d0bc3d8fbdfeb7d8fb5f18e`) with explicit
   `stepsExecuted` and `maxSteps` tracking and runtime `Operand.move`
   deinitialization (`deinitMovedPlace = true`), routing:
   - constant decoding, scalar validity checks, unary/binary integer and boolean
     arithmetic, and `SwitchInt` case comparisons through
     `Miri.Memory.ScalarInt` and `Miri.Interpreter.IntegerOps`;
   - operand evaluation (`evalRefOperandToSlot`) through
     `Miri.Interpreter.evalOperand`;
   - local place writes (`writeRefPlace`) through
     `Miri.Interpreter.placeWriteLocalImmediate`;
   - rvalue dispatch (`evalRefRvalue`) through
     `Miri.Interpreter.evalRvalueIntoPlace` and `Miri.Interpreter.runRvalue`;
   - outer step, statement, and local-storage dispatch (`evalRefStep`,
     `evalRefStatement`) through `Miri.Interpreter.Step.step`,
     `Miri.Interpreter.Step.evalStatement`,
     `Miri.Interpreter.Frame.storageLive`, and
     `Miri.Interpreter.Frame.storageDead`; and
   - basic-block jumps and terminators (`jumpToRefBlock`, `evalRefTerminator`)
     through `Miri.Interpreter.Step.step`,
     `Miri.Interpreter.ControlFlow.goToBlock`,
     `Miri.Interpreter.ControlFlow.evalTerminator`, and
     `Miri.Interpreter.ControlFlow.returnFromCurrentFrame`:

   > "pub fn step(&mut self) -> InterpResult<'tcx, bool> { ...
   > if let Some(stmt) = block.statements.get(stmt_idx) { ...
   > self.eval_statement(stmt)?; return Ok(true); }
   > let terminator = block.terminator();
   > self.eval_terminator(terminator)?; Ok(true) }"
   > (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
   > `8144389c895da997dbdecaa635e41d6a50be6ffd`)
4. **Top-level correspondence claims (`CorrespondenceClaim`,
   `FaultEquivalenceClaim`, `MiriMoveDeinitWiringClaim`, and core simulation /
   canary `*Claim` propositions):** States UB transfer together with exact
   terminal-behavior and divergence equivalence (`WellFormed p q →
   RefWellFormed (encodeProg p) q ∧ (∀ out, Behavior p q out ↔ RefBehavior
   (encodeProg p) q out) ∧ (Diverges p q ↔ RefDiverges (encodeProg p) q)`),
   bidirectional fault equivalence for `.undefined` (`.ub`) and `.unsupported`
   (`.blocked`), and the direct wiring contract of
   `Miri.Interpreter.ExecutionMachine.step` (`Miri.Interpreter.Step.step` over
   `ExecutionMachine.stepHooks`) and `deinitMovedPlace` on
   `Miri.Interpreter.ExecutionMachine.{withValidation,operandHooks}` and
   `Miri.Interpreter.evalOperand`.
5. **Fail-closed target, profile, and stack shape:** `initRefState` rejects
   programs whose `pointerWidthBits` is not 64 or whose `mirProfileVersion` is
   not 1 (matching `Trusted.MirSemantics.initState`) and starts the reference
   stack as `[callerSentinelFrame retTy, entryFrame]`, which `evalRefStep`
   requires and preserves.
-/

/-- Interned type-table index (`Miri.MIR.TyId`). -/
abbrev TyId := Nat

/-! ## Reference-Indexed AST with `TyId` Indirection (`Miri.MIR` Boundary) -/

/-- Reference place projection element indexing `RefProg.types` via `TyId`. -/
inductive RefProjectionElem where
  | deref
  | field (fieldIdx : FieldIdx) (ty : TyId)
  | unsupported

/-- Reference MIR place (`Miri.MIR.Place`). -/
structure RefPlace where
  localId : LocalId
  projection : List RefProjectionElem := []

/-- Reference constant operand indexing `RefProg.types` via `TyId`. -/
structure RefConstOperand where
  ty : TyId
  lit : ConstLit

/-- Reference MIR operand (`Miri.MIR.Operand`). -/
inductive RefOperand where
  | copy (place : RefPlace)
  | move (place : RefPlace)
  | constant (c : RefConstOperand)

/-- Reference MIR rvalue (`Miri.MIR.Rvalue`). -/
inductive RefRvalue where
  | use (op : RefOperand)
  | binaryOp (op : BinOp) (lhs rhs : RefOperand)
  | unaryOp (op : UnOp) (opnd : RefOperand)
  | ref (mutability : Mutability) (place : RefPlace)
  | addressOf (mutability : Mutability) (place : RefPlace)
  | aggregateTuple (fields : List RefOperand)
  | unsupported

/-- Reference MIR statement (`Miri.MIR.StatementKind`). -/
inductive RefStatementKind where
  | assign (dst : RefPlace) (rvalue : RefRvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported

/-- Reference MIR terminator (`Miri.MIR.TerminatorKind`). -/
inductive RefTerminatorKind where
  | goto (target : BasicBlockId)
  | switchInt (discr : RefOperand) (targets : SwitchTargets)
  | return_
  | unreachable
  | unwindResume
  | assert (cond : RefOperand) (expected : Bool) (msg : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | call (callee : DefId) (args : List RefOperand) (dst : RefPlace)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | unsupported

/-- Reference MIR basic block (`Miri.MIR.BasicBlock`). -/
structure RefBasicBlock where
  statements : List RefStatementKind
  terminator : RefTerminatorKind
  cleanup : Bool := false

/-- Reference MIR function body (`Miri.MIR.Body`) whose local declarations
store `TyId` indices into `RefProg.types`. -/
structure RefBody where
  argumentCount : Nat
  locals : List TyId
  basicBlocks : List RefBasicBlock

/-- Reference program with a single-source deduplicated `types : List MirTy`
table indexed by `TyId`.

Every `Machine` layout hook (`localLayout`, `scalarTypeClass`, `castTypeInfo`,
`pointeeTypes`, and `retagTypeShape`) derives its layout from `types[tyId]?`,
and `initRefState` pre-caches `cachedLayout := some (types[tyId])` on each
`RefLocalState` so `Miri.Interpreter.localToOp` never mutates `frame.locals`
during read-only accesses.

`pointerWidthBits` and `mirProfileVersion` carry `Program.pointerWidthBits` and
`Program.mirProfileVersion` across the codec so that `initRefState`
independently rejects non-64-bit targets and unsupported MIR profile versions,
matching `Trusted.MirSemantics.initState`. -/
structure RefProg where
  bodies : List RefBody
  entryDefId : DefId := 0
  types : List MirTy
  pointerWidthBits : Nat := 64
  mirProfileVersion : Nat := 1

/-! ## Canonical Type Interning and Codec (`encodeProg` / `decodeProg`) -/

/-- Return the first index `i` in `ts` where `MirTy.beq ts[i] ty = true`. -/
noncomputable def indexOfTy : List MirTy → MirTy → Option TyId
  | [], _ => none
  | t :: ts, ty =>
    if MirTy.beq t ty then some 0
    else
      match indexOfTy ts ty with
      | some i => some (i + 1)
      | none => none

/-- Append `ty` to `ts` if and only if no structurally equal type is already
present. -/
noncomputable def insertTy (ty : MirTy) : List MirTy → List MirTy
  | [] => [ty]
  | t :: ts => if MirTy.beq t ty then t :: ts else t :: insertTy ty ts

/-- Resolve `ty` to its interned `TyId` in `ts` (defaulting to `0` if
absent). -/
noncomputable def lookupTyId (ts : List MirTy) (ty : MirTy) : TyId :=
  (indexOfTy ts ty).getD 0

/-- Check that `ts` contains no duplicate `MirTy` entries under `MirTy.beq`. -/
noncomputable def typesAreCanonical : List MirTy → Bool
  | [] => true
  | t :: ts => (indexOfTy ts t).isNone && typesAreCanonical ts

mutual
  /-- Recursively intern all structural sub-types (`pointee` in `.ref`/`.rawPtr`
  and `fields` in `.tuple`) in bottom-up topological order before interning the
  enclosing `MirTy`, guaranteeing that pointee and field layouts are always
  present in `(encodeProg p).types`. -/
  noncomputable def collectTy (acc : List MirTy) : MirTy → List MirTy
    | .bool => insertTy .bool acc
    | .int w s => insertTy (.int w s) acc
    | .unit => insertTy .unit acc
    | .unsupported => insertTy .unsupported acc
    | .ref m p => insertTy (.ref m p) (collectTy acc p)
    | .rawPtr m p => insertTy (.rawPtr m p) (collectTy acc p)
    | .tuple fs => insertTy (.tuple fs) (collectTyList acc fs)

  /-- Intern a list of `MirTy` descriptors left-to-right. -/
  noncomputable def collectTyList (acc : List MirTy) : List MirTy → List MirTy
    | [] => acc
    | ty :: tys => collectTyList (collectTy acc ty) tys
end

/-- Intern any `MirTy` carried inside a `ProjectionElem`. -/
noncomputable def collectProjElem (acc : List MirTy) :
    ProjectionElem → List MirTy
  | .field _ ty => collectTy acc ty
  | .deref | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a projection path. -/
noncomputable def collectProjList (acc : List MirTy) :
    List ProjectionElem → List MirTy
  | [] => acc
  | e :: es => collectProjList (collectProjElem acc e) es

/-- Intern all `MirTy` descriptors carried in `p.projection`. -/
noncomputable def collectPlace (acc : List MirTy) (p : Place) : List MirTy :=
  collectProjList acc p.projection

/-- Intern all `MirTy` descriptors carried in an `Operand`. -/
noncomputable def collectOperand (acc : List MirTy) : Operand → List MirTy
  | .copy p | .move p => collectPlace acc p
  | .constant c => collectTy acc c.ty

/-- Intern all `MirTy` descriptors carried in a list of `Operand`s. -/
noncomputable def collectOperandList (acc : List MirTy) :
    List Operand → List MirTy
  | [] => acc
  | op :: ops => collectOperandList (collectOperand acc op) ops

/-- Intern all `MirTy` descriptors carried in an `Rvalue`. -/
noncomputable def collectRvalue (acc : List MirTy) : Rvalue → List MirTy
  | .use op => collectOperand acc op
  | .binaryOp _ l r => collectOperand (collectOperand acc l) r
  | .unaryOp _ op => collectOperand acc op
  | .ref _ p | .addressOf _ p => collectPlace acc p
  | .aggregateTuple ops => collectOperandList acc ops
  | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `StatementKind`. -/
noncomputable def collectStmt (acc : List MirTy) : StatementKind → List MirTy
  | .assign dst rv => collectRvalue (collectPlace acc dst) rv
  | .storageLive _ | .storageDead _ | .nop | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a statement list. -/
noncomputable def collectStmtList (acc : List MirTy) :
    List StatementKind → List MirTy
  | [] => acc
  | s :: ss => collectStmtList (collectStmt acc s) ss

/-- Intern all `MirTy` descriptors carried in a `TerminatorKind`. -/
noncomputable def collectTerminator (acc : List MirTy) :
    TerminatorKind → List MirTy
  | .switchInt d _ => collectOperand acc d
  | .assert c _ _ _ _ => collectOperand acc c
  | .call _ args dst _ _ => collectPlace (collectOperandList acc args) dst
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => acc

/-- Intern all `MirTy` descriptors carried in a `BasicBlock`. -/
noncomputable def collectBasicBlock (acc : List MirTy)
    (bb : BasicBlock) : List MirTy :=
  collectTerminator (collectStmtList acc bb.statements) bb.terminator

/-- Intern all `MirTy` descriptors carried in a list of `BasicBlock`s. -/
noncomputable def collectBasicBlockList (acc : List MirTy) :
    List BasicBlock → List MirTy
  | [] => acc
  | bb :: bbs => collectBasicBlockList (collectBasicBlock acc bb) bbs

/-- Intern all `MirTy` descriptors in a function `Body`. -/
noncomputable def collectBody (acc : List MirTy) (b : Body) : List MirTy :=
  collectBasicBlockList (collectTyList acc b.locals) b.basicBlocks

/-- Intern all `MirTy` descriptors across a list of `Body` definitions. -/
noncomputable def collectBodyList (acc : List MirTy) : List Body → List MirTy
  | [] => acc
  | b :: bs => collectBodyList (collectBody acc b) bs

/-- Built-in primitive types pre-interned at fixed `TyId`s `0, 1, 2` so
`ExecutionMachine` built-in layout queries (`unitLayout`, `boolLayout`,
`usizeLayout`, including `SwitchInt` case comparisons in
`Miri/Interpreter/ExecutionMachine.lean`) are always in bounds. -/
noncomputable def initTypeTable : List MirTy :=
  [.unit, .bool, .int .isize false]

/-- Collect the canonical deduplicated type table for `p : Program`. -/
noncomputable def collectProgTypes (p : Program) : List MirTy :=
  collectBodyList initTypeTable p.bodies

/-- Encode a `ProjectionElem` against type table `ts`. -/
noncomputable def encodeProjElem (ts : List MirTy) :
    ProjectionElem → RefProjectionElem
  | .deref => .deref
  | .field idx ty => .field idx (lookupTyId ts ty)
  | .unsupported => .unsupported

/-- Encode a list of `ProjectionElem`s against type table `ts`. -/
noncomputable def encodeProjList (ts : List MirTy) :
    List ProjectionElem → List RefProjectionElem
  | [] => []
  | e :: es => encodeProjElem ts e :: encodeProjList ts es

/-- Encode a `Place` against type table `ts`. -/
noncomputable def encodePlace (ts : List MirTy) (p : Place) : RefPlace :=
  ⟨p.localId, encodeProjList ts p.projection⟩

/-- Encode an `Operand` against type table `ts`. -/
noncomputable def encodeOperand (ts : List MirTy) : Operand → RefOperand
  | .copy p => .copy (encodePlace ts p)
  | .move p => .move (encodePlace ts p)
  | .constant c => .constant ⟨lookupTyId ts c.ty, c.lit⟩

/-- Encode a list of `Operand`s against type table `ts`. -/
noncomputable def encodeOperandList (ts : List MirTy) :
    List Operand → List RefOperand
  | [] => []
  | op :: ops => encodeOperand ts op :: encodeOperandList ts ops

/-- Encode an `Rvalue` against type table `ts`. -/
noncomputable def encodeRvalue (ts : List MirTy) : Rvalue → RefRvalue
  | .use op => .use (encodeOperand ts op)
  | .binaryOp op l r => .binaryOp op (encodeOperand ts l) (encodeOperand ts r)
  | .unaryOp op opnd => .unaryOp op (encodeOperand ts opnd)
  | .ref m p => .ref m (encodePlace ts p)
  | .addressOf m p => .addressOf m (encodePlace ts p)
  | .aggregateTuple ops => .aggregateTuple (encodeOperandList ts ops)
  | .unsupported => .unsupported

/-- Encode a `StatementKind` against type table `ts`. -/
noncomputable def encodeStmt (ts : List MirTy) :
    StatementKind → RefStatementKind
  | .assign dst rv => .assign (encodePlace ts dst) (encodeRvalue ts rv)
  | .storageLive id => .storageLive id
  | .storageDead id => .storageDead id
  | .nop => .nop
  | .unsupported => .unsupported

/-- Encode a `TerminatorKind` against type table `ts`. -/
noncomputable def encodeTerminator (ts : List MirTy) :
    TerminatorKind → RefTerminatorKind
  | .goto t => .goto t
  | .switchInt d targets => .switchInt (encodeOperand ts d) targets
  | .return_ => .return_
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert c exp msg t u => .assert (encodeOperand ts c) exp msg t u
  | .call callee args dst t u =>
    .call callee (encodeOperandList ts args) (encodePlace ts dst) t u
  | .unsupported => .unsupported

/-- Encode a `BasicBlock` against type table `ts`. -/
noncomputable def encodeBasicBlock (ts : List MirTy)
    (bb : BasicBlock) : RefBasicBlock :=
  ⟨bb.statements.map (encodeStmt ts),
   encodeTerminator ts bb.terminator,
   bb.cleanup⟩

/-- Encode a `Body` against type table `ts`. -/
noncomputable def encodeBody (ts : List MirTy) (b : Body) : RefBody :=
  ⟨b.argumentCount,
   b.locals.map (lookupTyId ts),
   b.basicBlocks.map (encodeBasicBlock ts)⟩

/-- Total encoder from `Program` to `RefProg`. -/
noncomputable def encodeProg (p : Program) : RefProg :=
  let ts := collectProgTypes p
  ⟨p.bodies.map (encodeBody ts), p.entryDefId, ts, p.pointerWidthBits,
   p.mirProfileVersion⟩

/-- Decode a `RefProjectionElem` against type table `ts`. -/
noncomputable def decodeProjElem (ts : List MirTy) :
    RefProjectionElem → Option ProjectionElem
  | .deref => some .deref
  | .field idx tyId =>
    match MirSemantics.getElem? ts tyId with
    | some ty => some (.field idx ty)
    | none => none
  | .unsupported => some .unsupported

/-- Decode a list of `RefProjectionElem`s against type table `ts`. -/
noncomputable def decodeProjList (ts : List MirTy) :
    List RefProjectionElem → Option (List ProjectionElem)
  | [] => some []
  | e :: es =>
    match decodeProjElem ts e, decodeProjList ts es with
    | some e', some es' => some (e' :: es')
    | _, _ => none

/-- Decode a `RefPlace` against type table `ts`. -/
noncomputable def decodePlace (ts : List MirTy) (p : RefPlace) : Option Place :=
  match decodeProjList ts p.projection with
  | some proj => some ⟨p.localId, proj⟩
  | none => none

/-- Decode a `RefOperand` against type table `ts`. -/
noncomputable def decodeOperand (ts : List MirTy) : RefOperand → Option Operand
  | .copy p =>
    match decodePlace ts p with
    | some p' => some (.copy p')
    | none => none
  | .move p =>
    match decodePlace ts p with
    | some p' => some (.move p')
    | none => none
  | .constant c =>
    match MirSemantics.getElem? ts c.ty with
    | some ty => some (.constant ⟨ty, c.lit⟩)
    | none => none

/-- Decode a list of `RefOperand`s against type table `ts`. -/
noncomputable def decodeOperandList (ts : List MirTy) :
    List RefOperand → Option (List Operand)
  | [] => some []
  | op :: ops =>
    match decodeOperand ts op, decodeOperandList ts ops with
    | some op', some ops' => some (op' :: ops')
    | _, _ => none

/-- Decode a `RefRvalue` against type table `ts`. -/
noncomputable def decodeRvalue (ts : List MirTy) : RefRvalue → Option Rvalue
  | .use op =>
    match decodeOperand ts op with
    | some op' => some (.use op')
    | none => none
  | .binaryOp op l r =>
    match decodeOperand ts l, decodeOperand ts r with
    | some l', some r' => some (.binaryOp op l' r')
    | _, _ => none
  | .unaryOp op opnd =>
    match decodeOperand ts opnd with
    | some opnd' => some (.unaryOp op opnd')
    | none => none
  | .ref m p =>
    match decodePlace ts p with
    | some p' => some (.ref m p')
    | none => none
  | .addressOf m p =>
    match decodePlace ts p with
    | some p' => some (.addressOf m p')
    | none => none
  | .aggregateTuple ops =>
    match decodeOperandList ts ops with
    | some ops' => some (.aggregateTuple ops')
    | none => none
  | .unsupported => some .unsupported

/-- Decode a `RefStatementKind` against type table `ts`. -/
noncomputable def decodeStmt (ts : List MirTy) :
    RefStatementKind → Option StatementKind
  | .assign dst rv =>
    match decodePlace ts dst, decodeRvalue ts rv with
    | some dst', some rv' => some (.assign dst' rv')
    | _, _ => none
  | .storageLive id => some (.storageLive id)
  | .storageDead id => some (.storageDead id)
  | .nop => some .nop
  | .unsupported => some .unsupported

/-- Decode a list of `RefStatementKind`s against type table `ts`. -/
noncomputable def decodeStmtList (ts : List MirTy) :
    List RefStatementKind → Option (List StatementKind)
  | [] => some []
  | s :: ss =>
    match decodeStmt ts s, decodeStmtList ts ss with
    | some s', some ss' => some (s' :: ss')
    | _, _ => none

/-- Decode a `RefTerminatorKind` against type table `ts`. -/
noncomputable def decodeTerminator (ts : List MirTy) :
    RefTerminatorKind → Option TerminatorKind
  | .goto t => some (.goto t)
  | .switchInt d targets =>
    match decodeOperand ts d with
    | some d' => some (.switchInt d' targets)
    | none => none
  | .return_ => some .return_
  | .unreachable => some .unreachable
  | .unwindResume => some .unwindResume
  | .assert c exp msg t u =>
    match decodeOperand ts c with
    | some c' => some (.assert c' exp msg t u)
    | none => none
  | .call callee args dst t u =>
    match decodeOperandList ts args, decodePlace ts dst with
    | some args', some dst' => some (.call callee args' dst' t u)
    | _, _ => none
  | .unsupported => some .unsupported

/-- Decode a `RefBasicBlock` against type table `ts`. -/
noncomputable def decodeBasicBlock (ts : List MirTy)
    (bb : RefBasicBlock) : Option BasicBlock :=
  match decodeStmtList ts bb.statements, decodeTerminator ts bb.terminator with
  | some stmts, some term => some ⟨stmts, term, bb.cleanup⟩
  | _, _ => none

/-- Decode a list of `RefBasicBlock`s against type table `ts`. -/
noncomputable def decodeBasicBlockList (ts : List MirTy) :
    List RefBasicBlock → Option (List BasicBlock)
  | [] => some []
  | bb :: bbs =>
    match decodeBasicBlock ts bb, decodeBasicBlockList ts bbs with
    | some bb', some bbs' => some (bb' :: bbs')
    | _, _ => none

/-- Resolve a list of `TyId` local declarations against type table `ts`. -/
noncomputable def decodeLocalTys (ts : List MirTy) :
    List TyId → Option (List MirTy)
  | [] => some []
  | id :: ids =>
    match MirSemantics.getElem? ts id, decodeLocalTys ts ids with
    | some ty, some tys => some (ty :: tys)
    | _, _ => none

/-- Decode a `RefBody` against type table `ts`. -/
noncomputable def decodeBody (ts : List MirTy) (b : RefBody) : Option Body :=
  match decodeLocalTys ts b.locals, decodeBasicBlockList ts b.basicBlocks with
  | some locals, some bbs => some ⟨b.argumentCount, locals, bbs⟩
  | _, _ => none

/-- Decode a list of `RefBody` definitions against type table `ts`. -/
noncomputable def decodeBodyList (ts : List MirTy) :
    List RefBody → Option (List Body)
  | [] => some []
  | b :: bs =>
    match decodeBody ts b, decodeBodyList ts bs with
    | some b', some bs' => some (b' :: bs')
    | _, _ => none

/-- Total decoder inverting `encodeProg` (`∀ p, decodeProg (encodeProg p) =
some p`). -/
noncomputable def decodeProg (rp : RefProg) : Option Program :=
  match decodeBodyList rp.types rp.bodies with
  | some bodies =>
    some ⟨bodies, rp.entryDefId, rp.pointerWidthBits, rp.mirProfileVersion⟩
  | none => none

/-! ## Reference Machine State and Step Engine ($M_{\text{ref}}$) -/

/-- Reference local slot (`Miri.Interpreter.LocalState` in
`Miri/Interpreter/Stack.lean`), pairing the runtime `slot : LocalSlot` with
`cachedLayout : Option MirTy` pre-populated by `initRefState`. -/
structure RefLocalState where
  slot : LocalSlot
  cachedLayout : Option MirTy

/-- Reference call-stack frame (`Miri.Interpreter.Frame` in
`Miri/Interpreter/Stack.lean`).

`returnContinuation` distinguishes the two kinds of frames that the reference
stack holds: `false` marks a frame that executes `defId`'s body, and `true`
marks a suspended caller frame that only receives a callee's return value
(`callerSentinelFrame`). `evalRefStep` executes only the top frame and requires
it to be an executing frame. -/
structure RefFrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List RefLocalState
  returnContinuation : Bool := false

/-- Caller sentinel frame beneath the entry function's frame.

$M_{\text{ref}}$ represents the caller of the entry function as an explicit
frame that owns the entry function's return place. In `lean-miri`,
`MainThread.callMain` (`vendor/lean-miri/Miri/Interpreter/MainThread.lean`)
allocates the return place `retPlace` before it calls the entry function, so
that place outlives the entry frame. The sentinel models this caller-owned
place as a single live destination slot (`_0`) of the entry function's return
type `retTy`.

The sentinel never executes a statement and is marked as a suspended caller
(`returnContinuation := true`). `initRefState` places it beneath the entry
frame, and `evalRefStep` requires it and preserves it on every running step,
so the reference stack has one fixed shape. Returning from the entry frame
ends the execution with `.returned` (`evalRefTerminator`) instead of resuming
the sentinel. Its `defId`, `blockIdx`, and `stmtIdx` are unused. -/
noncomputable def callerSentinelFrame (retTy : MirTy) : RefFrameState := {
  defId := 0
  blockIdx := 0
  stmtIdx := 0
  locals := [⟨liveUninitSlot retTy, some retTy⟩]
  returnContinuation := true
}

/-- Reference machine state (`Miri.Interpreter.ExecutionMachine.ExecutionState`
paired with `Limits.maxSteps`): tracks `stepsExecuted : Nat` and `maxSteps :
Nat` explicitly so `RefWellFormed` and `RefBehavior` quantify over the step
budget without mutating `ExecutionMachine.step`'s transition relation. -/
structure RefState where
  frames : List RefFrameState
  callerMem : CallerMemory
  stepsExecuted : Nat := 0
  maxSteps : Nat := 0

/-- Five-way step outcome of `Miri.Interpreter.ExecutionMachine.step`
(`Miri/Interpreter/ExecutionMachine.lean`). -/
inductive RefOutcome where
  | running (next : RefState)
  | returned (out : TerminalOut)
  | exhaustedStepLimit
  | ub
  | blocked

/-- Admissible demonic choice predicate in $M_{\text{ref}}$. -/
noncomputable def ValidRefChoice (_rp : RefProg) (_rs : RefState)
    (c : Choice) : Prop :=
  c = 0

/-- Map $M_{\text{anneal}}$'s two fault poles to $M_{\text{ref}}$'s `.ub` and
`.blocked` outcomes. -/
noncomputable def faultToRefOutcome : FaultKind → RefOutcome
  | .undefined => .ub
  | .unsupported => .blocked

/-- Convert the `StepResult` of executing the top frame's statement or
terminator into a `RefOutcome`.

Statement and terminator evaluators rebuild only the top frame
(`frames := [rframe']`). On `.step`, this function restores the caller
`sentinel` beneath that frame and increments `stepsExecuted`. -/
noncomputable def stepResultToRefOutcome (sentinel : RefFrameState)
    (stepsExecuted maxSteps : Nat) :
    StepResult RefState TerminalOut → RefOutcome
  | .step rs' =>
    .running {
      rs' with
      frames := sentinel :: rs'.frames
      stepsExecuted := stepsExecuted + 1
      maxSteps := maxSteps
    }
  | .done out => .returned out
  | .fault k => faultToRefOutcome k

/-- Whether `RefStatementKind` is a `StorageLive` or `StorageDead` annotation
for `localId`. -/
noncomputable def refStmtHasStorageMarker (localId : LocalId) :
    RefStatementKind → Bool
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Whether `rbody` contains a `StorageLive` or `StorageDead` annotation for
`localId`. -/
noncomputable def refHasStorageAnnotation (rbody : RefBody)
    (localId : LocalId) : Bool :=
  rbody.basicBlocks.any (fun bb =>
    bb.statements.any (refStmtHasStorageMarker localId))

/-- Check that all `StorageLive` and `StorageDead` local indices in `rbody` are
in bounds (`< rbody.locals.length`). -/
noncomputable def refStorageAnnotationsInBounds (rbody : RefBody) : Bool :=
  let numLocals := rbody.locals.length
  rbody.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true))

/-- Map an Anneal `IntWidth` to its `Miri.ABI.Size` in bytes (`1`, `2`, `4`,
`8`, or `16` bytes on 64-bit targets). -/
noncomputable def toMiriSize : IntWidth → Miri.ABI.Size
  | .i8 => Miri.ABI.Size.ofBytes 1
  | .i16 => Miri.ABI.Size.ofBytes 2
  | .i32 => Miri.ABI.Size.ofBytes 4
  | .i64 => Miri.ABI.Size.ofBytes 8
  | .i128 => Miri.ABI.Size.ofBytes 16
  | .isize => Miri.ABI.Size.ofBytes 8

/-- Map `(w, signed)` to `Miri.MIR.IntegerKind`
(`vendor/lean-miri/Miri/MIR/Operators.lean`). -/
noncomputable def toMiriIntKind :
    IntWidth → Bool → Miri.MIR.IntegerKind
  | .i8, true => .i8
  | .i8, false => .u8
  | .i16, true => .i16
  | .i16, false => .u16
  | .i32, true => .i32
  | .i32, false => .u32
  | .i64, true => .i64
  | .i64, false => .u64
  | .i128, true => .i128
  | .i128, false => .u128
  | .isize, true => .isize
  | .isize, false => .usize

/-- Construct the `Miri.Interpreter.IntegerType` for `(w, signed)`. -/
noncomputable def toMiriIntType (w : IntWidth) (s : Bool) :
    Miri.Interpreter.IntegerType :=
  ⟨toMiriSize w, toMiriIntKind w s⟩

/-- Construct a `Miri.Memory.ScalarInt` at width `w` via
`Miri.Memory.ScalarInt.truncateFromUInt`. -/
noncomputable def miriScalar (w : IntWidth) (bits : BitVec 128) :
    Miri.Memory.ScalarInt :=
  match Miri.Memory.ScalarInt.truncateFromUInt bits (toMiriSize w) with
  | .ok (sc, _) => sc
  | .error _ => Miri.Memory.ScalarInt.ofUInt128 bits

/-- Lift a `ScalarVal` into a `Miri.Interpreter.IntegerValue`. -/
noncomputable def miriIntValue (sv : ScalarVal) :
    Miri.Interpreter.IntegerValue :=
  ⟨miriScalar sv.width sv.bits, toMiriIntType sv.width sv.signed⟩

/-- Map `Trusted.MirAst.UnOp` to `Miri.MIR.UnOp`. -/
noncomputable def toMiriUnOp : UnOp → Miri.MIR.UnOp
  | .not => .Not
  | .neg => .Neg
  | .ptrMetadata => .PtrMetadata

/-- Map `Trusted.MirAst.BinOp` to `Miri.MIR.BinOp`. -/
noncomputable def toMiriBinOp : BinOp → Miri.MIR.BinOp
  | .add => .Add
  | .addUnchecked => .AddUnchecked
  | .addWithOverflow => .AddWithOverflow
  | .sub => .Sub
  | .subUnchecked => .SubUnchecked
  | .subWithOverflow => .SubWithOverflow
  | .mul => .Mul
  | .mulUnchecked => .MulUnchecked
  | .mulWithOverflow => .MulWithOverflow
  | .div => .Div
  | .rem => .Rem
  | .bitXor => .BitXor
  | .bitAnd => .BitAnd
  | .bitOr => .BitOr
  | .shl => .Shl
  | .shlUnchecked => .ShlUnchecked
  | .shr => .Shr
  | .shrUnchecked => .ShrUnchecked
  | .eq => .Eq
  | .lt => .Lt
  | .le => .Le
  | .ne => .Ne
  | .ge => .Ge
  | .gt => .Gt
  | .offset => .Offset

/-- Reference constant-literal decoder calling
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.Memory.ScalarInt.tryToBool`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`), matching
`ScalarInt::try_from_uint` and `ScalarInt::try_to_bool` in
`compiler/rustc_middle/src/mir/interpret/value.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, lossy) = Self::truncate_from_uint(i, size);
>     if lossy { None } else { Some(r) }
> }"
>
> "pub fn try_to_bool(self) -> InterpResult<'tcx, bool> {
>     match self.to_u8()? {
>         0 => interp_ok(false),
>         1 => interp_ok(true),
>         _ => err_ub!(InvalidBool(self.to_u8()?)),
>     }
> }"
> (`compiler/rustc_middle/src/mir/interpret/value.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefConstLit : MirTy → ConstLit → Except FaultKind Val
  | .int w s, .scalar bits =>
    match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize w) with
    | .ok (some sc) => .ok (.scalar ⟨w, s, sc.data⟩)
    | _ => .error .unsupported
  | .bool, .scalar bits =>
    match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => .ok (.bool b)
      | .error (.invalidBool _) => .error .undefined
      | .error _ => .error .unsupported
    | _ => .error .unsupported
  | .unit, .zeroSized => .ok .unit
  | _, _ => .error .unsupported

/-- Reference unary operator evaluator calling
`Miri.Interpreter.IntegerOps.unary`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`), matching `unary_op` in
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn unary_op(&self, un_op: mir::UnOp, val: &ImmTy<'tcx, M::Provenance>)
> -> InterpResult<'tcx, ImmTy<'tcx, M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefUnOp (op : UnOp) (v : Val) : Except FaultKind Val :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | _, .scalar sv =>
    match Miri.Interpreter.IntegerOps.unary
        (toMiriUnOp op) (miriIntValue sv) with
    | .ok sc => .ok (.scalar ⟨sv.width, sv.signed, sc.data⟩)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Reference binary operator evaluator calling
`Miri.Interpreter.IntegerOps.binary` and
`Miri.Interpreter.IntegerOps.binaryBool`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`), matching `binary_op` in
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn binary_op(&self, bin_op: mir::BinOp, left: &ImmTy<'tcx,
> M::Provenance>, right: &ImmTy<'tcx, M::Provenance>) -> InterpResult<'tcx,
> ImmTy<'tcx, M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefBinOp (op : BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    match op with
    | .addWithOverflow | .subWithOverflow | .mulWithOverflow | .offset =>
      .error .unsupported
    | _ =>
      match Miri.Interpreter.IntegerOps.binary
          (toMiriBinOp op) (miriIntValue l) (miriIntValue r) with
      | .ok (.scalar sc) => .ok (.scalar ⟨l.width, l.signed, sc.data⟩)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported
  | .bool l, .bool r =>
    match op with
    | .addWithOverflow | .subWithOverflow | .mulWithOverflow | .offset =>
      .error .unsupported
    | _ =>
      match Miri.Interpreter.IntegerOps.binaryBool (toMiriBinOp op) l r with
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Reference scalar/boolean/unit value validity and type check calling
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.Memory.ScalarInt.ofBool`. -/
noncomputable def checkRefVal (v : Val) (ty : MirTy) : Bool :=
  match v, ty with
  | .scalar sv, .int w s =>
    match Miri.Memory.ScalarInt.tryFromUInt sv.bits (toMiriSize sv.width) with
    | .ok (some _) => IntWidth.beq sv.width w && (sv.signed == s)
    | _ => false
  | .bool b, .bool =>
    match (Miri.Memory.ScalarInt.ofBool b).tryToBool with
    | .ok _ => true
    | .error _ => false
  | .unit, .unit => true
  | _, _ => false

/-- Check that argument list `vs` matches parameter types `tys` under
`checkRefVal`. -/
noncomputable def checkRefArgsMatch : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkRefVal v ty && checkRefArgsMatch vs tys
  | _, _ => false

/-- Reference `SwitchInt` branch comparator calling
`Miri.Memory.ScalarInt.tryFromUInt` on each case literal and
`Miri.Memory.ScalarInt.truncateFromUInt` on the discriminant bits, matching
`compareSwitchCase` (`Scalar.fromUInt` -> `ScalarInt.tryFromUInt`) in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`),
`ScalarInt::try_from_uint` in `compiler/rustc_middle/src/ty/consts/int.rs`, and
`SwitchInt` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "for (const_int, target) in targets.iter() {
>     let res = self.binary_op(
>         mir::BinOp::Eq,
>         &discr,
>         &ImmTy::from_uint(const_int, discr.layout),
>     )?;
>     if res.to_scalar().to_bool()? {
>         target_block = target;
>         break;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefSwitchBranches (w : IntWidth) (discrBits : BitVec 128)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    let sz := toMiriSize w
    match Miri.Memory.ScalarInt.tryFromUInt caseBits sz,
          Miri.Memory.ScalarInt.truncateFromUInt discrBits sz with
    | .ok (some caseSc), .ok (discrSc, _) =>
      if discrSc.data == caseSc.data then
        .ok target
      else
        evalRefSwitchBranches w discrBits otherwise rest
    | _, _ => .error .unsupported

/-- Reference `SwitchInt` boolean-branch comparator calling
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.Memory.ScalarInt.tryToBool`
(via `evalRefConstLit .bool`), matching `compareSwitchCase` in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`) and `SwitchInt`
equality comparison (`self.binary_op(mir::BinOp::Eq, &discr, &value)?`) in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def evalRefBoolSwitchBranches (discr : Bool)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    match evalRefConstLit .bool (.scalar caseBits) with
    | .ok (.bool false) =>
      if !discr then .ok target
      else evalRefBoolSwitchBranches discr otherwise rest
    | .ok (.bool true) =>
      if discr then .ok target
      else evalRefBoolSwitchBranches discr otherwise rest
    | .error k =>
      .error k
    | .ok _ =>
      .error .unsupported

/-- Initialize `RefLocalState` slots at function entry, pre-populating
`cachedLayout := some ty` on every slot, matching `initFrameLocals` in
`Miri.Interpreter.CallMachine` and
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "self.storage_live(mir::RETURN_PLACE)?;
> let always_live = always_storage_live_locals(body);
> for local in body.vars_and_temps_iter() {
>     if always_live.contains(local) {
>         self.storage_live(local)?;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def initRefLocalsLoop (rbody : RefBody) (args : List Val) :
    Nat → List MirTy → List RefLocalState
  | _, [] => []
  | idx, ty :: rest =>
      let slot : LocalSlot :=
        if Nat.beq idx 0 then
          liveUninitSlot ty
        else if Nat.ble idx rbody.argumentCount then
          match MirSemantics.getElem? args (idx - 1) with
          | some v => .live (some v)
          | none => .dead
        else if refHasStorageAnnotation rbody idx then
          .dead
        else
          liveUninitSlot ty
      ⟨slot, some ty⟩ :: initRefLocalsLoop rbody args (idx + 1) rest

/-- Entry initialization of $M_{\text{ref}}$ (`initRefState rp q maxSteps`):
resolves `rbody.locals` against `rp.types`, pre-populates `cachedLayout := some
ty` on every local, and initializes `stepsExecuted := 0` and
`maxSteps := maxSteps`.

Like `Trusted.MirSemantics.initState`, it first rejects programs captured for
a target whose pointer width is not 64 bits or whose `mirProfileVersion` is not
1. The initial stack is `[callerSentinelFrame retTy, rframe]`, where `retTy` is
the type of the entry function's return place `_0` and `rframe` executes the
entry body. -/
noncomputable def initRefState (rp : RefProg) (q : Query)
    (maxSteps : Nat) : Except FaultKind RefState :=
  if !Nat.beq rp.pointerWidthBits 64 || !Nat.beq rp.mirProfileVersion 1 then
    .error .unsupported
  else if !q.callerMem.allocations.isEmpty then
    .error .unsupported
  else
    match MirSemantics.getElem? rp.bodies rp.entryDefId with
    | none => .error .unsupported
    | some rbody =>
      match decodeLocalTys rp.types rbody.locals with
      | none => .error .unsupported
      | some localTys =>
        if rbody.basicBlocks.isEmpty then
          .error .unsupported
        else if !Nat.blt rbody.argumentCount localTys.length then
          .error .unsupported
        else if !refStorageAnnotationsInBounds rbody then
          .error .unsupported
        else if !localTys.all isSupportedScalarOrUnitTy then
          .error .unsupported
        else
          let paramTys := (localTys.drop 1).take rbody.argumentCount
          if !checkRefArgsMatch q.args paramTys then
            .error .unsupported
          else
            -- `argumentCount < localTys.length` makes `_0` present here; the
            -- `none` arm keeps the definition total and fails closed.
            match MirSemantics.getElem? localTys 0 with
            | none => .error .unsupported
            | some retTy =>
              let rlocals := initRefLocalsLoop rbody q.args 0 localTys
              let rframe : RefFrameState := {
                defId := rp.entryDefId
                blockIdx := 0
                stmtIdx := 0
                locals := rlocals
                returnContinuation := false
              }
              .ok {
                frames := [callerSentinelFrame retTy, rframe]
                callerMem := q.callerMem
                stepsExecuted := 0
                maxSteps := maxSteps
              }

/-! ### `Miri.Interpreter` Evaluator Wiring Adapters -/

/-- Canonical 8-byte sized `Miri.Interpreter.LocalLayout` (`isZst = false`) used
for Day 1 non-unit local frame slots in
`Miri.Interpreter.{evalOperand,placeWriteLocalImmediate,evalRvalueIntoPlace,
Step.evalStatement,ControlFlow.evalTerminator}`. -/
noncomputable def refSizedLocalLayout : Miri.Interpreter.LocalLayout := {
  ty := 0
  layout := {
    fields := .Primitive
    variants := .Single 0
    backendRepr := .Memory (sized := true)
    largestNiche := none
    uninhabited := false
    align := Miri.ABI.AbiAlign.new Miri.ABI.Align.ONE
    size := Miri.ABI.Size.ofBytes 8
    maxReprAlign := none
    unadjustedAbiAlign := Miri.ABI.Align.ONE
    reprC := false
    randomizationSeed := 0
  }
}

/-- Canonical 0-byte ZST `Miri.Interpreter.LocalLayout` (`Size.ZERO`,
`isZst = true`) used for `MirTy.unit` local frame slots. -/
noncomputable def refLocalLayoutZst : Miri.Interpreter.LocalLayout := {
  refSizedLocalLayout with
  layout := {
    refSizedLocalLayout.layout with
    size := Miri.ABI.Size.ZERO
  }
}

/-- `Miri.Interpreter.LocalLayout` for a Day 1 scalar or unit local slot:
0-byte ZST (`refLocalLayoutZst`, `isZst = true`) for `MirTy.unit`, and 8-byte
sized layout (`refSizedLocalLayout`, `isZst = false`) for non-unit types. -/
noncomputable def refLocalLayoutForTy : MirTy → Miri.Interpreter.LocalLayout
  | .unit => refLocalLayoutZst
  | _ => refSizedLocalLayout

/-- Embed `optVal : Option Val` into `Miri.Interpreter.Immediate (Option Val)`
via `Miri.Memory.Scalar.fromPointer` without pattern-matching on `optVal` so
projection back via `miriImmediateToOptVal` reduces by `rfl` even when `optVal`
is a free variable. -/
noncomputable def optValToMiriImmediate (optVal : Option Val) :
    Miri.Interpreter.Immediate (Option Val) :=
  .scalar (Miri.Memory.Scalar.fromPointer ⟨.big, .w64⟩
    ⟨Miri.ABI.Size.ZERO, optVal⟩)

/-- Project `optVal : Option Val` back out of
`Miri.Interpreter.Immediate (Option Val)`. -/
noncomputable def miriImmediateToOptVal :
    Miri.Interpreter.Immediate (Option Val) → Option Val
  | .scalar s =>
    match s.toBitsOrPtrInternal (Miri.ABI.Size.ofBytes 8) with
    | .ok (.pointer ptr) => ptr.provenance
    | _ => none
  | _ => none

/-- Lift a `LocalSlot` into `Miri.Interpreter.LocalValue (Option Val)`. -/
noncomputable def slotToMiriLocalValue :
    LocalSlot → Miri.Interpreter.LocalValue (Option Val)
  | .dead => .dead
  | .live optVal => .live (.immediate (optValToMiriImmediate optVal))

/-- Minimal `Miri.MIR.BasicBlock` with configurable `cleanup : Bool` for
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`. -/
noncomputable def refDummyMirBlock (cleanup : Bool) : Miri.MIR.BasicBlock := {
  statements := Array.empty
  terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  cleanup := cleanup
}

/-- Minimal `Miri.MIR.Body` with two local declarations (`_0` and `_1`) and one
basic block for `Miri.Interpreter.Frame`. -/
noncomputable def refDummyMirBody (cleanup : Bool) : Miri.MIR.Body := {
  phase := .Runtime .PostCleanup
  argumentCount := 0
  spreadArgument := none
  locals := Array.mk [0, 0]
  basicBlocks := Array.mk [refDummyMirBlock cleanup]
}

/-- Construct a single-local `Miri.Interpreter.Frame` holding `lv` at local `0`
with pre-cached `layout`. -/
noncomputable def mkSingleLocalMiriFrameWithLayout
    (lv : Miri.Interpreter.LocalValue (Option Val))
    (layout : Miri.Interpreter.LocalLayout) (cleanup : Bool) :
    Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit := {
  body := refDummyMirBody cleanup
  bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex 0
  functionInstance := { kind := .Item 0, args := Array.empty }
  extra := ()
  returnContinuation := .stop false
  returnPlace := .frameLocal 0 0 none layout
    (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
  localsIdentity := Miri.Interpreter.LocalsIdentity.ofAllocationToken 0
  locals := Array.mk [⟨lv, some layout⟩]
  vaList := Array.empty
  trackCallerArg := none
  location := .mir ⟨0, 0⟩
}

/-- Construct a single-local `Miri.Interpreter.Frame` holding `lv` at local `0`
with pre-cached `refSizedLocalLayout`. -/
noncomputable def mkSingleLocalMiriFrame
    (lv : Miri.Interpreter.LocalValue (Option Val)) (cleanup : Bool) :
    Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit :=
  mkSingleLocalMiriFrameWithLayout lv refSizedLocalLayout cleanup

/-- Construct a two-local `Miri.Interpreter.Frame` holding `lv₀` at `_0` and
`lv₁` at `_1` for `Miri.Interpreter.Frame.storageDead` (which forbids
`StorageDead` on return place `_0` and deallocates `_1`). -/
noncomputable def mkTwoLocalMiriFrame
    (lv₀ lv₁ : Miri.Interpreter.LocalValue (Option Val)) :
    Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit := {
  mkSingleLocalMiriFrame lv₀ false with
  locals := Array.mk [⟨lv₀, some refSizedLocalLayout⟩,
                      ⟨lv₁, some refSizedLocalLayout⟩]
}

/-- `Miri.Interpreter.LocalAccessHooks` with `deinitMovedPlace` configured for
`Miri.Interpreter.evalOperand`. -/
noncomputable def refLocalAccessHooks (deinitMovedPlace : Bool) :
    Miri.Interpreter.LocalAccessHooks (Option Val) Unit Unit := {
  layout := fun frame state _ _ => ⟨frame, state, .ok refSizedLocalLayout⟩
  validationInProgress := fun _ => true
  afterLocalRead := fun frame state _ => ⟨frame, state, .ok ()⟩
  project := fun frame state _ _ =>
    ⟨frame, state, .error (.resolver "projections unsupported on Day 1")⟩
  checkPlaceType := fun frame state _ _ => ⟨frame, state, .ok ()⟩
  runtimeChecks := fun frame state _ =>
    ⟨frame, state, .error (.resolver "runtimeChecks unsupported")⟩
  constant := fun frame state _ _ =>
    ⟨frame, state, .error (.resolver "constant handled via evalRefConstLit")⟩
  deinitMovedPlace := deinitMovedPlace
}

/-- Run `Miri.Interpreter.evalOperand` on `.Move ⟨0, Array.empty⟩` with
`deinitMovedPlace = true` and `refLocalLayoutForTy ty`, returning both the read
value `optVal` and the post-move `LocalSlot` projected from
`frame₁.getLocal 0`. -/
noncomputable def evalMiriMoveOperand (slot : LocalSlot) (ty : MirTy) :
    Option (Option Val × LocalSlot) :=
  let layout := refLocalLayoutForTy ty
  let frame₀ :=
    mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue slot) layout false
  match Miri.Interpreter.evalOperand (refLocalAccessHooks true) frame₀ ()
      (.Move ⟨0, Array.empty⟩) (some layout) with
  | ⟨frame₁, _, .ok ⟨.immediate imm, outLayout⟩⟩ =>
    match frame₁.getLocal 0 with
    | .ok ⟨.live (.immediate .uninit), _⟩ =>
      some (miriImmediateToOptVal imm, .live none)
    | .ok ⟨.live (.immediate _), _⟩ =>
      if outLayout.layout.isZst then
        some (miriImmediateToOptVal imm, .live (some .unit))
      else
        none
    | _ => none
  | _ => none

/-- Stage 1 of reference operand evaluation calling
`Miri.Interpreter.evalOperand`
(`vendor/lean-miri/Miri/Interpreter/LocalAccess.lean`) with
`deinitMovedPlace = true`, matching `eval_operand` in
`compiler/rustc_const_eval/src/interpret/operand.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_operand(&mut self, mir_op: &mir::Operand<'tcx>,
> layout: Option<TyAndLayout<'tcx>>) -> InterpResult<'tcx, OpTy<'tcx,
> M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Reads `(slot, cachedLayout)` from `rlocals[place.localId]`, and when
`opnd = .move place` on an unprojected live local, delegates ZST-aware move
deinitialization to `evalMiriMoveOperand` (`Miri.Interpreter.evalOperand` with
`refLocalLayoutForTy ty`). -/
noncomputable def evalRefOperandToSlot (types : List MirTy)
    (rlocals : List RefLocalState) :
    RefOperand → Except FaultKind (MirTy × Option Val × List RefLocalState)
  | .copy place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match MirSemantics.getElem? rlocals place.localId with
      | some ⟨slot, some ty⟩ =>
        let layout := refLocalLayoutForTy ty
        let frame₀ :=
          mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue slot) layout
            false
        match Miri.Interpreter.evalOperand (refLocalAccessHooks true) frame₀ ()
            (.Copy ⟨0, Array.empty⟩) (some layout) with
        | ⟨_, _, .ok ⟨.immediate imm, _⟩⟩ =>
          .ok (ty, miriImmediateToOptVal imm, rlocals)
        | _ => .error .undefined
      | _ => .error .unsupported
  | .move place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match MirSemantics.getElem? rlocals place.localId with
      | some ⟨slot, some ty⟩ =>
        match evalMiriMoveOperand slot ty with
        | some (optVal, postSlot) =>
          match MirSemantics.setElem? rlocals place.localId
              ⟨postSlot, some ty⟩ with
          | some rlocals' => .ok (ty, optVal, rlocals')
          | none => .error .unsupported
        | none => .error .undefined
      | _ => .error .unsupported
  | .constant c =>
    match MirSemantics.getElem? types c.ty with
    | none => .error .unsupported
    | some ty =>
      match evalRefConstLit ty c.lit with
      | .ok v => .ok (ty, some v, rlocals)
      | .error k => .error k

/-- Stage 2A of reference operand evaluation (`evalRefOperandToSlot` followed by
`MemoryOperand.readImmediate`). -/
noncomputable def evalRefPrimitiveOperand (types : List MirTy)
    (rlocals : List RefLocalState) (opnd : RefOperand) :
    Except FaultKind (Val × List RefLocalState) :=
  match evalRefOperandToSlot types rlocals opnd with
  | .error k => .error k
  | .ok (ty, optVal, rlocals') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, rlocals')
      | none => .error .undefined

/-- Map `RefRvalue` to its corresponding `Miri.MIR.Rvalue` constructor for
`Miri.Interpreter.evalRvalueIntoPlace`. -/
noncomputable def toMiriRvalueForDispatch : RefRvalue → Miri.MIR.Rvalue
  | .use _ => .Use (.Copy ⟨0, Array.empty⟩) .No
  | .binaryOp op _ _ =>
    .BinaryOp (toMiriBinOp op) (.Copy ⟨0, Array.empty⟩) (.Copy ⟨1, Array.empty⟩)
  | .unaryOp op _ => .UnaryOp (toMiriUnOp op) (.Copy ⟨0, Array.empty⟩)
  | _ => .CopyForDeref ⟨0, Array.empty⟩

/-- `Miri.Interpreter.RvalueHooks` used to dispatch and execute
`Miri.MIR.Rvalue` through `Miri.Interpreter.evalRvalueIntoPlace` and
`Miri.Interpreter.runRvalue`
(`vendor/lean-miri/Miri/Interpreter/Rvalue.lean`). -/
noncomputable def refRvalueHooksFor (types : List MirTy)
    (rlocals : List RefLocalState) (dstTy : MirTy) (rrv : RefRvalue) :
    Miri.Interpreter.RvalueHooks (Option Val)
      (Option (Except FaultKind (Val × List RefLocalState))) Unit Unit := {
  placeLayout := fun _ => refSizedLocalLayout
  evalPlace := fun _ _ _ s => .ok () s
  evalOperand := fun _ _ _ s =>
    .ok ⟨.immediate .uninit, refSizedLocalLayout⟩ s
  evalPlaceToOp := fun _ _ _ s =>
    .ok ⟨.immediate .uninit, refSizedLocalLayout⟩ s
  readImmediate := fun _ _ s =>
    .ok ⟨.uninit, refSizedLocalLayout⟩ s
  writeImmediate := fun _ _ _ s => .ok () s
  writePointer := fun _ _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  threadLocalPointer := fun _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  withRetagMode := fun _ _ act => act
  copyOp := fun _ _ _ _ =>
    let res :=
      match rrv with
      | .use opnd =>
        match evalRefOperandToSlot types rlocals opnd with
        | .error k => .error k
        | .ok (srcTy, optVal, rlocals₁) =>
          if !(MirTy.beq srcTy dstTy) then
            .error .unsupported
          else
            match optVal with
            | some v => .ok (v, rlocals₁)
            | none => .error .undefined
      | _ => .error .unsupported
    .ok () (some res)
  copyOpAllowTransmute := fun _ _ _ s => .ok () s
  binaryOp := fun _ _ _ _ _ =>
    let res :=
      match rrv with
      | .binaryOp op lhs rhs =>
        match evalRefPrimitiveOperand types rlocals lhs with
        | .error k => .error k
        | .ok (lVal, rlocals₁) =>
          match evalRefPrimitiveOperand types rlocals₁ rhs with
          | .error k => .error k
          | .ok (rVal, rlocals₂) =>
            match evalRefBinOp op lVal rVal with
            | .error k => .error k
            | .ok v => .ok (v, rlocals₂)
      | _ => .error .unsupported
    .ok ⟨.uninit, refSizedLocalLayout⟩ (some res)
  unaryOp := fun _ _ _ _ =>
    let res :=
      match rrv with
      | .unaryOp op opnd =>
        match evalRefPrimitiveOperand types rlocals opnd with
        | .error k => .error k
        | .ok (v, rlocals₁) =>
          match evalRefUnOp op v with
          | .error k => .error k
          | .ok u => .ok (u, rlocals₁)
      | _ => .error .unsupported
    .ok ⟨.uninit, refSizedLocalLayout⟩ (some res)
  writeAggregate := fun _ _ _ _ s =>
    .error (.unsupported "Aggregate unsupported on Day 1") s
  writeRepeat := fun _ _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  forceAllocation := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported on Day 1") s
  toRef := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported on Day 1") s
  enforceValidity := fun _ _ s => .ok false s
  retagPtrValue := fun _ _ _ s => .ok none s
  placeBaseRaw := fun _ _ s => .ok false s
  normalize := fun _ ty s => .ok ty s
  cast := fun _ _ _ _ _ s =>
    .error (.unsupported "Cast unsupported") s
  readDiscriminant := fun _ _ s =>
    .error (.unsupported "Discriminant unsupported") s
  discriminantForVariant := fun _ _ _ s =>
    .error (.unsupported "Discriminant unsupported") s
}

/-- Reference rvalue evaluator delegating outer dispatch and execution to
`Miri.Interpreter.evalRvalueIntoPlace` and `Miri.Interpreter.runRvalue`
(`vendor/lean-miri/Miri/Interpreter/Rvalue.lean`), matching
`eval_rvalue_into_place` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_rvalue_into_place(&mut self, rvalue: &mir::Rvalue<'tcx>,
> place: mir::Place<'tcx>) -> InterpResult<'tcx>"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefRvalue (types : List MirTy)
    (rlocals : List RefLocalState) (dstTy : MirTy) (rrv : RefRvalue) :
    Except FaultKind (Val × List RefLocalState) :=
  match Miri.Interpreter.runRvalue
      (Miri.Interpreter.evalRvalueIntoPlace
        (refRvalueHooksFor types rlocals dstTy rrv) ()
        (toMiriRvalueForDispatch rrv) ⟨0, Array.empty⟩) none with
  | (some res, .ok ()) => res
  | _ => .error .unsupported

/-- Write `val` into destination local `dstLocalId` in `rlocals` via
`Miri.Interpreter.placeWriteLocalImmediate`
(`vendor/lean-miri/Miri/Interpreter/Place.lean`), preserving its cached layout
`some ty`. -/
noncomputable def writeRefPlace (rlocals : List RefLocalState)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List RefLocalState) :=
  if !checkRefVal val dstTy then
    .error .unsupported
  else
    match MirSemantics.getElem? rlocals dstLocalId with
    | some ⟨slot, some ty⟩ =>
      let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
      match Miri.Interpreter.placeWriteLocalImmediate
          EStateM.get EStateM.set (pure true)
          (fun _ _ => pure ()) (fun _ _ => pure ())
          0 refSizedLocalLayout (optValToMiriImmediate (some val)) frame₀ with
      | .ok () frame₁ =>
        match frame₁.getLocal 0,
            MirSemantics.setElem? rlocals dstLocalId
              ⟨.live (some val), some ty⟩ with
        | .ok ⟨.live (.immediate _), _⟩, some rlocals' => .ok rlocals'
        | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
        | _, _ => .error .undefined
      | .error _ _ => .error .undefined
    | _ => .error .unsupported

/-- `Miri.Interpreter.LocalStorageHooks` for
`Miri.Interpreter.Frame.storageLive` and
`Miri.Interpreter.Frame.storageDead`. -/
noncomputable def refLocalStorageHooks :
    Miri.Interpreter.LocalStorageHooks
      (Option Val) Miri.Interpreter.LocalLayout Unit Unit := {
  veryTriviallySized := fun _ => .ok true
  layout := fun s _ _ => ⟨s, .ok refSizedLocalLayout⟩
  isSized := fun _ => true
  afterLocalWrite := fun s _ _ => ⟨s, .ok ()⟩
  allocateDyn := fun s _ _ =>
    ⟨s, .error (.allocationFailure "unsized local unsupported")⟩
  deallocateStack := fun s _ => ⟨s, .ok ()⟩
}

/-- Minimal `Miri.Interpreter.StepState` for
`Miri.Interpreter.ControlFlow.goToBlock` and
`Miri.Interpreter.ControlFlow.evalTerminator`. -/
noncomputable def mkRefStepState (cleanup : Bool) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      (Option (StepResult RefState TerminalOut)) := {
  stack := ⟨Array.mk [mkSingleLocalMiriFrame .dead cleanup]⟩
  machine := none
}

/-- Minimal `Miri.Interpreter.StepState` with a single statement `stmt` at
location `.mir ⟨0, 0⟩` so `Miri.Interpreter.Step.step` executes its statement
dispatch and statement-index increment path. -/
noncomputable def mkRefStmtStepState (stmt : Miri.MIR.Statement) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      (Option (StepResult RefState TerminalOut)) := {
  stack := ⟨Array.mk [{
    mkSingleLocalMiriFrame .dead false with
    body := {
      refDummyMirBody false with
      basicBlocks := Array.mk [{
        statements := Array.mk [stmt]
        terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
        cleanup := false
      }]
    }
  }]⟩
  machine := none
}

/-- Minimal `Miri.Interpreter.StepState` at terminator position
(`statements := Array.empty`, `location := .mir ⟨0, 0⟩`) so
`Miri.Interpreter.Step.step` executes its `beforeTerminator` + `terminator`
(`Miri.Interpreter.ControlFlow.evalTerminator`) path. -/
noncomputable def mkRefTermStepState (term : Miri.MIR.Terminator)
    (cleanup : Bool) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      (Option (StepResult RefState TerminalOut)) := {
  stack := ⟨Array.mk [{
    mkSingleLocalMiriFrame .dead cleanup with
    body := {
      refDummyMirBody cleanup with
      basicBlocks := Array.mk [{
        statements := Array.empty
        terminator := term
        cleanup := cleanup
      }]
    }
  }]⟩
  machine := none
}

/-- Minimal `Miri.Interpreter.StepState` with `basicBlocks := Array.empty` at
location `.mir ⟨blockIdx, 0⟩` so `Miri.Interpreter.Step.step` executes its
out-of-bounds `.invalidBlock` path. -/
noncomputable def mkRefInvalidBlockStepState (blockIdx : BasicBlockId) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      (Option (StepResult RefState TerminalOut)) := {
  stack := ⟨Array.mk [{
    mkSingleLocalMiriFrame .dead false with
    body := {
      refDummyMirBody false with
      basicBlocks := Array.empty
    }
    location := .mir ⟨blockIdx, 0⟩
  }]⟩
  machine := none
}

/-- Reference basic-block jump calling
`Miri.Interpreter.ControlFlow.goToBlock`
(`vendor/lean-miri/Miri/Interpreter/ControlFlow.lean`). -/
noncomputable def jumpToRefBlock (rframe : RefFrameState)
    (callerMem : CallerMemory) (target : BasicBlockId) :
    StepResult RefState TerminalOut :=
  match Miri.Interpreter.ControlFlow.goToBlock target
      (mkRefStepState false) with
  | (st', .ok ()) =>
    match st'.stack.currentFrame? with
    | some f =>
      match f.location with
      | .mir loc =>
        .step {
          frames := [{
            rframe with
            blockIdx := loc.block
            stmtIdx := loc.statementIndex
          }]
          callerMem
        }
      | .unwinding _ => .fault .unsupported
    | none => .fault .unsupported
  | (_, .error _) => .fault .unsupported

/-- Map `RefStatementKind` to its `Miri.MIR.Statement` constructor for
`Miri.Interpreter.Step.step` and `Miri.Interpreter.Step.evalStatement`. -/
noncomputable def toMiriStatementForDispatch :
    RefStatementKind → Miri.MIR.Statement
  | .nop => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Nop }
  | .storageLive localId =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageLive localId }
  | .storageDead localId =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .StorageDead (if Nat.beq localId 0 then 0 else 1) }
  | .assign _ _ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign ⟨0, Array.empty⟩ (.Use (.Copy ⟨0, Array.empty⟩) .No) }
  | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Intrinsic (.Assume (.Copy ⟨0, Array.empty⟩)) }

/-- Map `RefTerminatorKind` to its `Miri.MIR.Terminator` constructor for
`Miri.Interpreter.Step.step` and
`Miri.Interpreter.ControlFlow.evalTerminator`. -/
noncomputable def toMiriTerminatorForDispatch :
    RefTerminatorKind → Miri.MIR.Terminator
  | .goto target =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Goto target Array.empty }
  | .return_ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  | .unreachable =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Unreachable }
  | .switchInt _ targets =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .SwitchInt (.Copy ⟨0, Array.empty⟩)
        { cases := Array.empty, otherwise := targets.otherwise } }
  | _ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .UnwindTerminate .Abi }

/-- `Miri.Interpreter.TerminatorHooks` for
`Miri.Interpreter.ControlFlow.evalTerminator` and
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`. -/
noncomputable def refTerminatorHooksFor (types : List MirTy)
    (rterm : RefTerminatorKind) (rframe : RefFrameState)
    (callerMem : CallerMemory) :
    Miri.Interpreter.TerminatorHooks (Option Val) Miri.Interpreter.LocalLayout
      Unit (Option (StepResult RefState TerminalOut)) Unit Unit Unit := {
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ st => (st, .ok ())
  popFrame := fun _ st =>
    ( { st with stack := Miri.Interpreter.Stack.empty },
      .ok (mkSingleLocalMiriFrame .dead false) )
  copyReturn := fun _ _ _ st =>
    let res : StepResult RefState TerminalOut :=
      match MirSemantics.getElem? rframe.locals 0 with
      | some ⟨.live (some retVal), some _⟩ =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
        .fault .undefined
      | _ => .fault .unsupported
    ({ st with machine := some res }, .ok ())
  cleanupFrame := fun _ _ _ st => (st, .ok .normal)
  unwindTerminate := fun _ _ st =>
    (st, .error (.unsupported "UnwindTerminate unsupported"))
  evalDiscriminant := fun _ _ st =>
    let res : StepResult RefState TerminalOut :=
      match rterm with
      | .switchInt discr targets =>
        match evalRefPrimitiveOperand types rframe.locals discr with
        | .error k => .fault k
        | .ok (discrVal, rlocalsAfterDiscr) =>
          let targetRes : Except FaultKind BasicBlockId :=
            match discrVal with
            | .scalar sv =>
              evalRefSwitchBranches sv.width sv.bits targets.otherwise
                targets.branches
            | .bool b =>
              evalRefBoolSwitchBranches b targets.otherwise targets.branches
            | _ => .error .unsupported
          match targetRes with
          | .error k => .fault k
          | .ok target =>
            jumpToRefBlock { rframe with locals := rlocalsAfterDiscr }
              callerMem target
      | _ => .fault .unsupported
    ({ st with machine := some res }, .ok ())
  compareSwitchCase := fun _ _ _ st => (st, .ok false)
  call := fun _ _ st => (st, .error (.unsupported "Call unsupported on Day 1"))
  tailCall := fun _ _ st => (st, .error (.unsupported "TailCall unsupported"))
  drop := fun _ _ _ _ st => (st, .error (.unsupported "Drop unsupported"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ _ st =>
    (st, .error (.unsupported "Assert unsupported on Day 1"))
  assertPanic := fun _ _ _ st =>
    (st, .error (.unsupported "Assert unsupported on Day 1"))
}

/-- `Miri.Interpreter.StepHooks` routing `.Assign`, `.StorageLive`,
`.StorageDead`, and terminators through `Miri.Interpreter.Step.step`,
`Miri.Interpreter.Step.evalStatement`,
`Miri.Interpreter.Frame.storageLive`,
`Miri.Interpreter.Frame.storageDead`, and
`Miri.Interpreter.ControlFlow.evalTerminator`. -/
noncomputable def refStepHooksFor (types : List MirTy) (rframe : RefFrameState)
    (callerMem : CallerMemory) (stmt : RefStatementKind)
    (rterm : RefTerminatorKind) :
    Miri.Interpreter.StepHooks (Option Val) Miri.Interpreter.LocalLayout Unit
      (Option (StepResult RefState TerminalOut)) Unit Unit := {
  assign := fun _ _ _ st =>
    let res : StepResult RefState TerminalOut :=
      match stmt with
      | .assign dst rvalue =>
        if !dst.projection.isEmpty then
          .fault .unsupported
        else
          match MirSemantics.getElem? rframe.locals dst.localId with
          | none => .fault .unsupported
          | some ⟨_, none⟩ => .fault .unsupported
          | some ⟨_, some dstTy⟩ =>
            match evalRefRvalue types rframe.locals dstTy rvalue with
            | .error k => .fault k
            | .ok (val, rlocalsAfterRval) =>
              match writeRefPlace rlocalsAfterRval dst.localId dstTy val with
              | .error k => .fault k
              | .ok rlocalsAfterWrite =>
                .step {
                  frames := [{
                    rframe with
                    stmtIdx := rframe.stmtIdx + 1
                    locals := rlocalsAfterWrite
                  }]
                  callerMem
                }
      | _ => .fault .unsupported
    ({ st with machine := some res }, .ok ())
  evalPlace := fun _ _ _ st => (st, .error (.unsupported "SetDiscriminant"))
  writeDiscriminant := fun _ _ _ st =>
    (st, .error (.unsupported "SetDiscriminant"))
  storageLive := fun _ localId st =>
    let res := Miri.Interpreter.Frame.storageLive
      (mkSingleLocalMiriFrame .dead false) () refLocalStorageHooks 0
    match res.outcome with
    | .error e => (st, .error (.stack e))
    | .ok () =>
      let stepRes : StepResult RefState TerminalOut :=
        match MirSemantics.getElem? rframe.locals localId with
        | some ⟨_, some localTy⟩ =>
          match MirSemantics.setElem? rframe.locals localId
              ⟨liveUninitSlot localTy, some localTy⟩ with
          | some rlocals' =>
            .step {
              frames := [{
                rframe with
                stmtIdx := rframe.stmtIdx + 1
                locals := rlocals'
              }]
              callerMem
            }
          | none => .fault .unsupported
        | _ => .fault .unsupported
      ({ st with machine := some stepRes }, .ok ())
  storageDead := fun _ lid st =>
    let res := Miri.Interpreter.Frame.storageDead
      (mkTwoLocalMiriFrame .dead .dead) () refLocalStorageHooks lid
    match res.outcome with
    | .error e => (st, .error (.stack e))
    | .ok () =>
      let stepRes : StepResult RefState TerminalOut :=
        match stmt with
        | .storageDead localId =>
          match MirSemantics.getElem? rframe.locals localId with
          | some ⟨_, some localTy⟩ =>
            match MirSemantics.setElem? rframe.locals localId
                ⟨.dead, some localTy⟩ with
            | some rlocals' =>
              .step {
                frames := [{
                  rframe with
                  stmtIdx := rframe.stmtIdx + 1
                  locals := rlocals'
                }]
                callerMem
              }
            | none => .fault .unsupported
          | _ => .fault .unsupported
        | _ => .fault .unsupported
      ({ st with machine := some stepRes }, .ok ())
  intrinsic := fun _ _ st => (st, .error (.unsupported "Intrinsic"))
  incrementConstEvalCounter := fun _ st => (st, .ok ())
  returnFromCurrentFrame := fun _ _ st => (st, .ok ())
  beforeTerminator := fun _ st => (st, .ok ())
  terminator :=
    Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor types rterm rframe callerMem)
}

/-- Reference statement evaluator delegating outer step and statement dispatch
to `Miri.Interpreter.Step.step` and `Miri.Interpreter.Step.evalStatement` and
local lifecycle checks to `Miri.Interpreter.Frame.storageLive` and
`Miri.Interpreter.Frame.storageDead`
(`vendor/lean-miri/Miri/Interpreter/{Step,Stack}.lean`), matching
`eval_statement` in `compiler/rustc_const_eval/src/interpret/step.rs` and
`storage_live` / `storage_dead` in
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_statement(&mut self, stmt: &mir::Statement<'tcx>) ->
> InterpResult<'tcx> {
>     match &stmt.kind {
>         Assign((place, rvalue)) => self.eval_rvalue_into_place(rvalue,
>             *place)?,
>         StorageLive(local) => { self.storage_live(*local)?; }
>         StorageDead(local) => { self.storage_dead(*local)?; }
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "assert!(local != mir::RETURN_PLACE, \"Cannot make return place dead\");"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefStatement (types : List MirTy) (rframe : RefFrameState)
    (callerMem : CallerMemory) (stmt : RefStatementKind) :
    StepResult RefState TerminalOut :=
  match Miri.Interpreter.Step.step
      (refStepHooksFor types rframe callerMem stmt .return_) ()
      (mkRefStmtStepState (toMiriStatementForDispatch stmt)) with
  | (st', .ok true) =>
    match st'.machine with
    | some res => res
    | none =>
      match st'.stack.currentFrame? with
      | some f =>
        match f.location with
        | .mir loc =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + loc.statementIndex
            }]
            callerMem
          }
        | .unwinding _ => .fault .unsupported
      | none => .fault .unsupported
  | (_, _) => .fault .unsupported

/-- Reference terminator evaluator delegating outer step and terminator
dispatch to `Miri.Interpreter.Step.step`,
`Miri.Interpreter.ControlFlow.evalTerminator`, and
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`
(`vendor/lean-miri/Miri/Interpreter/{Step,ControlFlow}.lean`), matching
`eval_terminator` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "fn eval_terminator(&mut self, terminator: &mir::Terminator<'tcx>) ->
> InterpResult<'tcx> {
>     match terminator.kind {
>         Return => { self.return_from_current_stack_frame(false)? }
>         Goto { target, loop_hint_attrs: _ } => self.go_to_block(target),
>         SwitchInt { ref discr, ref targets } => { ... }
>         Unreachable => throw_ub!(Unreachable),
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefTerminator (types : List MirTy) (rbb : RefBasicBlock)
    (rframe : RefFrameState) (callerMem : CallerMemory) :
    StepResult RefState TerminalOut :=
  match Miri.Interpreter.Step.step
      (refStepHooksFor types rframe callerMem .nop rbb.terminator) ()
      (mkRefTermStepState (toMiriTerminatorForDispatch rbb.terminator)
        rbb.cleanup) with
  | (st', .ok true) =>
    match st'.machine with
    | some res => res
    | none =>
      match st'.stack.currentFrame? with
      | some f =>
        match f.location with
        | .mir loc =>
          .step {
            frames := [{
              rframe with
              blockIdx := loc.block
              stmtIdx := loc.statementIndex
            }]
            callerMem
          }
        | .unwinding _ => .fault .unsupported
      | none => .fault .unsupported
  | (_, .error (.undefinedBehavior _)) => .fault .undefined
  | (_, _) => .fault .unsupported

/-- Single-step evaluator of $M_{\text{ref}}$:
checks `rs.stepsExecuted < rs.maxSteps` first, returning `.exhaustedStepLimit`
when the step budget is reached, and otherwise resolves the active `RefBody`
and `RefBasicBlock` and delegates statement, terminator, and out-of-bounds
block transitions to `Miri.Interpreter.Step.step` (`evalRefStatement`,
`evalRefTerminator`, and `mkRefInvalidBlockStepState`), incrementing
`stepsExecuted := rs.stepsExecuted + 1` on each running step.

The stack must have the shape established by `initRefState`: a suspended
caller sentinel (`returnContinuation = true`) beneath an executing frame
(`returnContinuation = false`). Any other shape is `.blocked`. Each running
step preserves the sentinel and replaces only the top frame. -/
noncomputable def evalRefStep (rp : RefProg) (_c : Choice)
    (rs : RefState) : RefOutcome :=
  if !Nat.blt rs.stepsExecuted rs.maxSteps then
    .exhaustedStepLimit
  else
    match rs.frames with
    | [sentinel, rframe] =>
      if !sentinel.returnContinuation || rframe.returnContinuation then
        .blocked
      else
        match MirSemantics.getElem? rp.bodies rframe.defId with
        | none => .blocked
        | some rbody =>
          match MirSemantics.getElem? rbody.basicBlocks rframe.blockIdx with
          | none =>
            match Miri.Interpreter.Step.step
                (refStepHooksFor rp.types rframe rs.callerMem .nop .return_) ()
                (mkRefInvalidBlockStepState rframe.blockIdx) with
            | (_, .error (.invalidBlock _)) => .blocked
            | _ => .ub
          | some rbb =>
            match MirSemantics.getElem? rbb.statements rframe.stmtIdx with
            | some rstmt =>
              stepResultToRefOutcome sentinel rs.stepsExecuted rs.maxSteps
                (evalRefStatement rp.types rframe rs.callerMem rstmt)
            | none =>
              if Nat.beq rframe.stmtIdx rbb.statements.length then
                stepResultToRefOutcome sentinel rs.stepsExecuted rs.maxSteps
                  (evalRefTerminator rp.types rbb rframe rs.callerMem)
              else
                .ub
    | _ => .blocked

/-- Relational small-step transition of $M_{\text{ref}}$. -/
noncomputable def RefStep (rp : RefProg) (rs : RefState)
    (out : RefOutcome) : Prop :=
  ∃ c : Choice, ValidRefChoice rp rs c ∧ evalRefStep rp c rs = out

/-- Unbounded finite-step reachability in $M_{\text{ref}}$, chaining `rs₃` from
`RefStep rp rs₂ (.running rs₃)` unmodified. -/
inductive RefReaches (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReaches rp rs rs
  | tail {rs₁ rs₂ rs₃ : RefState} :
      RefReaches rp rs₁ rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReaches rp rs₁ rs₃

/-- Outcome `out` is reached from `(rp, q)` under step budget `maxSteps`. -/
noncomputable def RefReachesOutcome (rp : RefProg) (q : Query)
    (maxSteps : Nat) (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReaches rp rs₀ rs ∧ RefStep rp rs out

/-- All-prefix well-formedness in $M_{\text{ref}}$: quantifies universally over
all step budgets `maxSteps : Nat`. -/
noncomputable def RefWellFormed (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefState rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReaches rp rs₀ rs →
        ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcome rp q maxSteps .ub ∧
    ¬ RefReachesOutcome rp q maxSteps .blocked

/-- Observable terminal behavior in $M_{\text{ref}}$: quantifies existentially
over a sufficient step budget `maxSteps : Nat`. -/
noncomputable def RefBehavior (rp : RefProg) (q : Query)
    (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcome rp q maxSteps (.returned out)

/-- Divergence in $M_{\text{ref}}$: initialization succeeds at step budget `0`
with `rs₀`, and there exists an infinite reference execution trace
`trace : Nat → RefState` starting at `trace 0 = rs₀` such that at every step
`n`, executing `trace n` with `stepsExecuted := n` and step budget
`maxSteps := n + 1` transitions via `RefStep` to
`.running { trace (n + 1) with stepsExecuted := n + 1, maxSteps := n + 1 }`. -/
noncomputable def RefDiverges (rp : RefProg) (q : Query) : Prop :=
  ∃ rs₀ : RefState,
    initRefState rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        RefStep rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 })

/-! ## Bijective Simulation Invariant (`SimulationInv`) -/

/-- Pair each runtime `LocalSlot` with its pre-cached `some ty` layout. -/
noncomputable def zipRefLocals :
    List MirTy → List LocalSlot → List RefLocalState
  | ty :: tys, slot :: slots => ⟨slot, some ty⟩ :: zipRefLocals tys slots
  | _, _ => []

/-- Project the runtime `LocalSlot` list from a `RefLocalState` list. -/
noncomputable def unzipRefSlots
    (rlocals : List RefLocalState) : List LocalSlot :=
  rlocals.map (·.slot)

/-- Lift an $M_{\text{anneal}}$ `FrameState` to its unique $M_{\text{ref}}$
`RefFrameState` with `cachedLayout` populated from `bodyLocals`. -/
noncomputable def liftFrame (bodyLocals : List MirTy)
    (f : FrameState) : RefFrameState :=
  { defId := f.defId
    blockIdx := f.blockIdx
    stmtIdx := f.stmtIdx
    locals := zipRefLocals bodyLocals f.locals
    returnContinuation := false }

/-- Lift an $M_{\text{anneal}}$ single-frame `StepResult` to
$M_{\text{ref}}$. -/
noncomputable def mapStepRes (bodyLocals : List MirTy) :
    StepResult State TerminalOut → StepResult RefState TerminalOut
  | .step { frames := [f'], callerMem := cm } =>
    .step { frames := [liftFrame bodyLocals f'], callerMem := cm }
  | .step { frames := _, callerMem := cm } =>
    .step { frames := [], callerMem := cm }
  | .done out => .done out
  | .fault k => .fault k

/-- Frame-level bijective simulation invariant: relates $M_{\text{anneal}}$
frame `f` to $M_{\text{ref}}$ frame `rf` via exact equality
`rf = liftFrame body.locals f`. -/
noncomputable def FrameSimInv (p : Program) (f : FrameState)
    (rf : RefFrameState) : Prop :=
  ∃ body : Body,
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    f.locals.length = body.locals.length ∧
    rf = liftFrame body.locals f

/-- Type of the entry function's return place `_0`, which types the caller
sentinel's destination slot (`callerSentinelFrame`). -/
noncomputable def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

/-- Whole-state bijective simulation invariant between $M_{\text{anneal}}$ and
$M_{\text{ref}}$: constrains every field of `s` and `rs` (up to the explicit
step counters `rs.stepsExecuted` and `rs.maxSteps`), placing the fixed caller
sentinel for the entry function's return type beneath the lifted image of the
single $M_{\text{anneal}}$ frame. -/
noncomputable def SimulationInv (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ f : FrameState, ∃ rf : RefFrameState, ∃ retTy : MirTy,
    s.frames = [f] ∧
    rs.frames = [callerSentinelFrame retTy, rf] ∧
    rs.callerMem = s.callerMem ∧
    entryRetTy? p = some retTy ∧
    FrameSimInv p f rf

/-! ## Trusted Top-Level Correspondence and Canary Claims -/

/-- Trusted statement of the correspondence theorem between
$M_{\text{anneal}}$ (`Trusted.MirSemantics`) and $M_{\text{ref}}$
(`Trusted.Correspondence`). For every well-formed `(p, q)`:
1. `encodeProg p` is well-formed in $M_{\text{ref}}$ under every step budget
   (UB transfer);
2. both machines exhibit exactly the same terminal behaviors; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ if and only if `encodeProg p`
   diverges in $M_{\text{ref}}$.

The behavior and divergence equivalences rule out reference executions that
$M_{\text{anneal}}$ omits, so a postcondition proved over `Behavior` cannot
miss an outcome that the reference model permits. -/
noncomputable def CorrespondenceClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
    RefWellFormed (encodeProg p) q ∧
    (∀ (out : TerminalOut),
      Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
    (Diverges p q ↔ RefDiverges (encodeProg p) q)

/-- Trusted statement of bidirectional fault equivalence for all
`k : FaultKind` (`.undefined` ↔ `.ub` and `.unsupported` ↔ `.blocked`). -/
noncomputable def FaultEquivalenceClaim : Prop :=
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
    ∃ maxSteps,
      RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)

/-- Trusted statement verifying the direct consumer-side wiring of
`Miri.Interpreter.ExecutionMachine.step` (`Miri.Interpreter.Step.step` over
`Miri.Interpreter.ExecutionMachine.stepHooks`) and `deinitMovedPlace` in
`vendor/lean-miri` (`Miri.Interpreter.ExecutionMachine.withValidation`,
`Miri.Interpreter.ExecutionMachine.operandHooks`, and
`Miri.Interpreter.evalOperand`). -/
noncomputable def MiriMoveDeinitWiringClaim : Prop :=
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits)
      (c : C)
      (state : Miri.Interpreter.MachineHooks.State K U),
    Miri.Interpreter.ExecutionMachine.step cfg limits c state =
      let (state', out) := Miri.Interpreter.Step.step
        (Miri.Interpreter.ExecutionMachine.stepHooks cfg limits) c
        { state with
          machine := {
            state.machine with
            pendingMoveDeinit := false
            pendingMoveDeinits := Array.empty
          } }
      ( { state' with
          machine := {
            state'.machine with
            pendingMoveDeinit := false
            pendingMoveDeinits := Array.empty
          } },
        out )) ∧
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits),
    cfg.deinitMovedPlace = true →
    (Miri.Interpreter.ExecutionMachine.withValidation
        cfg limits).access.deinitMovedPlace = true ∧
    (Miri.Interpreter.ExecutionMachine.operandHooks
        cfg).deinitMovedPlace = true) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame : Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = false →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame frame₁ frame₂ :
        Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state state₁ : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout)
      (imm : Miri.Interpreter.Immediate Prov)
      (layout : Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = true →
    Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known =
      ⟨frame₁, state₁, .ok ⟨.immediate imm, layout⟩⟩ →
    frame₁.replaceLocalValue localId
        (.live (if layout.layout.isZst then .immediate imm
          else .immediate .uninit)) =
      .ok frame₂ →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      ⟨frame₂, state₁, .ok ⟨.immediate imm, layout⟩⟩) ∧
  (∀ {K U : Type}
      (m : Miri.Interpreter.MachineHooks.MachineState K U)
      (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
      (isMove : Bool),
    (Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit
      (Miri.Interpreter.MachineHooks.recordPendingMoveDeinit m mplace
        isMove)).2 = isMove) ∧
  (∀ {P S C E Other Extern FnABI ArgABI : Type}
      (h : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI)
      (choice : C)
      (place : Miri.Interpreter.MPlaceTy P)
      (snap : Miri.Interpreter.OpTy P),
    Miri.Interpreter.FnArg.copyFnArg (.InPlace place (some snap)) = snap ∧
    Miri.Interpreter.Call.deinitInPlaceArg h choice place (some snap) =
      Bind.bind (h.restoreInPlaceMovedBytes choice snap place)
        (fun _ => h.deinitInPlaceArgument choice place))

/-- Trusted claim for `Anneal.MirCorrespondenceProof.decodeProg_encodeProg`. -/
noncomputable def DecodeProgEncodeProgClaim : Prop :=
  ∀ (p : Program), decodeProg (encodeProg p) = some p

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeProg_types_canonical`. -/
noncomputable def EncodeProgTypesCanonicalClaim : Prop :=
  ∀ (p : Program), typesAreCanonical (encodeProg p).types = true

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeStmt_no_dormant_noops`. -/
noncomputable def EncodeStmtNoDormantNoopsClaim : Prop :=
  ∀ (ts : List MirTy) (s : StatementKind),
    encodeStmt ts s = .nop ↔ s = .nop

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeRvalue_binaryOp_iff`. -/
noncomputable def EncodeRvalueBinaryOpIffClaim : Prop :=
  ∀ (ts : List MirTy) (rv : Rvalue) (op : BinOp) (l' r' : RefOperand),
    encodeRvalue ts rv = .binaryOp op l' r' ↔
      ∃ l r : Operand, rv = .binaryOp op l r ∧
        encodeOperand ts l = l' ∧ encodeOperand ts r = r'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeRvalue_unaryOp_iff`. -/
noncomputable def EncodeRvalueUnaryOpIffClaim : Prop :=
  ∀ (ts : List MirTy) (rv : Rvalue) (op : UnOp) (o' : RefOperand),
    encodeRvalue ts rv = .unaryOp op o' ↔
      ∃ o : Operand, rv = .unaryOp op o ∧ encodeOperand ts o = o'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeStmt_assign_iff`. -/
noncomputable def EncodeStmtAssignIffClaim : Prop :=
  ∀ (ts : List MirTy) (s : StatementKind) (dst' : RefPlace) (rv' : RefRvalue),
    encodeStmt ts s = .assign dst' rv' ↔
      ∃ (dst : Place) (rv : Rvalue), s = .assign dst rv ∧
        encodePlace ts dst = dst' ∧ encodeRvalue ts rv = rv'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.state_unique_of_simulationInv`. -/
noncomputable def StateUniqueOfSimulationInvClaim : Prop :=
  ∀ {p : Program} {s₁ s₂ : State} {rs : RefState},
    SimulationInv p s₁ rs → SimulationInv p s₂ rs → s₁ = s₂

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refState_unique_of_simulationInv`. -/
noncomputable def RefStateUniqueOfSimulationInvClaim : Prop :=
  ∀ {p : Program} {s : State} {rs₁ rs₂ : RefState},
    SimulationInv p s rs₁ → SimulationInv p s rs₂ →
    rs₁.stepsExecuted = rs₂.stepsExecuted →
    rs₁.maxSteps = rs₂.maxSteps →
    rs₁ = rs₂

/-- Trusted claim for `Anneal.MirCorrespondenceProof.initRefState_sim`. -/
noncomputable def InitRefStateSimClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {q : Query} (maxSteps : Nat),
    decodeProg rp = some p →
    (∀ k, initState p q = .error k → initRefState rp q maxSteps = .error k) ∧
    (∀ s₀, initState p q = .ok s₀ →
      ∃ rs₀, initRefState rp q maxSteps = .ok rs₀ ∧
        SimulationInv p s₀ rs₀ ∧
        rs₀.stepsExecuted = 0 ∧
        rs₀.maxSteps = maxSteps)

/-- Trusted claim for `Anneal.MirCorrespondenceProof.evalRefStep_eq`. -/
noncomputable def EvalRefStepEqClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs : RefState}
    {f : FrameState} {rf : RefFrameState} {retTy : MirTy} {body : Body},
    decodeProg rp = some p →
    s.frames = [f] →
    rs.frames = [callerSentinelFrame retTy, rf] →
    rs.callerMem = s.callerMem →
    MirSemantics.getElem? p.bodies f.defId = some body →
    f.locals.length = body.locals.length →
    rf = liftFrame body.locals f →
    Nat.blt rs.stepsExecuted rs.maxSteps = true →
    ∀ (c : Choice),
      evalRefStep rp c rs =
        stepResultToRefOutcome (callerSentinelFrame retTy) rs.stepsExecuted
          rs.maxSteps (mapStepRes body.locals (evalStep p c s))

/-- Trusted claim for `Anneal.MirCorrespondenceProof.sim_of_refStep`. -/
noncomputable def SimOfRefStepClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs rs' : RefState},
    decodeProg rp = some p →
    SimulationInv p s rs →
    RefStep rp rs (.running rs') →
    ∃ s' : State, Step p s (.step s') ∧ SimulationInv p s' rs'

/-- Trusted claim for `Anneal.MirCorrespondenceProof.sim_of_refReaches`. -/
noncomputable def SimOfRefReachesClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s₀ : State} {rs₀ rs : RefState},
    decodeProg rp = some p →
    SimulationInv p s₀ rs₀ →
    RefReaches rp rs₀ rs →
    ∃ s : State, Reaches p s₀ s ∧ SimulationInv p s rs

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refWellFormed_of_wellFormed`. -/
noncomputable def RefWellFormedOfWellFormedClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q → RefWellFormed (encodeProg p) q

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refBehavior_of_behavior`. -/
noncomputable def RefBehaviorOfBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    Behavior p q out → RefBehavior (encodeProg p) q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.behavior_of_refBehavior`. -/
noncomputable def BehaviorOfRefBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    RefBehavior (encodeProg p) q out → Behavior p q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.behavior_iff_refBehavior`. -/
noncomputable def BehaviorIffRefBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    Behavior p q out ↔ RefBehavior (encodeProg p) q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.diverges_iff_refDiverges`. -/
noncomputable def DivergesIffRefDivergesClaim : Prop :=
  ∀ (p : Program) (q : Query),
    Diverges p q ↔ RefDiverges (encodeProg p) q

/-! ### Correspondence Canary Programs and Claims (`D6`–`D10`) -/

/-- `D6` (Use-After-Move UB):
`_2 = move _1; _0 = copy _1; return` deinitializes `_1` on `move _1` and
faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$) on the subsequent
`copy _1`. -/
noncomputable def progUseAfterMoveD6 : Program where
  entryDefId := 0
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(42u32)` for canaries `D6`–`D8`. -/
noncomputable def queryU32_42 : Query where
  args := [u32Val 42]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D6_use_after_move_ub`. -/
noncomputable def CanaryD6UseAfterMoveUbClaim : Prop :=
  ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .unsupported) ∧
  ¬ WellFormed progUseAfterMoveD6 queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progUseAfterMoveD6)
    queryU32_42 maxSteps .ub)

/-- `D7a` (`BinaryOp` left-to-right `copy _1` then `move _1` succeeds):
`_0 = BinOp(Add, copy _1, move _1); return` reads `_1` in `lhs`, then reads
and deinitializes `_1` in `rhs`, and returns `84`. -/
noncomputable def progBinOpCopyThenMoveD7a : Program where
  entryDefId := 0
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7a_binop_copy_then_move_ok`. -/
noncomputable def CanaryD7aBinopCopyThenMoveOkClaim : Prop :=
  WellFormed progBinOpCopyThenMoveD7a queryU32_42 ∧
  Behavior progBinOpCopyThenMoveD7a queryU32_42
    (.returned ⟨u32Val 84, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progBinOpCopyThenMoveD7a) queryU32_42 ∧
  RefBehavior (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
    (.returned ⟨u32Val 84, ⟨[]⟩⟩)

/-- `D7b` (`BinaryOp` left-to-right `move _1` then `copy _1` faults with UB):
`_0 = BinOp(Add, move _1, copy _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = copy _1`. -/
noncomputable def progBinOpMoveThenCopyD7b : Program where
  entryDefId := 0
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7b_binop_move_then_copy_ub`. -/
noncomputable def CanaryD7bBinopMoveThenCopyUbClaim : Prop :=
  ReachesResult progBinOpMoveThenCopyD7b queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progBinOpMoveThenCopyD7b queryU32_42
    (.fault .unsupported) ∧
  ¬ WellFormed progBinOpMoveThenCopyD7b queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBinOpMoveThenCopyD7b)
    queryU32_42 maxSteps .ub)

/-- `D7c` (`BinaryOp` left-to-right `move _1` then `move _1` faults with UB):
`_0 = BinOp(Add, move _1, move _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = move _1`. -/
noncomputable def progBinOpMoveThenMoveD7c : Program where
  entryDefId := 0
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7c_binop_move_then_move_ub`. -/
noncomputable def CanaryD7cBinopMoveThenMoveUbClaim : Prop :=
  ReachesResult progBinOpMoveThenMoveD7c queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progBinOpMoveThenMoveD7c queryU32_42
    (.fault .unsupported) ∧
  ¬ WellFormed progBinOpMoveThenMoveD7c queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBinOpMoveThenMoveD7c)
    queryU32_42 maxSteps .ub)

/-- `D8` (Self-move `_1 = move _1` preserves initialized value):
`_1 = move _1; _0 = copy _1; return` reads `42` from `_1`, deinitializes `_1`
to `.live none`, and then writes `42` back into `_1`, so the subsequent
`_0 = copy _1` succeeds and returns `42`. -/
noncomputable def progSelfMoveD8 : Program where
  entryDefId := 0
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D8_self_move_ok`. -/
noncomputable def CanaryD8SelfMoveOkClaim : Prop :=
  WellFormed progSelfMoveD8 queryU32_42 ∧
  Behavior progSelfMoveD8 queryU32_42 (.returned ⟨u32Val 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progSelfMoveD8) queryU32_42 ∧
  RefBehavior (encodeProg progSelfMoveD8) queryU32_42
    (.returned ⟨u32Val 42, ⟨[]⟩⟩)

/-- `D9` (Move of 0-Byte ZST `MirTy.unit` Remains Initialized):
`_2 = move _1; _0 = copy _1; return` where `_1 : ()` sets `_1` to
`liveUninitSlot .unit = .live (some .unit)`, so subsequent `_0 = copy _1`
succeeds and returns `.unit`. -/
noncomputable def progMoveUnitZstD9 : Program where
  entryDefId := 0
  bodies := [{
    argumentCount := 0
    locals := [.unit, .unit, .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D9_move_unit_zst_ok`. -/
noncomputable def CanaryD9MoveUnitZstOkClaim : Prop :=
  WellFormed progMoveUnitZstD9 queryEmpty ∧
  Behavior progMoveUnitZstD9 queryEmpty (.returned ⟨.unit, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progMoveUnitZstD9) queryEmpty ∧
  RefBehavior (encodeProg progMoveUnitZstD9) queryEmpty
    (.returned ⟨.unit, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D10_add_unchecked_overflow_ub`. -/
noncomputable def CanaryD10AddUncheckedOverflowUbClaim : Prop :=
  ReachesResult progAddUncheckedU32 queryU32MaxPlusOne
    (.fault .undefined) ∧
  ¬ WellFormed progAddUncheckedU32 queryU32MaxPlusOne ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progAddUncheckedU32)
    queryU32MaxPlusOne maxSteps .ub) ∧
  Behavior progAddU32 queryU32MaxPlusOne (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg progAddU32) queryU32MaxPlusOne
    (.returned ⟨u32Val 0, ⟨[]⟩⟩)

end Trusted.Correspondence
