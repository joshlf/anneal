import Trusted
import Mir.WireframeDemo.advance_cursor
import Obligations.WireframeDemo.advance_cursor

namespace Specs.WireframeDemo.advance_cursor

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-!
Stateful `&mut FrameCursor` contract for `wireframe_demo::advance_cursor`
(Journey 1).

Universally quantifies over all valid `FrameCursor` states (`offset <= limit < 65536`),
all 16-bit `step < 65536` increments, and active Tree Borrows `&mut FrameCursor`
references, requiring `advance_cursor` to preserve the `FrameCursor` invariant
`newOffset <= limit`, update `cursor.offset` in place when
`step <= limit - offset`, and return whether the cursor advanced.
-/

/-- Canonical `V2026_06_01` aggregate value for `FrameCursor { offset, limit }`. -/
def cursorValue (offset limit : Nat) : Value :=
  .aggregate 0
    [ .scalar { bits := offset, sizeBytes := 2 }
    , .scalar { bits := limit, sizeBytes := 2 } ]

/-- Caller-frame slot index (`>= Mir.WireframeDemo.advance_cursor.body.localDecls.length`)
holding the pointee `FrameCursor`. -/
abbrev cursorSlotIdx : Nat := 10

/-- Caller local table placing `FrameCursor { offset, limit }` at `cursorSlotIdx`. -/
def cursorCallerLocals (offset limit : Nat) : List LocalSlot :=
  List.replicate cursorSlotIdx LocalSlot.dead ++ [.init (cursorValue offset limit)]

/-- Active Tree Borrows entry granting `&mut FrameCursor` access to `ptrVal.tag`. -/
def activeCursorBorrow (ptrVal : ProvenancePtr) : BorrowEntry :=
  { tag := ptrVal.tag
    targetLocal := cursorSlotIdx
    targetProjection := .nil
    perm := .active }

/-- Canonical root-entry `&mut FrameCursor` pointer provenance (`allocId = 1`). -/
def rootCursorPtr : ProvenancePtr :=
  { allocId := 1, offsetBytes := 0 }

/-- Stateful precondition covering all valid `&mut FrameCursor` calls. -/
def cursorStatefulPre (args : List Value) (mem : Memory) : Prop :=
  ∃ (offset limit step : Nat),
    offset ≤ limit ∧
    limit < 65536 ∧
    step < 65536 ∧
    args = [.ptr rootCursorPtr 8, .scalar { bits := step, sizeBytes := 2 }] ∧
    mem.activeCallee = .none ∧
    mem.callStack = .nil ∧
    mem.activeProtectors = .nil ∧
    mem.borrows = [activeCursorBorrow rootCursorPtr] ∧
    mem.callerLocals = cursorCallerLocals offset limit

/-- Stateful postcondition asserting return-flag accuracy, in-place mutation of
`FrameCursor`, and preservation of the `newOffset <= limit` type invariant. -/
def cursorStatefulPost
    (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  ∀ (offset limit step : Nat),
    offset ≤ limit →
    limit < 65536 →
    step < 65536 →
    args = [.ptr rootCursorPtr 8, .scalar { bits := step, sizeBytes := 2 }] →
    mem.callerLocals = cursorCallerLocals offset limit →
    let newOffset := if step ≤ limit - offset then offset + step else offset
    newOffset ≤ limit ∧
      ret = .scalar { bits := if step ≤ limit - offset then 1 else 0, sizeBytes := 1 } ∧
      get? mem'.callerLocals cursorSlotIdx = .some (.init (cursorValue newOffset limit))

/-- Normal-priority `StatefulItemSpec` instance for `wireframe_demo::advance_cursor`. -/
instance : StatefulItemSpec "wireframe_demo::advance_cursor" :=
  Obligations.WireframeDemo.advance_cursor.refineStatefulSpec
    cursorStatefulPre
    cursorStatefulPost

end Specs.WireframeDemo.advance_cursor
