import Trusted
import Mir.WireframeDemo.checksum_frame_safe
import Obligations.WireframeDemo.checksum_frame_safe

namespace Specs.WireframeDemo.checksum_frame_safe

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-!
Stateful reference contract for `wireframe_demo::checksum_frame_safe` (Journey 4).

Universally quantifies over all `256^8 = 2^64` 8-byte `&[u8; 8]` frames backed
by a shared (`.frozen`) Tree Borrows reference, specifying that
`checksum_frame_safe` computes the sum of the four big-endian 16-bit words
without mutating `Memory`.
-/

/-- Canonical `V2026_06_01` aggregate value encoding `[b0, .., b7] : [u8; 8]`. -/
def frame8Value (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Value :=
  .aggregate 0
    [ .scalar { bits := b0, sizeBytes := 1 }
    , .scalar { bits := b1, sizeBytes := 1 }
    , .scalar { bits := b2, sizeBytes := 1 }
    , .scalar { bits := b3, sizeBytes := 1 }
    , .scalar { bits := b4, sizeBytes := 1 }
    , .scalar { bits := b5, sizeBytes := 1 }
    , .scalar { bits := b6, sizeBytes := 1 }
    , .scalar { bits := b7, sizeBytes := 1 } ]

/-- Caller-frame slot index (`69`, strictly above the local-declaration counts
of both `checksum_frame_safe` (`28`) and `checksum_frame_fast` (`69`)) holding
the pointee `[u8; 8]` array so both functions share an identical caller frame. -/
abbrev frame8SlotIdx : Nat := 69

/-- Caller local table placing `[b0, .., b7]` at `frame8SlotIdx`. -/
def frame8CallerLocals (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : List LocalSlot :=
  List.replicate frame8SlotIdx LocalSlot.dead ++
    [.init (frame8Value b0 b1 b2 b3 b4 b5 b6 b7)]

/-- Shared (`.frozen`) Tree Borrows entry granting `&[u8; 8]` read access. -/
def sharedFrame8Borrow (ptrVal : ProvenancePtr) : BorrowEntry :=
  { tag := ptrVal.tag
    targetLocal := frame8SlotIdx
    targetProjection := .nil
    perm := .frozen }

/-- Pure specification of the sum of four big-endian 16-bit frame words. -/
def bigEndianWordSum4 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  (b0 * 256 + b1) + (b2 * 256 + b3) + (b4 * 256 + b5) + (b6 * 256 + b7)

/-- Canonical root-entry `&[u8; 8]` pointer provenance (`allocId = 1`). -/
def rootFrame8Ptr : ProvenancePtr :=
  { allocId := 1, offsetBytes := 0 }

/-- Universal precondition covering all `2^64` valid `&[u8; 8]` frame references. -/
def frame8Pre (args : List Value) (mem : Memory) : Prop :=
  ∃ (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
    b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
    b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧ b7 < 256 ∧
    args = [.ptr rootFrame8Ptr 8] ∧
    mem.activeCallee = .none ∧
    mem.callStack = .nil ∧
    mem.borrows = [sharedFrame8Borrow rootFrame8Ptr] ∧
    mem.callerLocals = frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7

/-- Postcondition asserting the exact 32-bit big-endian word sum and read-only
memory preservation (`mem' = mem`). -/
def frame8Post
    (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
      args = [.ptr rootFrame8Ptr 8] →
      mem.callerLocals = frame8CallerLocals b0 b1 b2 b3 b4 b5 b6 b7 →
      ret =
        .scalar
          { bits := bigEndianWordSum4 b0 b1 b2 b3 b4 b5 b6 b7
            sizeBytes := 4 }

/-- Normal-priority `StatefulItemSpec` instance for `wireframe_demo::checksum_frame_safe`. -/
instance : StatefulItemSpec "wireframe_demo::checksum_frame_safe" :=
  Obligations.WireframeDemo.checksum_frame_safe.refineStatefulSpec
    frame8Pre
    frame8Post

end Specs.WireframeDemo.checksum_frame_safe
