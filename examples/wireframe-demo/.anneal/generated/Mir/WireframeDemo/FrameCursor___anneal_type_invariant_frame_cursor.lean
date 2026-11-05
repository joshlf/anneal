import Trusted

namespace Mir.WireframeDemo.FrameCursor___anneal_type_invariant_frame_cursor

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::FrameCursor::__anneal_type_invariant_frame_cursor`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=2, align=2
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil))) }

-- bb0: _2 = copy ((*_1).0: u16); _3 = copy ((*_1).1: u16); _0 = Le(move _2, move _3); return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::FrameCursor::__anneal_type_invariant_frame_cursor",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.model,
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.adt "wireframe_demo::FrameCursor" List.nil)), layoutIdx := 1 }, debugName := (Option.some "self") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 2 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u16), layoutIdx := 2 }) List.nil)) }))), span := "src/lib.rs:83:26: 83:37" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := (List.cons ProjectionElem.deref (List.cons (ProjectionElem.field 1 { kind := (RigidTy.uint UintTy.u16), layoutIdx := 2 }) List.nil)) }))), span := "src/lib.rs:83:41: 83:51" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.le (Operand.move { local_ := 2, projection := List.nil }) (Operand.move { local_ := 3, projection := List.nil }))), span := "src/lib.rs:83:26: 83:51" } List.nil))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:83:53: 83:53" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.FrameCursor___anneal_type_invariant_frame_cursor
