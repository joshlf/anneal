import Trusted

namespace Mir.WireframeDemo.frame_total_len

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::frame_total_len`. -/

-- TypeLayout[0]: size=2, align=2
-- TypeLayout[1]: size=1, align=1
-- TypeLayout[2]: size=4, align=2
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 2 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 1 List.nil)) } List.nil))) }

-- bb0: _3 = AddWithOverflow(copy _1, copy _2); assert(!move (_3.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _1, copy _2) -> [success: bb1, unwind continue]
-- bb1: _0 = move (_3.0: u16); return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::frame_total_len",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }, debugName := (Option.some "header_len") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }, debugName := (Option.some "payload_len") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u16) (List.cons RigidTy.bool List.nil))), layoutIdx := 2 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 1, projection := List.nil }) (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:99:5: 99:29" } List.nil)), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 3, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 1 }) List.nil) }) false 1 UnwindAction.continue_), span := "src/lib.rs:99:5: 99:29" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.move { local_ := 3, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:99:5: 99:29" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:100:2: 100:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.frame_total_len
