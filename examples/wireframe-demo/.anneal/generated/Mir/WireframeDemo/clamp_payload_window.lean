import Trusted

namespace Mir.WireframeDemo.clamp_payload_window

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::clamp_payload_window`. -/

-- TypeLayout[0]: size=2, align=2
-- TypeLayout[1]: size=1, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)) }

-- bb0: _3 = Le(copy _1, copy _2); switchInt(move _3) -> [0: bb2, otherwise: bb1]
-- bb1: _0 = copy _1; goto -> bb3
-- bb2: _0 = copy _2; goto -> bb3
-- bb3: return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::clamp_payload_window",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 2,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }, debugName := (Option.some "requested") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u16), layoutIdx := 0 }, debugName := (Option.some "max_window") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 1 }, debugName := Option.none } List.nil)))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.binaryOp BinOp.le (Operand.copy { local_ := 1, projection := List.nil }) (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:160:8: 160:31" } List.nil)), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 2) List.nil), otherwise := 1 }), span := "src/lib.rs:160:8: 160:31" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:161:9: 161:18" } List.nil), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:160:5: 164:6" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:163:9: 163:19" } List.nil), terminator := { kind := (TerminatorKind.goto 3), span := "src/lib.rs:160:5: 164:6" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:165:2: 165:2" }, isCleanup := false } List.nil)))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil)), ret := { layout := { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 16 false) { start := 0, end_ := 65535 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.clamp_payload_window
