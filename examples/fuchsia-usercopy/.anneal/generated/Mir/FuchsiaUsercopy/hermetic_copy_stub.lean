import Trusted

namespace Mir.FuchsiaUsercopy.hermetic_copy_stub

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `fuchsia_usercopy::hermetic_copy_stub`. -/

-- TypeLayout[0]: size=8, align=8
-- TypeLayout[1]: size=1, align=1
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=0, align=1
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: switchInt(copy _3) -> [0: bb1, otherwise: bb2]
-- bb1: _4 = core::hint::unreachable_unchecked() -> unwind continue
-- bb2: _0 = copy _2; return
def body : CapturedMir :=
  {
    defPath := "fuchsia_usercopy::hermetic_copy_stub",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 3,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 0 }, debugName := (Option.some "count") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 0 }, debugName := (Option.some "fault_offset") } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.bool, layoutIdx := 1 }, debugName := (Option.some "normal_mode_dest_valid") } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.never, layoutIdx := 2 }, debugName := Option.none } List.nil))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "<dummy>" } List.nil), terminator := { kind := (TerminatorKind.switchInt (Operand.copy { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 1) List.nil), otherwise := 2 }), span := "src/lib.rs:107:9: 107:31" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::hint::unreachable_unchecked" List.nil), layoutIdx := 3 }, val := ConstValue.zeroSized }) List.nil { local_ := 4, projection := List.nil } Option.none UnwindAction.continue_), span := "src/lib.rs:108:18: 108:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:110:5: 110:17" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:111:2: 111:2" }, isCleanup := false } List.nil))),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } (List.cons { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil))), ret := { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.FuchsiaUsercopy.hermetic_copy_stub
