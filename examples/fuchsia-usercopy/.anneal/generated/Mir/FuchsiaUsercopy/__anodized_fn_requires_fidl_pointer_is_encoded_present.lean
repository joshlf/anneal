import Trusted

namespace Mir.FuchsiaUsercopy.__anodized_fn_requires_fidl_pointer_is_encoded_present

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `fuchsia_usercopy::__anodized_fn_requires_fidl_pointer_is_encoded_present`. -/

-- TypeLayout[0]: size=1, align=1
-- TypeLayout[1]: size=8, align=8
-- TypeLayout[2]: size=0, align=1
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: _2 = const true; _4 = const (); _6 = &_4; _0 = const true; _3 = move _5; _0 = BitAnd(move _2, move _3); return
def body : CapturedMir :=
  {
    defPath := "fuchsia_usercopy::__anodized_fn_requires_fidl_pointer_is_encoded_present",
    phase := MirPhaseTag.runtimeOptimized,
    role := (ContractRole.requires "fuchsia_usercopy::fidl_pointer_is_encoded_present"),
    argCount := 1,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := (Option.some "__anodized_pre") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u64), layoutIdx := 1 }, debugName := (Option.some "encoded_u64") } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.closure "fuchsia_usercopy::__anodized_fn_requires_fidl_pointer_is_encoded_present::{closure#0}" (List.cons (RigidTy.int IntTy.i8) (List.cons (RigidTy.fnPtr (List.cons (RigidTy.tuple List.nil) List.nil) RigidTy.bool Safety.safe (CallConv.other "rust-call")) (List.cons (RigidTy.tuple List.nil) List.nil)))), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not (RigidTy.closure "fuchsia_usercopy::__anodized_fn_requires_fidl_pointer_is_encoded_present::{closure#0}" (List.cons (RigidTy.int IntTy.i8) (List.cons (RigidTy.fnPtr (List.cons (RigidTy.tuple List.nil) List.nil) RigidTy.bool Safety.safe (CallConv.other "rust-call")) (List.cons (RigidTy.tuple List.nil) List.nil))))), layoutIdx := 3 }, debugName := Option.none } List.nil))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 2), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 4), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 5), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 6), span := "<dummy>" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }))), span := "src/lib.rs:204:1: 207:3" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.closure "fuchsia_usercopy::__anodized_fn_requires_fidl_pointer_is_encoded_present::{closure#0}" (List.cons (RigidTy.int IntTy.i8) (List.cons (RigidTy.fnPtr (List.cons (RigidTy.tuple List.nil) List.nil) RigidTy.bool Safety.safe (CallConv.other "rust-call")) (List.cons (RigidTy.tuple List.nil) List.nil)))), layoutIdx := 2 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:205:15: 205:19" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.ref BorrowKind.shared { local_ := 4, projection := List.nil })), span := "src/lib.rs:205:15: 205:19" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }))), span := "src/lib.rs:205:15: 205:19" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.move { local_ := 5, projection := List.nil }))), span := "src/lib.rs:205:19: 205:19" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitAnd (Operand.move { local_ := 2, projection := List.nil }) (Operand.move { local_ := 3, projection := List.nil }))), span := "src/lib.rs:204:1: 207:3" } List.nil))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:207:3: 207:3" }, isCleanup := false } List.nil),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.FuchsiaUsercopy.__anodized_fn_requires_fidl_pointer_is_encoded_present
