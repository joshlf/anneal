import Trusted

namespace Mir.WireframeDemo.__ANNEAL_MODEL_is_valid_payload_len

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `wireframe_demo::__ANNEAL_MODEL_is_valid_payload_len`. -/

-- TypeLayout[0]: size=16, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = const "is_valid_payload_len"; return
def body : CapturedMir :=
  {
    defPath := "wireframe_demo::__ANNEAL_MODEL_is_valid_payload_len",
    phase := MirPhaseTag.runtimePostCleanup,
    role := ContractRole.model,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 0 }, debugName := Option.none } List.nil),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.ref Mutability.not RigidTy.str), layoutIdx := 0 }, val := (ConstValue.slice (ConstScalar.ptr { allocId := 1, offsetBytes := 0 } 8) 20) }))), span := "src/lib.rs:76:1: 76:22" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:76:1: 76:22" }, isCleanup := false } List.nil),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 8 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.pair }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := (List.cons { allocId := 1, bytes := (List.cons (Option.some (UInt8.ofNat 105)) (List.cons (Option.some (UInt8.ofNat 115)) (List.cons (Option.some (UInt8.ofNat 95)) (List.cons (Option.some (UInt8.ofNat 118)) (List.cons (Option.some (UInt8.ofNat 97)) (List.cons (Option.some (UInt8.ofNat 108)) (List.cons (Option.some (UInt8.ofNat 105)) (List.cons (Option.some (UInt8.ofNat 100)) (List.cons (Option.some (UInt8.ofNat 95)) (List.cons (Option.some (UInt8.ofNat 112)) (List.cons (Option.some (UInt8.ofNat 97)) (List.cons (Option.some (UInt8.ofNat 121)) (List.cons (Option.some (UInt8.ofNat 108)) (List.cons (Option.some (UInt8.ofNat 111)) (List.cons (Option.some (UInt8.ofNat 97)) (List.cons (Option.some (UInt8.ofNat 100)) (List.cons (Option.some (UInt8.ofNat 95)) (List.cons (Option.some (UInt8.ofNat 108)) (List.cons (Option.some (UInt8.ofNat 101)) (List.cons (Option.some (UInt8.ofNat 110)) List.nil)))))))))))))))))))), relocations := List.nil, align := { bytes := 1 }, mutability := Mutability.not } List.nil)
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.WireframeDemo.__ANNEAL_MODEL_is_valid_payload_len
