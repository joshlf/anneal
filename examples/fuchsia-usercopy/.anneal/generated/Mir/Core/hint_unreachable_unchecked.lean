import Trusted

namespace Mir.Core.hint_unreachable_unchecked

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

/-! Captured `Runtime(PostCleanup)` MIR and compiler layout table for `core::hint::unreachable_unchecked`. -/

-- TypeLayout[0]: size=0, align=1
-- TypeLayout[1]: size=0, align=1
-- TypeLayout[2]: size=1, align=1
-- TypeLayout[3]: size=8, align=8
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))) }

-- bb0: assume(UbChecks); _1 = core::hint::unreachable_unchecked::precondition_check() -> [return: bb1, unwind unreachable]
-- bb1: unreachable
def body : CapturedMir :=
  {
    defPath := "core::hint::unreachable_unchecked",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.never, layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 1 }, debugName := Option.none } List.nil)),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 1), span := "<dummy>" } (List.cons { kind := (StatementKind.intrinsic (NonDivergingIntrinsic.assume (Operand.constant { ty := { kind := RigidTy.bool, layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }))), span := "/usr/local/google/home/markdittmer/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ub_checks.rs:77:35: 77:42" } List.nil)), terminator := { kind := (TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.fnDef "core::hint::unreachable_unchecked::precondition_check" List.nil), layoutIdx := 1 }, val := ConstValue.zeroSized }) List.nil { local_ := 1, projection := List.nil } (Option.some 1) UnwindAction.unreachable), span := "/usr/local/google/home/markdittmer/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ub_checks.rs:78:17: 78:46" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unreachable, span := "/usr/local/google/home/markdittmer/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ub_checks.rs:77:13: 79:14" }, isCleanup := false } List.nil)),
    fnAbi := { args := (List.cons { layout := { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct } List.nil), ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := true }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.Core.hint_unreachable_unchecked
