import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Terminators
import Trusted.Rustc.V2026_06_01.MirAst.Body

namespace Trusted.MirAst

/-!
Default dialect alias re-exporting `Trusted.Rustc.V2026_06_01.MirAst`.
-/

export Trusted.Rustc.V2026_06_01.MirAst (
  Local BasicBlockIdx FieldIdx VariantIdx AllocId LayoutIdx DefPath
  UintTy IntTy FloatTy Mutability Safety RigidTy Ty
  ProjectionElem Place ScalarInt ProvenancePtr ConstScalar ConstValue
  ConstOperand Operand BinOp UnOp NullOp BorrowKind CastKind
  AggregateKind Rvalue NonDivergingIntrinsic RetagKind StatementKind
  Statement SwitchTargets UnwindAction TerminatorKind Terminator
  BasicBlockData LocalDecl MirPhaseTag ContractRole CapturedAllocation
  CapturedMir
)

namespace UintTy
export Trusted.Rustc.V2026_06_01.MirAst.UintTy (bitWidth byteWidth)
end UintTy

namespace IntTy
export Trusted.Rustc.V2026_06_01.MirAst.IntTy (bitWidth byteWidth)
end IntTy

namespace ScalarInt
export Trusted.Rustc.V2026_06_01.MirAst.ScalarInt (inRange)
end ScalarInt

namespace ProvenancePtr
export Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr (tag)
end ProvenancePtr

namespace CapturedMir
export Trusted.Rustc.V2026_06_01.MirAst.CapturedMir (
  getBlock? getLocalDecl? isRuntimePostCleanup wellFormed
)
end CapturedMir

end Trusted.MirAst
