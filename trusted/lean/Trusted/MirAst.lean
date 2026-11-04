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
  GenericParamDef TraitRef TraitImplEntry TypeSubst
  CapturedMir
  instantiate_nil instantiate_empty_id instantiate_wellFormed
)

namespace UintTy
export Trusted.Rustc.V2026_06_01.MirAst.UintTy (bitWidth byteWidth)
end UintTy

namespace IntTy
export Trusted.Rustc.V2026_06_01.MirAst.IntTy (bitWidth byteWidth)
end IntTy

namespace FloatTy
export Trusted.Rustc.V2026_06_01.MirAst.FloatTy (byteWidth)
end FloatTy

namespace ScalarInt
export Trusted.Rustc.V2026_06_01.MirAst.ScalarInt (inRange)
end ScalarInt

namespace ProvenancePtr
export Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr (tag)
end ProvenancePtr

namespace TypeSubst
export Trusted.Rustc.V2026_06_01.MirAst.TypeSubst (lookup layouts length)
end TypeSubst

namespace RigidTy
export Trusted.Rustc.V2026_06_01.MirAst.RigidTy (
  instantiate instantiateList instantiate_nil instantiateList_nil
  instantiateList_nil_eq instantiate_empty_id hasSubstParam hasSubstParamList
  isCompoundSubstParam instantiate_of_hasSubstParam_false
  instantiateList_of_hasSubstParamList_false
  hasSubstParam_nil hasSubstParamList_nil computeLayout computeLayoutList
)
end RigidTy

namespace LayoutTable
export Trusted.Rustc.V2026_06_01.MirAst.LayoutTable (
  instantiate instantiate_nil instantiate_empty_id
  instantiateForDecls instantiateForDecls_nil
)
end LayoutTable

namespace Ty
export Trusted.Rustc.V2026_06_01.MirAst.Ty (
  instantiate instantiate_nil instantiate_empty_id
  instantiate_of_hasSubstParam_false
)
end Ty

namespace ConstOperand
export Trusted.Rustc.V2026_06_01.MirAst.ConstOperand (
  instantiate instantiate_nil
)
end ConstOperand

namespace TraitRef
export Trusted.Rustc.V2026_06_01.MirAst.TraitRef (
  instantiate instantiate_nil
)
end TraitRef

namespace TraitImplEntry
export Trusted.Rustc.V2026_06_01.MirAst.TraitImplEntry (
  instantiate instantiateList instantiate_nil instantiateList_nil
)
end TraitImplEntry

namespace ProjectionElem
export Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem (
  instantiate instantiateList instantiate_nil instantiateList_nil
)
end ProjectionElem

namespace Place
export Trusted.Rustc.V2026_06_01.MirAst.Place (
  instantiate instantiate_nil
)
end Place

namespace Operand
export Trusted.Rustc.V2026_06_01.MirAst.Operand (
  instantiate instantiateList instantiate_nil instantiateList_nil
)
end Operand

namespace AggregateKind
export Trusted.Rustc.V2026_06_01.MirAst.AggregateKind (
  instantiate instantiate_nil
)
end AggregateKind

namespace Rvalue
export Trusted.Rustc.V2026_06_01.MirAst.Rvalue (
  instantiate instantiate_nil
)
end Rvalue

namespace NonDivergingIntrinsic
export Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic (
  instantiate instantiate_nil
)
end NonDivergingIntrinsic

namespace StatementKind
export Trusted.Rustc.V2026_06_01.MirAst.StatementKind (
  instantiate instantiate_nil
)
end StatementKind

namespace Statement
export Trusted.Rustc.V2026_06_01.MirAst.Statement (
  instantiate instantiateList instantiate_nil instantiateList_nil
)
end Statement

namespace TerminatorKind
export Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind (
  instantiate instantiate_nil
)
end TerminatorKind

namespace Terminator
export Trusted.Rustc.V2026_06_01.MirAst.Terminator (
  instantiate instantiate_nil
)
end Terminator

namespace BasicBlockData
export Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData (
  instantiate instantiateList instantiate_nil instantiateList_nil
  instantiateList_nonEmpty instantiateList_length
)
end BasicBlockData

namespace LocalDecl
export Trusted.Rustc.V2026_06_01.MirAst.LocalDecl (
  instantiate instantiateList instantiate_nil instantiateList_nil
  instantiateList_nonEmpty instantiateList_length
)
end LocalDecl

namespace ArgAbi
export Trusted.Rustc.V2026_06_01.MirAst.ArgAbi (
  recomputeMode instantiateForDecl instantiateListForDecls
  instantiateForDecl_nil instantiateListForDecls_nil
)
end ArgAbi

namespace FnAbi
export Trusted.Rustc.V2026_06_01.MirAst.FnAbi (
  instantiate instantiate_nil
)
end FnAbi

namespace CapturedMir
export Trusted.Rustc.V2026_06_01.MirAst.CapturedMir (
  getBlock? getLocalDecl? isRuntimePostCleanup wellFormed
  instantiate instantiate_nil instantiate_empty_id
  instantiate_defPath instantiate_phase instantiate_role
  instantiate_argCount instantiate_allocations instantiate_typeParamCount
  instantiate_isRuntimePostCleanup instantiate_localDecls_length
  instantiate_basicBlocks_length instantiate_wellFormed
)
end CapturedMir

end Trusted.MirAst
