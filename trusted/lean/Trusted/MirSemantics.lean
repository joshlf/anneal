import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_06_01.MirSemantics.Eval
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine

namespace Trusted.MirSemantics

/-!
Default dialect alias re-exporting `Trusted.Rustc.V2026_06_01.MirSemantics`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/

export Trusted.Rustc.V2026_06_01.MirSemantics (
  MirObs Value LocalSlot StackFrame TreeBorrowPerm LocalIdx BorrowEntry
  SavedCallerFrame Memory emptyMemory MachineState
  MirCallReq MirCallAns MirFailE MirObsE MirCallE MirEffect MirReturn MirOutcome
  MirExecState MirStepNode
  ProjReadResult ProjWriteResult PlaceReadResult OperandEvalResult
  LookupResult OperandsEvalResult RvalueEvalResult PlaceWriteResult
  appendProjections replicateValue listByteEq stringEq initLocalsAux initLocals
  scalarModulus scalarPow2 wrapScalarBits boolToScalar bitwiseAndBits
  bitwiseOrBits bitwiseXorBits shiftLeftBits shiftRightUnsignedBits
  isSignedNegative arithmeticShrBits signedLt signedLe signExtendBits
  emptyLayoutTable pointeeTyOf elemTyOf resolveProjectedTy placeTy operandTy
  tyIsSigned placeIsSigned operandIsSigned evalUnaryNot signedOverflowAdd
  signedOverflowSub signedOverflowMul evalSignedDiv evalSignedRem
  evalScalarBinOp intCastTargetBytes ScalarVal AbstractByte mergeByteProvenance
  encodeLittleEndianBytes encodeScalarBytes decodeLittleEndianBytes
  decodeScalarBytes replicateUninitBytes takeAbstractBytes dropAbstractBytes
  appendAbstractBytes sliceAbstractBytes writeAbstractBytesAt
  lookupRelocAllocId globalAllocBytesAux globalAllocSliceToAbstractBytes
  isValidCharCode wrappingRangeContains primitiveKindByteWidth
  scalarLayoutByteWidth decodeScalarLayoutBytes rigidTyKindByteSize
  tupleFieldsByteSize rigidTyByteSize encodeListWith decodeArrayChunksWith
  encodeUntypedValueToBytes encodeFieldsAtOffsetsWith encodeSeqFieldsWith
  decodeFieldsAtOffsetsWith decodeFieldsBySpan decodeSeqFieldsWith
  defaultCodecFuel encodeValueToBytes decodeValueFromBytes lookupBorrow
  updateBorrowPerm invalidateConflictingBorrows lookupGlobalAlloc
  readLittleEndianBytes readGlobalScalar tyScalarBytes evalConstValue
  dropValues takeValues extractSubslice readProjectedValue writeProjectedValue
  sliceConstElemKind evalOperand evalOperands writePlaceValue evalByteCast
  evalRvalue evalRvalueWithMemory advanceStmt projectionsOverlap appendValues
  spliceValues sameRigidTyShape operandPointeeTy evalCopySingleDirect
  evalCopyNonOverlappingWithCount evalCopyNonOverlapping
  evalStmt lookupSwitchTarget findCallee?
  extractCalleeDefPath? applyUnwindAction resumeExternalCall
  resumeExternalTailCall evalTerminator
  initMachineState initMachineStateWithCallees
  stepMirFn stepMirState mirTree mirCallTree MirCallInstance
  MirLang MirNoUBTree
)

end Trusted.MirSemantics
