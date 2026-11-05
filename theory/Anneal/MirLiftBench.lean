import Trusted
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.MirLiftCore

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirLiftCore
open Anneal.PureMirExec

def makeEmptyBlock (bb : BasicBlockIdx) (next : BasicBlockIdx) : BasicBlockData :=
  { statements := [], terminator := { kind := .goto next, span := "bench" }, isCleanup := false }

def benchBody : CapturedMir :=
  { pureAdtMultiBlockBody with
    basicBlocks := [
      makeEmptyBlock 0 1,
      makeEmptyBlock 1 2,
      makeEmptyBlock 2 3,
      makeEmptyBlock 3 4,
      makeEmptyBlock 4 5,
      makeEmptyBlock 5 6,
      makeEmptyBlock 6 7,
      makeEmptyBlock 7 8,
      makeEmptyBlock 8 9,
      makeEmptyBlock 9 10,
      { statements := [], terminator := { kind := .return_, span := "bench" }, isCleanup := false }
    ],
    argCount := 0
  }

theorem bench_converges : LiftBlock benchBody 0 [ .init (.scalar { bits := 0, sizeBytes := 4 }) ] (fun v => v = (.scalar { bits := 0, sizeBytes := 4 })) := by
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_goto
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.nil_return
  · rfl
  · rfl
