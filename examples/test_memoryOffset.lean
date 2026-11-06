import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.SimLM1_4

namespace LeanMiriSpec.Correspondence

theorem StateRel_memoryOffset {body s m whole offset mode memmeta mplace m_new} :
  StateRel body s m →
  (annealPlaceHooks body.localDecls body.layouts).memoryOffset () whole offset mode memmeta m = EStateM.Result.ok mplace m_new →
  StateRel body s m_new := by
  intro hs hl
  unfold Miri.Interpreter.PlaceHooks.memoryOffset at hl
  dsimp [annealPlaceHooks, throw, EStateM.throw] at hl
  cases hl

