import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.SimLM1_4

namespace LeanMiriSpec.Correspondence

theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
  (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
  cases hx : x m with
  | error e m1 => rw [EStateM.bind, hx] at h; contradiction
  | ok a m1 => rw [EStateM.bind, hx] at h; exact ⟨a, m1, rfl, h⟩

theorem StateRel_writeMemoryNoValidate {body s m value mplace w m_new} :
  StateRel body s m →
  (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () value mplace m = EStateM.Result.ok w m_new →
  StateRel body s m_new := by
  intro hs hw
  unfold Miri.Interpreter.PlaceHooks.writeMemoryNoValidate at hw
  dsimp [annealPlaceHooks] at hw
  cases mplace.meta
  case some =>
    dsimp [throw, EStateM.throw] at hw
    contradiction
  case none =>
    cases hprov : mplace.ptr.provenance
    case none =>
      rw [hprov] at hw
      dsimp [throw, EStateM.throw] at hw
      contradiction
    case some prov =>
      rw [hprov] at hw
      dsimp [get, EStateM.get, StateT.get] at hw
      cases halloc : m.machine.memory.allocations.find? prov.allocId
      case none =>
        rw [halloc] at hw
        dsimp [throw, EStateM.throw] at hw
        contradiction
      case some alloc =>
        rw [halloc] at hw
        cases hwrite : Miri.Memory.MemoryState.write m.machine.memory prov.allocId mplace.ptr.offset.bytes value.toBytes
        case error =>
          rw [hwrite] at hw
          dsimp [throw, EStateM.throw] at hw
          contradiction
        case ok new_alloc =>
          rw [hwrite] at hw
          dsimp [set, EStateM.set, StateT.set, pure, EStateM.pure] at hw
          injection hw with _ hm_eq
          subst m_new
          
          cases hs with | mk frames_eq frames_rel returnContinuation_eq returnPlace_eq frame_rel =>
          apply StateRel.mk frames_eq frames_rel
          · exact returnContinuation_eq
          · exact returnPlace_eq
          · apply FrameRel_update
            · intro x hx
              exact hx
            · rfl
            · exact frame_rel

