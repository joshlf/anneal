import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.SimLM1_4

namespace LeanMiriSpec.Correspondence

theorem StateRel_placeLayoutOfLocal_sim {body s m localId lay m_new} :
  StateRel body s m →
  Miri.Interpreter.placeLayoutOfLocal (annealPlaceHooks body.localDecls body.layouts) () localId m = EStateM.Result.ok lay m_new →
  StateRel body s m_new := by
  intro hstate hl
  unfold Miri.Interpreter.placeLayoutOfLocal at hl
  have ⟨f1, m1, h_f1, hl1⟩ := split_bind hl
  have ⟨s_loc, m2, h_loc, hl2⟩ := split_bind hl1
  split at hl2
  next layout h_layout_some =>
    dsimp [pure, EStateM.pure] at hl2
    injection hl2 with _ h_m_eq; subst m_new
    exact hstate
  next h_layout_none =>
    have ⟨lay2, m3, h_lay, hl3⟩ := split_bind hl2
    have ⟨f2, m4, h_f2, hl4⟩ := split_bind hl3
    have ⟨cache_res, m5, h_cache, hl5⟩ := split_bind hl4
    have ⟨res_sf, m6, h_sf, hl6⟩ := split_bind hl5
    sorry

