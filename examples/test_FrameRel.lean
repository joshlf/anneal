import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.SimLM1_4

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.Layout

theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
  (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
  cases hx : x m with
  | error e m1 => rw [EStateM.bind, hx] at h; contradiction
  | ok a m1 => rw [EStateM.bind, hx] at h; exact ⟨a, m1, rfl, h⟩

theorem LocalRel_cacheLayout {mach decl layouts slot value} {lay : Miri.Interpreter.LocalLayout} :
  lay = translateTy decl.ty layouts →
  LocalRel mach decl layouts slot value →
  LocalRel mach decl layouts slot { value with layout := some lay } := by
  intro hl hrel
  cases hrel
  · apply LocalRel.dead
    intro l hl_some
    cases hl_some
    exact hl
  · apply LocalRel.immediate
    · intro l hl_some
      cases hl_some
      exact hl
    · assumption
  · apply LocalRel.indirect
    · intro l hl_some
      cases hl_some
      exact hl
    · assumption
    · assumption

theorem FrameRel_cacheLayout {body mach af mf} {idx : Nat} {lay : Miri.Interpreter.LocalLayout}
  (hrel : FrameRel body mach af mf)
  {decl_cached : LocalDecl}
  (hdecl : get? body.localDecls idx = some decl_cached)
  (hlay : lay = translateTy decl_cached.ty body.layouts)
  (hlt : idx < mf.locals.size) :
  FrameRel body mach af (cacheFrameLocalLayout mf idx hlt lay) := by
  cases hrel with | mk body_eq loc_eq af_locals_len mf_locals_len h_locs =>
  apply FrameRel.mk
  · exact body_eq
  · exact loc_eq
  · exact af_locals_len
  · unfold cacheFrameLocalLayout; dsimp; rw [Array.size_set]; exact mf_locals_len
  · intro i decl_i slot mls_i h_decl_i h_slot_i h_mls_i
    unfold cacheFrameLocalLayout at h_mls_i; dsimp at h_mls_i
    rw [Array.getElem?_set] at h_mls_i
    split at h_mls_i
    next heq =>
      subst i
      rw [hdecl] at h_decl_i
      cases h_decl_i
      have h_mls_idx : mf.locals[idx]? = some (mf.locals[idx]'hlt) := by
        apply Array.getElem?_eq_getElem
      have h_loc := h_locs idx decl_cached slot (mf.locals[idx]'hlt) hdecl h_slot_i h_mls_idx
      injection h_mls_i with heq_mls
      subst mls_i
      apply LocalRel_cacheLayout hlay h_loc
    next hneq =>
      exact h_locs i decl_i slot mls_i h_decl_i h_slot_i h_mls_i

theorem StateRel_placeLayoutOfLocal {body s m localId lay m_new} :
  StateRel body s m →
  Miri.Interpreter.placeLayoutOfLocal (annealPlaceHooks body.localDecls body.layouts) () localId m = EStateM.Result.ok lay m_new →
  StateRel body s m_new := by
  intro hstate hl
  unfold Miri.Interpreter.placeLayoutOfLocal at hl
  have ⟨f1, m1, h_f1, hl1⟩ := split_bind hl
  have ⟨s_loc, m2, h_loc, hl2⟩ := split_bind hl1
  cases h_s_layout : s_loc.layout
  case some layout =>
    rw [h_s_layout] at hl2
    dsimp only at hl2
    dsimp [pure, EStateM.pure] at hl2
    injection hl2 with _ h_m_eq; subst m_new
    exact hstate
  case none =>
    rw [h_s_layout] at hl2
    dsimp only at hl2
    have ⟨lay2, m3, h_lay, hl3⟩ := split_bind hl2
    have ⟨f2, m4, h_f2, hl4⟩ := split_bind hl3
    have ⟨cache_res, m5, h_cache, hl5⟩ := split_bind hl4
    rcases cache_res with ⟨frame, cached⟩
    dsimp only at hl5
    have ⟨res_sf, m6, h_sf, hl6⟩ := split_bind hl5
    dsimp [pure, EStateM.pure] at hl6
    injection hl6 with _ h_m_eq; subst m_new
    
    dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.getFrame, get, EStateM.get, StateT.get] at h_f1 h_f2
    injection h_f1 with _ hm1; subst m1
    injection h_f2 with _ hm4; subst m4
    
    have hframes := hstate.frames_eq
    unfold Miri.Interpreter.Stack.currentFrame? at h_loc hl4
    rw [hframes] at h_loc hl4
    dsimp [Array.back?, pure, EStateM.pure] at h_loc hl4
    injection h_loc with hs_loc hm2; subst m2 s_loc
    
    dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.resolveLayout, pure, EStateM.pure] at h_lay
    injection h_lay with hlay_eq hm3; subst m3 lay2
    
    -- h_cache is stackLift, which evaluates to pure
    -- stackLift x = match x with ok a => pure a | error e => throw e
    -- So `stackLift ... m = ok ... m5` means `m5 = m`.
    -- Wait, how to prove it?
    -- split_bind on h_cache? No, stackLift is not bind!
    -- I can just unfold stackLift
    unfold Miri.Interpreter.stackLift at h_cache
    split at h_cache
    next ok_val heq_cache =>
      dsimp [pure, EStateM.pure] at h_cache
      injection h_cache with hres_eq hm5
      subst m5 cache_res
    
      apply StateRel_setFrame hstate h_sf
      · sorry
      · sorry
      · sorry
      · sorry
    next err_val heq_cache =>
      dsimp [throw, EStateM.throw] at h_cache
      contradiction

