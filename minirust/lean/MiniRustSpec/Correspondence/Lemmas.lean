/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Relation

/-!
# Lemmas about the translation and the MiniRust interpretation

Symbolic-evaluation facts used by the simulation proof: what `translateFn`
produces, and what the interpreted MiniRust functions compute on machines in
the shape described by `StateRel`.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Association lists -/

theorem mapGet_nil {K V : Type} [DecidableEq K] (k : K) : mapGet (⟨[]⟩ : Map K V) k = none := rfl

theorem mapGet_cons {K V : Type} [DecidableEq K] (k k' : K) (v : V) (es : List (K × V)) :
    mapGet ⟨(k', v) :: es⟩ k = if k' = k then some v else mapGet ⟨es⟩ k := by
  unfold mapGet
  by_cases h : k' = k <;> simp [h]

theorem mapGet_append_of_some {K V : Type} [DecidableEq K] (k : K) (v : V) (es es' : List (K × V))
    (h : mapGet ⟨es⟩ k = some v) : mapGet ⟨es ++ es'⟩ k = some v := by
  induction es with
  | nil => simp [mapGet_nil] at h
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    rw [List.cons_append, mapGet_cons]
    rw [mapGet_cons] at h
    split
    · next hk => simp [hk] at h; simp [h]
    · next hk => simp [hk] at h; exact ih h

theorem localName_inj (a b : Nat) : localName a = localName b ↔ a = b := by
  simp [localName]

theorem bbName_inj (a b : Nat) : bbName a = bbName b ↔ a = b := by
  simp [bbName]

/-! ## `translateFn` -/

theorem translateLocals_get (k : Nat) (ds : List LocalDecl) (L : List (Gen.LocalName × Gen.Type))
    (h : translateLocals k ds = some L) (j : Nat) (d : LocalDecl) (hd : ds[j]? = some d) :
    ∃ it, intTypeOf d.ty = some it ∧ mapGet ⟨L⟩ (localName (k + j)) = some (.Int it) := by
  induction ds generalizing k L j with
  | nil => simp at hd
  | cons d' ds ih =>
    simp only [translateLocals, Option.bind_eq_bind] at h
    cases hit : intTypeOf d'.ty with
    | none => simp [hit] at h
    | some it' =>
      cases hrest : translateLocals (k + 1) ds with
      | none => simp [hit, hrest] at h
      | some rest =>
        simp [hit, hrest] at h
        subst h
        cases j with
        | zero =>
          simp at hd; subst hd
          exact ⟨it', hit, by simp [mapGet_cons]⟩
        | succ j =>
          simp at hd
          obtain ⟨it, hit2, hget⟩ := ih (k + 1) rest hrest j hd
          refine ⟨it, hit2, ?_⟩
          rw [mapGet_cons]
          split
          · next heq => rw [localName_inj] at heq; omega
          · rw [show k + (j + 1) = k + 1 + j by omega]; exact hget

theorem translateBlocks_get (decls : List LocalDecl) (k : Nat) (bbs : List BasicBlockData)
    (B : List (Gen.BbName × Gen.BasicBlock)) (h : translateBlocks decls k bbs = some B) (j : Nat)
    (bb : BasicBlockData) (hb : bbs[j]? = some bb) :
    ∃ tb, translateBlock decls bb = some tb ∧ mapGet ⟨B⟩ (bbName (k + j)) = some tb := by
  induction bbs generalizing k B j with
  | nil => simp at hb
  | cons bb' bbs ih =>
    simp only [translateBlocks, Option.bind_eq_bind] at h
    cases htb : translateBlock decls bb' with
    | none => simp [htb] at h
    | some tb' =>
      cases hrest : translateBlocks decls (k + 1) bbs with
      | none => simp [htb, hrest] at h
      | some rest =>
        simp [htb, hrest] at h
        subst h
        cases j with
        | zero =>
          simp at hb; subst hb
          exact ⟨tb', htb, by simp [mapGet_cons]⟩
        | succ j =>
          simp at hb
          obtain ⟨tb, htb2, hget⟩ := ih (k + 1) rest hrest j hb
          refine ⟨tb, htb2, ?_⟩
          rw [mapGet_cons]
          split
          · next heq => rw [bbName_inj] at heq; omega
          · rw [show k + (j + 1) = k + 1 + j by omega]; exact hget

/-- What `translateFn` produces, in the form the simulation proof consumes. -/
theorem translateFn_spec (body : CapturedMir) (f : Gen.Function) (h : translateFn body = some f) :
    f.ret = localName 0 ∧
    (∀ (i : Nat) d, body.localDecls[i]? = some d →
      intTypeOf d.ty = some (itOf d) ∧ mapGet f.locals (localName i) = some (.Int (itOf d))) ∧
    (∀ (i : Nat) bb, body.basicBlocks[i]? = some bb →
      ∃ tb, translateBlock body.localDecls bb = some tb ∧ mapGet f.blocks (bbName i) = some tb) := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hL : translateLocals 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocks body.localDecls 0 body.basicBlocks with
    | none => simp [hL, hB] at h
    | some B =>
      simp [hL, hB] at h
      subst h
      refine ⟨rfl, ?_, ?_⟩
      · intro i d hd
        obtain ⟨it, hit, hget⟩ := translateLocals_get 0 body.localDecls L hL i d hd
        have : itOf d = it := by simp [itOf, hit]
        rw [this]; refine ⟨hit, ?_⟩
        simpa using hget
      · intro i bb hbb
        obtain ⟨tb, htb, hget⟩ := translateBlocks_get body.localDecls 0 body.basicBlocks B hB i bb hbb
        refine ⟨tb, htb, ?_⟩
        apply mapGet_append_of_some
        simpa using hget

theorem translateBlocks_append_get (decls : List LocalDecl) (k : Nat) (bbs : List BasicBlockData)
    (B : List (Gen.BbName × Gen.BasicBlock)) (h : translateBlocks decls k bbs = some B)
    (m : Nat) (hm : k + bbs.length ≤ m) :
    mapGet ⟨B ++ [(bbName m, initBlock)]⟩ (bbName m) = some initBlock := by
  induction bbs generalizing k B with
  | nil => simp [translateBlocks] at h; subst h; simp [mapGet_cons]
  | cons bb bbs ih =>
    simp only [translateBlocks, Option.bind_eq_bind] at h
    cases htb : translateBlock decls bb with
    | none => simp [htb] at h
    | some tb =>
      cases hrest : translateBlocks decls (k + 1) bbs with
      | none => simp [htb, hrest] at h
      | some rest =>
        simp [htb, hrest] at h
        subst h
        rw [List.cons_append, mapGet_cons]
        split
        · next heq => rw [bbName_inj] at heq; simp at hm; omega
        · exact ih (k + 1) rest hrest (by simp at hm; omega)

/-- `translateFn` sets `f.start` to `bbName body.basicBlocks.length` and maps
that name to `initBlock` (`Goto(bb0)`). -/
theorem translateFn_start (body : CapturedMir) (f : Gen.Function) (h : translateFn body = some f) :
    f.start = bbName body.basicBlocks.length ∧
    mapGet f.blocks (bbName body.basicBlocks.length) = some initBlock := by
  simp only [translateFn, Option.bind_eq_bind] at h
  cases hL : translateLocals 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocks body.localDecls 0 body.basicBlocks with
    | none => simp [hL, hB] at h
    | some B =>
      simp [hL, hB] at h
      subst h
      exact ⟨rfl, translateBlocks_append_get body.localDecls 0 body.basicBlocks B hB
        body.basicBlocks.length (by omega)⟩

end MiniRustSpec.Correspondence
