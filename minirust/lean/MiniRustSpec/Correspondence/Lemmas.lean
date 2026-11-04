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
    ∃ ty, translateTy d.ty = some ty ∧ mapGet ⟨L⟩ (localName (k + j)) = some ty := by
  induction ds generalizing k L j with
  | nil => simp at hd
  | cons d' ds ih =>
    simp only [translateLocals, Option.bind_eq_bind] at h
    cases hty : translateTy d'.ty with
    | none => simp [hty] at h
    | some ty' =>
      cases hrest : translateLocals (k + 1) ds with
      | none => simp [hty, hrest] at h
      | some rest =>
        simp [hty, hrest] at h
        subst h
        cases j with
        | zero =>
          simp at hd; subst hd
          exact ⟨ty', hty, by simp [mapGet_cons]⟩
        | succ j =>
          simp at hd
          obtain ⟨ty, hty2, hget⟩ := ih (k + 1) rest hrest j hd
          refine ⟨ty, hty2, ?_⟩
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
      ∃ ty, translateTy d.ty = some ty ∧ mapGet f.locals (localName i) = some ty) ∧
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
        obtain ⟨ty, hty, hget⟩ := translateLocals_get 0 body.localDecls L hL i d hd
        exact ⟨ty, hty, by simpa using hget⟩
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

theorem arrayTypeOf_none_of_intTypeOf {t : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf t = some it) : arrayTypeOf t = none := by
  unfold intTypeOf intTyBytes at h
  unfold arrayTypeOf
  split at h <;> simp_all

theorem intTypeOf_none_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) : intTypeOf t = none := by
  unfold arrayTypeOf at h
  unfold intTypeOf intTyBytes
  split at h <;> simp_all

theorem itOf_eq_of_intTypeOf {d : LocalDecl} {it : Gen.IntType}
    (h : intTypeOf d.ty = some it) : itOf d = it := by
  simp [itOf, arrayTypeOf_none_of_intTypeOf h, h]

theorem itOf_eq_of_arrayTypeOf {d : LocalDecl} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf d.ty = some (elemIt, count)) : itOf d = elemIt := by
  simp [itOf, h]

theorem translateTy_of_intTypeOf {t : MirAst.Ty} {it : Gen.IntType}
    (h : intTypeOf t = some it) : translateTy t = some (.Int it) := by
  simp [translateTy, h]

theorem translateTy_of_arrayTypeOf {t : MirAst.Ty} {elemIt : Gen.IntType} {count : Nat}
    (h : arrayTypeOf t = some (elemIt, count)) :
    translateTy t = some (.Array (.Int elemIt) (Int.ofNat count)) := by
  simp [translateTy, intTypeOf_none_of_arrayTypeOf h, h]

/-! ## Uniform byte-chunk lists for homogeneous arrays -/

theorem drop_length_add_append {β : Type} (a b : List β) (n : Nat) :
    (a ++ b).drop (a.length + n) = b.drop n := by
  induction a with
  | nil => simp
  | cons _ a ih => simp [Nat.succ_add, ih]

theorem take_length_add_append {β : Type} (a b : List β) (n : Nat) :
    (a ++ b).take (a.length + n) = a ++ b.take n := by
  induction a with
  | nil => simp
  | cons _ a ih => simp [Nat.succ_add, ih]

theorem flatten_map_length {α β : Type} (f : α → List β) (k : Nat) (xs : List α)
    (hf : ∀ x ∈ xs, (f x).length = k) :
    (xs.map f).flatten.length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : (f x).length = k := hf x (by simp)
    have hxs : ∀ y ∈ xs, (f y).length = k := fun y hy => hf y (by simp [hy])
    simp [hx, ih hxs, Nat.succ_mul, Nat.add_comm]

theorem drop_mul_take_flatten_map {α β : Type} (f : α → List β) (k : Nat)
    (xs : List α) (hf : ∀ x ∈ xs, (f x).length = k) (i : Nat) (x : α)
    (hi : xs[i]? = some x) :
    ((xs.map f).flatten.drop (i * k)).take k = f x := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    have hhd : (f hd).length = k := hf hd (by simp)
    have htl : ∀ y ∈ tl, (f y).length = k := fun y hy => hf y (by simp [hy])
    cases i with
    | zero =>
      simp at hi; subst hi
      have htake := take_length_add_append (f hd) (tl.map f).flatten 0
      rw [hhd, Nat.add_zero] at htake
      simpa using htake
    | succ j =>
      simp at hi
      rw [List.map_cons, List.flatten_cons,
        show (j + 1) * k = (f hd).length + j * k by rw [hhd, Nat.succ_mul, Nat.add_comm],
        drop_length_add_append]
      exact ih htl j hi

theorem subsliceWithLength_flatten_map {α β : Type} (f : α → List β) (k : Nat)
    (xs : List α) (hf : ∀ x ∈ xs, (f x).length = k) (i : Nat) (x : α)
    (hi : xs[i]? = some x) :
    subsliceWithLength (xs.map f).flatten ((i * k : Nat) : Int) (k : Int) = .ok (f x) := by
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : (xs.map f).flatten.length = xs.length * k := flatten_map_length f k xs hf
  have hle : i * k + k ≤ (xs.map f).flatten.length := by
    rw [hlen, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right k (by omega)
  have hle' : ((i * k : Nat) : Int) + (k : Int) ≤ ((xs.map f).flatten.length : Int) := by
    exact_mod_cast hle
  unfold subsliceWithLength
  split
  · have htonat1 : (((i * k : Nat) : Int)).toNat = i * k := rfl
    have htonat2 : ((k : Int)).toNat = k := rfl
    rw [htonat1, htonat2, drop_mul_take_flatten_map f k xs hf i x hi]
    rfl
  · next hbad =>
    exfalso
    apply hbad
    exact ⟨by omega, by omega, hle'⟩

theorem splice_flatten_map {α β : Type} (f : α → List β) (k : Nat)
    (xs : List α) (hf : ∀ x ∈ xs, (f x).length = k) (i : Nat) (v : α)
    (hi : i < xs.length) :
    (xs.map f).flatten.take (i * k) ++ f v ++ (xs.map f).flatten.drop (i * k + k) =
      ((xs.set i v).map f).flatten := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    have hhd : (f hd).length = k := hf hd (by simp)
    have htl : ∀ y ∈ tl, (f y).length = k := fun y hy => hf y (by simp [hy])
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.map_cons, List.flatten_cons, List.set_cons_zero]
      have hdrop := drop_length_add_append (f hd) (tl.map f).flatten 0
      rw [hhd, Nat.add_zero] at hdrop
      simp [hdrop]
    | succ j =>
      simp only [List.length_cons] at hi
      have hj : j < tl.length := by omega
      simp only [List.map_cons, List.flatten_cons, List.set_cons_succ]
      rw [show (j + 1) * k = (f hd).length + j * k by rw [hhd, Nat.succ_mul, Nat.add_comm],
        take_length_add_append,
        show (f hd).length + j * k + k = (f hd).length + (j * k + k) by omega,
        drop_length_add_append]
      simp only [List.append_assoc]
      congr 1
      simpa [List.append_assoc] using ih htl j hj

end MiniRustSpec.Correspondence
