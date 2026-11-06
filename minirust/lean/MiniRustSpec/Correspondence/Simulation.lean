/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.AnnealEval

/-!
# The correspondence theorem

`step_correspondence` states that, for every fragment body and every pair of
related states, one step of Anneal's trusted MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`) and one step of the
ground-truth MiniRust interpretation (`MiniRustSpec.Interp.step`, which
executes the MiniRust program that MiniRust's own `minimize` tool produces
for the body) agree in the sense of `StepRel`: both continue in related
states, both perform a related function return, or both raise UB.
`step_start` runs `minimize`'s init block (`initLen body` MiniRust steps) from
the entry relation `StartRel` into `StateRel`.
`MiniRustSpec.Correspondence.Run` lifts these to whole executions.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Facts about the fragment check and the translation -/

theorem mapM_option_spec {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ (k : Nat) x, xs[k]? = some x → ∃ y, f x = some y ∧ ys[k]? = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst h; simp
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some ys' =>
        simp [hx, hxs] at h
        subst h
        obtain ⟨hlen, hget⟩ := ih ys' hxs
        refine ⟨by simp [hlen], fun k x' hk => ?_⟩
        cases k with
        | zero => simp at hk; subst hk; exact ⟨y, hx, rfl⟩
        | succ k => simp at hk; simpa using hget k x' hk

theorem translateBlock_spec (decls : List LocalDecl) (bb : BasicBlockData) (tb : Gen.BasicBlock)
    (h : translateBlock decls bb = some tb) :
    tb.statements.length = bb.statements.length ∧
    (∀ (k : Nat) st, bb.statements[k]? = some st →
      ∃ st', translateStatement decls st = some st' ∧ tb.statements[k]? = some st') ∧
    translateTerminator decls bb.terminator = some tb.terminator := by
  simp only [translateBlock, Option.bind_eq_bind] at h
  cases hs : bb.statements.mapM (translateStatement decls) with
  | none => simp [hs] at h
  | some stmts =>
    cases ht : translateTerminator decls bb.terminator with
    | none => simp [hs, ht] at h
    | some term =>
      simp [hs, ht] at h
      subst h
      obtain ⟨hlen, hget⟩ := mapM_option_spec (translateStatement decls) bb.statements stmts hs
      exact ⟨hlen, hget, rfl⟩

/-- Facts about a body accepted by `inFragment`. -/
theorem inFragment_spec (body : CapturedMir) (h : inFragment body = true) :
    body.phase = .runtimePostCleanup ∧ body.argCount + 1 ≤ body.localDecls.length ∧
    body.localDecls.length < 2 ^ 31 ∧
    (∀ bb ∈ body.basicBlocks, bb.isCleanup = false ∧
      (∀ st ∈ bb.statements, statementOk body.localDecls st = true) ∧
      terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true) ∧
    storageDeadOk body = true ∧ movesOk body = true ∧ mentionsOk body = true := by
  simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hphase, hargs⟩, hn⟩, _⟩, _⟩, hbbs⟩, hsd⟩, hmv⟩, hmt⟩, _⟩ := h
  refine ⟨?_, hargs, hn, fun bb hbb => ?_, hsd, hmv, hmt⟩
  · unfold CapturedMir.isRuntimePostCleanup at hphase
    split at hphase <;> simp_all
  · obtain ⟨⟨hc, hst⟩, ht⟩ := hbbs bb hbb
    exact ⟨hc, hst, ht⟩

theorem storageDeadOk_spec {body : CapturedMir} (h : storageDeadOk body = true)
    {bb : BasicBlockData} (hbb : bb ∈ body.basicBlocks) {st : MirAst.Statement}
    (hst : st ∈ bb.statements) {i : Nat} (hk : st.kind = .storageDead i) : body.argCount < i := by
  simp only [storageDeadOk, List.all_eq_true] at h
  have := h bb hbb st hst
  rw [hk] at this
  simpa using this

theorem mentionsOk_stmt {body : CapturedMir} (h : mentionsOk body = true)
    {bb : BasicBlockData} (hbb : bb ∈ body.basicBlocks) {st : MirAst.Statement}
    (hst : st ∈ bb.statements) {j : Nat} (hj : j ∈ stmtLocals st) :
    j ∉ alwaysStorageLiveLocals body := by
  simp only [mentionsOk, List.all_eq_true, Bool.and_eq_true] at h
  have := (h bb hbb).1 st hst j hj
  simpa using this

theorem mentionsOk_term {body : CapturedMir} (h : mentionsOk body = true)
    {bb : BasicBlockData} (hbb : bb ∈ body.basicBlocks) {j : Nat} (hj : j ∈ termLocals bb.terminator) :
    j ∉ alwaysStorageLiveLocals body := by
  simp only [mentionsOk, List.all_eq_true, Bool.and_eq_true] at h
  have := (h bb hbb).2 j hj
  simpa using this

/-! ## Moved-out locals -/

theorem foldl_moveOut_mem (ops : List Operand) (acc : List Nat) (j : Nat) :
    j ∈ ops.foldl moveOut acc ↔ j ∈ acc ∨ j ∈ ops.filterMap opMoved := by
  induction ops generalizing acc with
  | nil => simp
  | cons op ops ih =>
    rw [List.foldl_cons, ih]
    unfold moveOut
    cases h : opMoved op with
    | none => simp [List.filterMap_cons_none h]
    | some k =>
      simp only [List.mem_cons, List.filterMap_cons_some h]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact .inr (.inl h1)
        · exact .inl h1
        · exact .inr (.inr h1)
      · rintro (h1 | h1 | h1)
        · exact .inl (.inr h1)
        · exact .inl (.inl h1)
        · exact .inr h1

theorem unionLocals_mem (acc xs : List Nat) (j : Nat) :
    j ∈ unionLocals acc xs ↔ j ∈ acc ∨ j ∈ xs := by
  induction xs generalizing acc with
  | nil => simp [unionLocals]
  | cons x xs ih =>
    simp only [unionLocals, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hc : acc.contains x = true
    · simp only [hc, ↓reduceIte, List.mem_cons]
      have hx : x ∈ acc := List.contains_iff_mem.mp hc
      exact ⟨fun h => h.elim .inl (.inr ∘ .inr),
        fun h => h.elim .inl (fun h2 => h2.elim (fun hjx => .inl (hjx ▸ hx)) .inr)⟩
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      exact ⟨fun h => h.elim (fun h1 => h1.elim (.inr ∘ .inl) .inl) (.inr ∘ .inr),
        fun h => h.elim (.inl ∘ .inr) (fun h2 => h2.elim (.inl ∘ .inl) .inr)⟩

/-- Each pass of `stepMovedEntries` preserves existing moved-out entries and
propagates every outgoing control-flow edge `(src → dst)` into block `dst`'s
entry set. -/
theorem stepMovedEntries_spec (bbs : List BasicBlockData) (entries : List (List Nat))
    (dst : Nat) (hdst : dst < bbs.length) :
    (∀ j ∈ entries.getD dst [], j ∈ (stepMovedEntries bbs entries).getD dst []) ∧
    (∀ (src : Nat) (bb : BasicBlockData), bbs[src]? = some bb → dst ∈ termTargets bb.terminator →
      ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator,
        j ∈ (stepMovedEntries bbs entries).getD dst []) := by
  let stepFn (acc : List Nat) (src : Nat) : List Nat :=
    match bbs[src]? with
    | some bb =>
      if (termTargets bb.terminator).contains dst then
        unionLocals acc (termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator)
      else acc
    | none => acc
  have hmono : ∀ (srcs : List Nat) (acc : List Nat) (j : Nat),
      j ∈ acc → j ∈ srcs.foldl stepFn acc := by
    intro srcs
    induction srcs with
    | nil => intro acc j hj; exact hj
    | cons s srcs ih =>
      intro acc j hj
      simp only [List.foldl_cons]
      apply ih
      simp only [stepFn]
      cases h : bbs[s]? with
      | none => exact hj
      | some bb =>
        simp only
        split
        · exact (unionLocals_mem _ _ _).mpr (.inl hj)
        · exact hj
  have hprop : ∀ (srcs : List Nat) (acc : List Nat) (src : Nat) (bb : BasicBlockData),
      src ∈ srcs → bbs[src]? = some bb → dst ∈ termTargets bb.terminator →
      ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator,
        j ∈ srcs.foldl stepFn acc := by
    intro srcs
    induction srcs with
    | nil => intro _ _ _ hmem; simp at hmem
    | cons s srcs ih =>
      intro acc src bb hmem hbb htgt j hj
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hrest
      · apply hmono
        have hcont : (termTargets bb.terminator).contains dst = true :=
          List.contains_iff_mem.mpr htgt
        simp only [stepFn, hbb, hcont, ↓reduceIte]
        exact (unionLocals_mem _ _ _).mpr (.inr hj)
      · exact ih _ src bb hrest hbb htgt j hj
  have hget : (stepMovedEntries bbs entries).getD dst [] =
      (List.range bbs.length).foldl stepFn (entries.getD dst []) := by
    simp only [stepMovedEntries, stepFn, List.getD, List.getElem?_map,
      List.getElem?_range hdst, Option.map_some, Option.getD_some]
    rfl
  rw [hget]
  refine ⟨fun j hj => hmono _ _ j hj, fun src bb hbb htgt j hj => ?_⟩
  have hsrc : src ∈ List.range bbs.length :=
    List.mem_range.mpr (List.getElem?_eq_some_iff.mp hbb).1
  exact hprop _ _ src bb hsrc hbb htgt j hj

/-- Any fixed point of `stepMovedEntries` satisfies outgoing-edge closure for
every in-range successor block `dst < bbs.length`. -/
theorem iterMovedEntries_fixed {bbs : List BasicBlockData} {entries : List (List Nat)}
    (hfix : stepMovedEntries bbs entries = entries) {src dst : Nat} {bb : BasicBlockData}
    (hbb : bbs[src]? = some bb) (hdst : dst < bbs.length)
    (htgt : dst ∈ termTargets bb.terminator) :
    ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator,
      j ∈ entries.getD dst [] := by
  intro j hj
  rw [← hfix]
  exact (stepMovedEntries_spec bbs entries dst hdst).2 src bb hbb htgt j hj

/-- `iterMovedEntries` is monotone at every in-range block index
`dst < bbs.length`. -/
theorem iterMovedEntries_mono (fuel : Nat) (bbs : List BasicBlockData)
    (entries : List (List Nat)) (dst : Nat) (hdst : dst < bbs.length) :
    ∀ j ∈ entries.getD dst [],
      j ∈ (iterMovedEntries fuel bbs entries).getD dst [] := by
  induction fuel generalizing entries with
  | zero => intro j hj; exact hj
  | succ n ih =>
    intro j hj
    simp only [iterMovedEntries]
    split
    · exact hj
    · exact ih (stepMovedEntries bbs entries) j
        ((stepMovedEntries_spec bbs entries dst hdst).1 j hj)

/-- Once `stepMovedEntries bbs entries = entries`, any further
`iterMovedEntries` fuel leaves `entries` unchanged. -/
theorem iterMovedEntries_eq_of_fixed (fuel : Nat) {bbs : List BasicBlockData}
    {entries : List (List Nat)}
    (hfix : stepMovedEntries bbs entries = entries) :
    iterMovedEntries fuel bbs entries = entries := by
  cases fuel with
  | zero => rfl
  | succ n => simp [iterMovedEntries, hfix]

/-- Every successor block target of a `terminatorOk` terminator is in range
(`< nblocks`). -/
theorem terminatorOk_targets_lt {decls : List LocalDecl} {nblocks : Nat}
    {t : MirAst.Terminator} (ht : terminatorOk decls nblocks t = true) :
    ∀ dst ∈ termTargets t, dst < nblocks := by
  intro dst hdst
  obtain ⟨kind, span⟩ := t
  match kind, ht, hdst with
  | .goto target, ht, hdst =>
    have ht' : target < nblocks := of_decide_eq_true ht
    have hdst' : dst = target := List.mem_singleton.mp hdst
    exact hdst' ▸ ht'
  | .switchInt discr targets, ht, hdst =>
    simp only [terminatorOk, termTargets, List.mem_cons, List.mem_map, Prod.exists] at ht hdst
    cases hit : switchIntType decls (copyOp discr) with
    | none => simp [hit] at ht
    | some it =>
      simp only [hit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Prod.forall] at ht
      obtain ⟨⟨⟨_, hbr⟩, _⟩, ho⟩ := ht
      rcases hdst with rfl | ⟨val, b, hmem, rfl⟩
      · exact ho
      · exact (hbr val b hmem).2
  | .unreachable, _, hdst => simp [termTargets] at hdst
  | .return_, _, hdst => simp [termTargets] at hdst
  | .unwindResume, ht, _ => simp [terminatorOk] at ht
  | .unwindTerminate, ht, _ => simp [terminatorOk] at ht
  | .drop _ _ _, ht, _ => simp [terminatorOk] at ht
  | .call _ _ _ _ _, ht, _ => simp [terminatorOk] at ht
  | .tailCall _ _, ht, _ => simp [terminatorOk] at ht
  | .assert _ _ _ _, ht, _ => simp [terminatorOk] at ht
  | .inlineAsm _ _ _, ht, _ => simp [terminatorOk] at ht

/-- When `iterMovedEntries` reaches a fixed point of `stepMovedEntries` at the
canonical fuel bound `N * (L + 1)` on a CFG whose terminators satisfy
`terminatorOk` and whose blocks satisfy `blockMovesOk`, `movesOk body = true`
follows automatically because outgoing-edge closure holds at every fixed
point. -/
theorem movesOk_of_fixed {body : CapturedMir}
    (hfix : stepMovedEntries body.basicBlocks
        (iterMovedEntries (body.basicBlocks.length * (body.localDecls.length + 1))
          body.basicBlocks []) =
      iterMovedEntries (body.basicBlocks.length * (body.localDecls.length + 1))
        body.basicBlocks [])
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true)
    (hblk : ∀ blk (bb : BasicBlockData), body.basicBlocks[blk]? = some bb →
      blockMovesOk (movedAtEntry body blk) bb.statements bb.terminator = true) :
    movesOk body = true := by
  simp only [movesOk, List.all_eq_true, List.mem_range]
  intro blk hlt
  obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[blk]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  simp only [hbb, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  refine ⟨hblk blk bb hbb, fun dst hdst j hj => ?_⟩
  have hmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
  have hdst_lt : dst < body.basicBlocks.length :=
    terminatorOk_targets_lt (hterm bb hmem) dst hdst
  exact iterMovedEntries_fixed hfix hbb hdst_lt hdst j hj

/-- Either `unionLocals acc xs = acc`, or some `j ∈ xs` was absent from `acc`
and is present in `unionLocals acc xs`. -/
theorem unionLocals_eq_or_mem_new (acc xs : List Nat) :
    unionLocals acc xs = acc ∨ ∃ j ∈ xs, j ∉ acc ∧ j ∈ unionLocals acc xs := by
  induction xs generalizing acc with
  | nil => exact .inl rfl
  | cons x xs ih =>
    simp only [unionLocals, List.foldl_cons] at ih ⊢
    by_cases hc : acc.contains x = true
    · simp only [hc, ↓reduceIte]
      rcases ih acc with heq | ⟨j, hjx, hnot, hin⟩
      · exact .inl heq
      · exact .inr ⟨j, List.mem_cons_of_mem x hjx, hnot, hin⟩
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hnot : x ∉ acc := fun hx => by
        rw [List.contains_iff_mem.mpr hx] at hc; cases hc
      have hin : x ∈ unionLocals (x :: acc) xs :=
        (unionLocals_mem (x :: acc) xs x).mpr (.inl (List.mem_cons.mpr (.inl rfl)))
      exact .inr ⟨x, List.mem_cons.mpr (.inl rfl), hnot, hin⟩

/-- When `entries.length = bbs.length`, one pass of `stepMovedEntries` either
reaches a fixed point or adds at least one new element `j` at some in-range
block `dst < bbs.length`. -/
theorem stepMovedEntries_eq_or_strict (bbs : List BasicBlockData)
    (entries : List (List Nat)) (hlen : entries.length = bbs.length) :
    stepMovedEntries bbs entries = entries ∨
      ∃ dst < bbs.length, ∃ j,
        j ∉ entries.getD dst [] ∧ j ∈ (stepMovedEntries bbs entries).getD dst [] := by
  by_cases heq : stepMovedEntries bbs entries = entries
  · exact .inl heq
  · right
    have hex : ∃ dst < bbs.length,
        (stepMovedEntries bbs entries).getD dst [] ≠ entries.getD dst [] := by
      by_cases hall : (List.range bbs.length).all
          (fun dst => decide ((stepMovedEntries bbs entries).getD dst [] =
            entries.getD dst [])) = true
      · exfalso; apply heq
        simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
        apply List.ext_getElem (by simp [stepMovedEntries, hlen])
        intro i h1 h2
        have hi : i < bbs.length := by simpa [stepMovedEntries] using h1
        have h := hall i hi
        simpa [List.getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using h
      · simp only [Bool.not_eq_true, List.all_eq_false, List.mem_range,
          Bool.not_eq_true, decide_eq_false_iff_not] at hall
        obtain ⟨dst, hdst, hne⟩ := hall
        exact ⟨dst, hdst, hne⟩
    obtain ⟨dst, hdst, hne_dst⟩ := hex
    let stepFn (acc : List Nat) (src : Nat) : List Nat :=
      match bbs[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          unionLocals acc
            (termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator)
        else acc
      | none => acc
    have hmono : ∀ (srcs : List Nat) (acc : List Nat) (j : Nat),
        j ∈ acc → j ∈ srcs.foldl stepFn acc := by
      intro srcs
      induction srcs with
      | nil => intro acc j hj; exact hj
      | cons s srcs ih =>
        intro acc j hj
        apply ih
        simp only [stepFn]
        cases bbs[s]? with
        | none => exact hj
        | some bb =>
          simp only
          split
          · exact (unionLocals_mem _ _ _).mpr (.inl hj)
          · exact hj
    have hfold : ∀ (srcs : List Nat) (acc : List Nat),
        srcs.foldl stepFn acc = acc ∨
          ∃ j, j ∉ acc ∧ j ∈ srcs.foldl stepFn acc := by
      intro srcs
      induction srcs with
      | nil => intro acc; exact .inl rfl
      | cons s srcs ih =>
        intro acc
        simp only [List.foldl_cons]
        have hone : stepFn acc s = acc ∨ ∃ j, j ∉ acc ∧ j ∈ stepFn acc s := by
          simp only [stepFn]
          cases bbs[s]? with
          | none => exact .inl rfl
          | some bb =>
            simp only
            split
            · rcases unionLocals_eq_or_mem_new acc _ with h1 | ⟨j, _, hnot, hin⟩
              · exact .inl h1
              · exact .inr ⟨j, hnot, hin⟩
            · exact .inl rfl
        rcases hone with hsame | ⟨j, hnot, hin⟩
        · rw [hsame]; exact ih acc
        · exact .inr ⟨j, hnot, hmono srcs (stepFn acc s) j hin⟩
    have hget : (stepMovedEntries bbs entries).getD dst [] =
        (List.range bbs.length).foldl stepFn (entries.getD dst []) := by
      simp only [stepMovedEntries, stepFn, List.getD, List.getElem?_map,
        List.getElem?_range hdst, Option.map_some, Option.getD_some]
      rfl
    rcases hfold (List.range bbs.length) (entries.getD dst []) with hsame | ⟨j, hnot, hin⟩
    · exact False.elim (hne_dst (hget.trans hsame))
    · exact ⟨dst, hdst, j, hnot, hget ▸ hin⟩

private def countMissing (m : List Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if m.contains x then 0 else 1) + countMissing m xs

private theorem countMissing_le (m u : List Nat) : countMissing m u ≤ u.length := by
  induction u with
  | nil => simp [countMissing]
  | cons x xs ih =>
    simp only [countMissing, List.length_cons]
    cases m.contains x <;> simp <;> omega

private theorem countMissing_mono {m m' : List Nat} (hsub : ∀ k ∈ m, k ∈ m')
    (u : List Nat) : countMissing m' u ≤ countMissing m u := by
  induction u with
  | nil => simp [countMissing]
  | cons x xs ih =>
    simp only [countMissing]
    by_cases hx : m.contains x = true
    · have hx' : m'.contains x = true :=
        List.contains_iff_mem.mpr (hsub x (List.contains_iff_mem.mp hx))
      rw [hx, hx']; simp; omega
    · simp only [Bool.not_eq_true] at hx
      rw [hx]; cases m'.contains x <;> simp <;> omega

private theorem countMissing_lt_of_new {m m' : List Nat} (hsub : ∀ k ∈ m, k ∈ m')
    {j : Nat} (hnot : j ∉ m) (hin : j ∈ m') {u : List Nat} (hju : j ∈ u) :
    countMissing m' u < countMissing m u := by
  induction u with
  | nil => simp at hju
  | cons x xs ih =>
    simp only [countMissing]
    rcases List.mem_cons.mp hju with rfl | hrest
    · have hc1 : m.contains j = false := by
        cases hc : m.contains j with
        | false => rfl
        | true => exact False.elim (hnot (List.contains_iff_mem.mp hc))
      have hc2 : m'.contains j = true := List.contains_iff_mem.mpr hin
      have hle := countMissing_mono hsub xs
      rw [hc1, hc2]; simp; omega
    · have hlt := ih hrest
      by_cases hx : m.contains x = true
      · have hx' : m'.contains x = true :=
          List.contains_iff_mem.mpr (hsub x (List.contains_iff_mem.mp hx))
        rw [hx, hx']; simp; omega
      · simp only [Bool.not_eq_true] at hx
        rw [hx]; cases m'.contains x <;> simp <;> omega

private def remCapAux (L : Nat) (entries : List (List Nat)) : List Nat → Nat
  | [] => 0
  | d :: ds => countMissing (entries.getD d []) (List.range L) + remCapAux L entries ds

private theorem remCapAux_le (L : Nat) (entries : List (List Nat)) (ds : List Nat) :
    remCapAux L entries ds ≤ ds.length * L := by
  induction ds with
  | nil => simp [remCapAux]
  | cons d ds ih =>
    simp only [remCapAux, List.length_cons, Nat.succ_mul]
    have hc : countMissing (entries.getD d []) (List.range L) ≤ L := by
      simpa using countMissing_le (entries.getD d []) (List.range L)
    omega

private theorem remCapAux_mono {L : Nat} {entries entries' : List (List Nat)}
    {ds : List Nat}
    (hmono : ∀ d ∈ ds, ∀ k ∈ entries.getD d [], k ∈ entries'.getD d []) :
    remCapAux L entries' ds ≤ remCapAux L entries ds := by
  induction ds with
  | nil => simp [remCapAux]
  | cons d ds ih =>
    simp only [remCapAux]
    have hd := countMissing_mono (hmono d (List.mem_cons.mpr (.inl rfl))) (List.range L)
    have hds := ih (fun d' hd' => hmono d' (List.mem_cons_of_mem d hd'))
    omega

private theorem remCapAux_lt {L : Nat} {entries entries' : List (List Nat)}
    {ds : List Nat}
    (hmono : ∀ d ∈ ds, ∀ k ∈ entries.getD d [], k ∈ entries'.getD d [])
    {dst : Nat} (hdst : dst ∈ ds) {j : Nat} (hjL : j < L)
    (hnot : j ∉ entries.getD dst []) (hin : j ∈ entries'.getD dst []) :
    remCapAux L entries' ds < remCapAux L entries ds := by
  induction ds with
  | nil => simp at hdst
  | cons d ds ih =>
    simp only [remCapAux]
    rcases List.mem_cons.mp hdst with rfl | hrest
    · have hd := countMissing_lt_of_new
        (hmono dst (List.mem_cons.mpr (.inl rfl))) hnot hin (List.mem_range.mpr hjL)
      have hds := remCapAux_mono (L := L)
        (fun d' hd' => hmono d' (List.mem_cons_of_mem dst hd'))
      omega
    · have hd := countMissing_mono (hmono d (List.mem_cons.mpr (.inl rfl))) (List.range L)
      have hds := ih (fun d' hd' => hmono d' (List.mem_cons_of_mem d hd')) hrest
      omega

private theorem stepMovedEntries_lt {L : Nat} {bbs : List BasicBlockData}
    (hbbs : ∀ bb ∈ bbs,
      (∀ s ∈ bb.statements, ∀ mo j, j ∈ stmtMoved mo s → j ∈ mo ∨ j < L) ∧
      (∀ mo j, j ∈ termMoved mo bb.terminator → j ∈ mo ∨ j < L))
    (entries : List (List Nat))
    (hent : ∀ src < bbs.length, ∀ j ∈ entries.getD src [], j < L) :
    ∀ dst < bbs.length, ∀ j ∈ (stepMovedEntries bbs entries).getD dst [], j < L := by
  have hfold_ss : ∀ (ss : List MirAst.Statement)
      (_ : ∀ s ∈ ss, ∀ mo j, j ∈ stmtMoved mo s → j ∈ mo ∨ j < L)
      (mo : List Nat) (_ : ∀ j ∈ mo, j < L) (j : Nat),
      j ∈ ss.foldl stmtMoved mo → j < L := by
    intro ss
    induction ss with
    | nil => intro _ mo hmo j hj; exact hmo j hj
    | cons s ss ih =>
      intro hss mo hmo j hj
      apply ih (fun s' hs' => hss s' (List.mem_cons_of_mem s hs')) (stmtMoved mo s) _ j hj
      intro k hk
      rcases hss s (List.mem_cons.mpr (.inl rfl)) mo k hk with h1 | h2
      · exact hmo k h1
      · exact h2
  intro dst hdst
  let stepFn (acc : List Nat) (src : Nat) : List Nat :=
    match bbs[src]? with
    | some bb =>
      if (termTargets bb.terminator).contains dst then
        unionLocals acc
          (termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator)
      else acc
    | none => acc
  have hsrcs : ∀ (srcs : List Nat) (_ : ∀ s ∈ srcs, s < bbs.length)
      (acc : List Nat) (_ : ∀ j ∈ acc, j < L) (j : Nat),
      j ∈ srcs.foldl stepFn acc → j < L := by
    intro srcs
    induction srcs with
    | nil => intro _ acc hacc j hj; exact hacc j hj
    | cons s srcs ih =>
      intro hlt acc hacc j hj
      apply ih (fun s' hs' => hlt s' (List.mem_cons_of_mem s hs')) (stepFn acc s) _ j hj
      intro k hk
      simp only [stepFn] at hk
      cases hbb : bbs[s]? with
      | none => simp [hbb] at hk; exact hacc k hk
      | some bb =>
        simp only [hbb] at hk
        split at hk
        · rcases (unionLocals_mem _ _ _).mp hk with h1 | h2
          · exact hacc k h1
          · obtain ⟨hbb_ss, hbb_tm⟩ := hbbs bb (List.mem_of_getElem? hbb)
            have hs_lt : s < bbs.length := hlt s (List.mem_cons.mpr (.inl rfl))
            rcases hbb_tm _ k h2 with h3 | h4
            · exact hfold_ss bb.statements hbb_ss (entries.getD s []) (hent s hs_lt) k h3
            · exact h4
        · exact hacc k hk
  have hget : (stepMovedEntries bbs entries).getD dst [] =
      (List.range bbs.length).foldl stepFn (entries.getD dst []) := by
    simp only [stepMovedEntries, stepFn, List.getD, List.getElem?_map,
      List.getElem?_range hdst, Option.map_some, Option.getD_some]
    rfl
  rw [hget]
  exact hsrcs (List.range bbs.length) (fun _ hs => List.mem_range.mp hs)
    (entries.getD dst []) (hent dst hdst)

private theorem iterMovedEntries_stabilizes_from {L : Nat} {bbs : List BasicBlockData}
    (hbbs : ∀ bb ∈ bbs,
      (∀ s ∈ bb.statements, ∀ mo j, j ∈ stmtMoved mo s → j ∈ mo ∨ j < L) ∧
      (∀ mo j, j ∈ termMoved mo bb.terminator → j ∈ mo ∨ j < L)) :
    ∀ (fuel : Nat) (entries : List (List Nat)),
      entries.length = bbs.length →
      (∀ src < bbs.length, ∀ j ∈ entries.getD src [], j < L) →
      remCapAux L entries (List.range bbs.length) ≤ fuel →
      stepMovedEntries bbs (iterMovedEntries fuel bbs entries) =
        iterMovedEntries fuel bbs entries := by
  intro fuel
  induction fuel with
  | zero =>
    intro entries hlen hent hcap
    rcases stepMovedEntries_eq_or_strict bbs entries hlen with hfix | ⟨dst, hdst, j, hnot, hin⟩
    · simpa [iterMovedEntries] using hfix
    · have hent' := stepMovedEntries_lt hbbs entries hent
      have hjL : j < L := hent' dst hdst j hin
      have hlt := remCapAux_lt (L := L)
        (fun d hd => (stepMovedEntries_spec bbs entries d (List.mem_range.mp hd)).1)
        (List.mem_range.mpr hdst) hjL hnot hin
      omega
  | succ n ih =>
    intro entries hlen hent hcap
    simp only [iterMovedEntries]
    by_cases hbeq : (stepMovedEntries bbs entries == entries) = true
    · simp only [hbeq, ↓reduceIte]
      exact beq_iff_eq.mp hbeq
    · simp only [Bool.not_eq_true] at hbeq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hne : stepMovedEntries bbs entries ≠ entries := fun h => by
        rw [beq_iff_eq.mpr h] at hbeq; cases hbeq
      rcases stepMovedEntries_eq_or_strict bbs entries hlen with hfix | ⟨dst, hdst, j, hnot, hin⟩
      · exact False.elim (hne hfix)
      · have hent' := stepMovedEntries_lt hbbs entries hent
        have hjL : j < L := hent' dst hdst j hin
        have hlt := remCapAux_lt (L := L)
          (fun d hd => (stepMovedEntries_spec bbs entries d (List.mem_range.mp hd)).1)
          (List.mem_range.mpr hdst) hjL hnot hin
        exact ih (stepMovedEntries bbs entries) (by simp [stepMovedEntries]) hent' (by omega)

/-- Unconditional finite-fuel convergence: when every moved-out local index of
`bbs` lies below `L`, `iterMovedEntries (bbs.length * (L + 1)) bbs []` always
reaches a fixed point of `stepMovedEntries bbs`. -/
theorem iterMovedEntries_stabilizes {L : Nat} {bbs : List BasicBlockData}
    (hbbs : ∀ bb ∈ bbs,
      (∀ s ∈ bb.statements, ∀ mo j, j ∈ stmtMoved mo s → j ∈ mo ∨ j < L) ∧
      (∀ mo j, j ∈ termMoved mo bb.terminator → j ∈ mo ∨ j < L)) :
    stepMovedEntries bbs (iterMovedEntries (bbs.length * (L + 1)) bbs []) =
      iterMovedEntries (bbs.length * (L + 1)) bbs [] := by
  cases hN : bbs.length with
  | zero =>
    have hnil : bbs = [] := List.eq_nil_of_length_eq_zero hN
    subst hnil
    simp [Nat.zero_mul, iterMovedEntries, stepMovedEntries]
  | succ k =>
    have hfuel : (k + 1) * (L + 1) = ((k + 1) * L + k) + 1 := by
      rw [Nat.mul_succ]
      omega
    rw [hfuel]
    simp only [iterMovedEntries]
    by_cases hbeq : (stepMovedEntries bbs [] == []) = true
    · simp only [hbeq, ↓reduceIte]
      exact beq_iff_eq.mp hbeq
    · simp only [Bool.not_eq_true] at hbeq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hent0 : ∀ src < bbs.length, ∀ j ∈ ([] : List (List Nat)).getD src [], j < L := by
        intro src _ j hj; simp [List.getD] at hj
      have hent1 := stepMovedEntries_lt hbbs [] hent0
      have hcap : remCapAux L (stepMovedEntries bbs []) (List.range bbs.length) ≤
          (k + 1) * L + k := by
        have hle := remCapAux_le L (stepMovedEntries bbs []) (List.range (k + 1))
        simp only [List.length_range] at hle
        rw [hN]
        omega
      exact iterMovedEntries_stabilizes_from hbbs ((k + 1) * L + k)
        (stepMovedEntries bbs []) (by simp [stepMovedEntries]) hent1 hcap

private theorem opMoved_eq_move {op : Operand} {j : Nat} (h : opMoved op = some j) :
    op = .move ⟨j, []⟩ := by
  cases op with
  | copy _ => simp [opMoved] at h
  | constant _ => simp [opMoved] at h
  | move p =>
    rcases p with ⟨k, proj⟩
    cases proj with
    | nil => simp [opMoved] at h; subst h; rfl
    | cons _ _ => simp [opMoved] at h

private theorem opMoved_lt_of_operandOk {decls : List LocalDecl} {it : Gen.IntType}
    {op : Operand} {j : Nat} (hop : opMoved op = some j)
    (hok : operandOk decls it (copyOp op) = true) : j < decls.length := by
  rw [opMoved_eq_move hop] at hok
  simp only [copyOp, operandOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1

private theorem opMoved_lt_of_operandOkB {decls : List LocalDecl}
    {op : Operand} {j : Nat} (hop : opMoved op = some j)
    (hok : operandOkB decls (copyOp op) = true) : j < decls.length := by
  rw [opMoved_eq_move hop] at hok
  simp only [copyOp, operandOkB, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1

private theorem opMoved_lt_of_operandOkO {decls : List LocalDecl}
    {op : Operand} {j : Nat} (hop : opMoved op = some j)
    (hok : operandOkO decls (copyOp op) = true) : j < decls.length := by
  rw [opMoved_eq_move hop] at hok
  simp only [copyOp, operandOkO, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1

private theorem opMoved_lt_of_operandOkTuple {decls : List LocalDecl} {it : Gen.IntType}
    {op : Operand} {j : Nat} (hop : opMoved op = some j)
    (hok : operandOkTuple decls it (copyOp op) = true) : j < decls.length := by
  rw [opMoved_eq_move hop] at hok
  simp only [copyOp, operandOkTuple, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1

private theorem opMoved_lt_of_relOperandsOk {decls : List LocalDecl} {a b : Operand}
    (hok : relOperandsOk decls (copyOp a) (copyOp b) = true) :
    (∀ j, opMoved a = some j → j < decls.length) ∧
    (∀ j, opMoved b = some j → j < decls.length) := by
  unfold relOperandsOk at hok
  split at hok
  · simp only [Bool.and_eq_true] at hok
    exact ⟨fun _ ha => opMoved_lt_of_operandOk ha hok.1,
      fun _ hb => opMoved_lt_of_operandOk hb hok.2⟩
  · simp only [Bool.and_eq_true] at hok
    exact ⟨fun _ ha => opMoved_lt_of_operandOkB ha hok.1,
      fun _ hb => opMoved_lt_of_operandOkB hb hok.2⟩
  · simp at hok

private theorem rvalue_filterMap_opMoved_lt {decls : List LocalDecl} {rv : Rvalue} {j : Nat}
    (hj : j ∈ (rvOperands rv).filterMap opMoved)
    (hok : (∃ it, rvalueOk decls it (copyRv rv) = true) ∨
      rvalueOkB decls (copyRv rv) = true ∨
      rvalueOkO decls (copyRv rv) = true ∨
      (∃ it, rvalueOkTuple decls it (copyRv rv) = true)) :
    j < decls.length := by
  obtain ⟨op, hop_mem, hop_mv⟩ := List.mem_filterMap.mp hj
  match rv, hop_mem, hok with
  | .use o, hop_mem, hok =>
    simp [rvOperands] at hop_mem; subst hop_mem
    rcases hok with ⟨it, h⟩ | h | h | ⟨it, h⟩
    · exact opMoved_lt_of_operandOk hop_mv (by simpa [copyRv, rvalueOk] using h)
    · exact opMoved_lt_of_operandOkB hop_mv (by simpa [copyRv, rvalueOkB] using h)
    · exact opMoved_lt_of_operandOkO hop_mv (by simpa [copyRv, rvalueOkO] using h)
    · exact opMoved_lt_of_operandOkTuple hop_mv (by simpa [copyRv, rvalueOkTuple] using h)
  | .unaryOp uop o, hop_mem, hok =>
    simp [rvOperands] at hop_mem; subst hop_mem
    rcases hok with ⟨it, h⟩ | h | h | ⟨it, h⟩
    · simp only [copyRv, rvalueOk, Bool.and_eq_true] at h
      exact opMoved_lt_of_operandOk hop_mv h.2
    · cases uop <;> simp only [copyRv, rvalueOkB] at h <;> try cases h
      exact opMoved_lt_of_operandOkB hop_mv h
    · simp [copyRv, rvalueOkO] at h
    · simp [copyRv, rvalueOkTuple] at h
  | .cast ck o ty, hop_mem, hok =>
    simp [rvOperands] at hop_mem; subst hop_mem
    rcases hok with ⟨it, h⟩ | h | h | ⟨it, h⟩
    · cases ck <;> simp only [copyRv, rvalueOk, Bool.and_eq_true] at h <;> try contradiction
      split at h
      · exact opMoved_lt_of_operandOk hop_mv h.2
      · exact opMoved_lt_of_operandOkB hop_mv h.2
    · simp [copyRv, rvalueOkB] at h
    · simp [copyRv, rvalueOkO] at h
    · simp [copyRv, rvalueOkTuple] at h
  | .binaryOp bop a b, hop_mem, hok =>
    simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false] at hop_mem
    rcases hok with ⟨it, h⟩ | h | h | ⟨it, h⟩
    · simp only [copyRv, rvalueOk] at h
      cases htb : translateBinOp bop with
      | none => simp [htb] at h
      | some iop =>
        simp only [htb, Bool.and_eq_true] at h
        rcases hop_mem with rfl | rfl
        · exact opMoved_lt_of_operandOk hop_mv h.1
        · split at h
          · split at h
            · exact opMoved_lt_of_operandOk hop_mv h.2
            · simp at h
          · exact opMoved_lt_of_operandOk hop_mv h.2
    · simp only [copyRv, rvalueOkB] at h
      split at h
      · obtain ⟨ha, hb⟩ := opMoved_lt_of_relOperandsOk h
        rcases hop_mem with rfl | rfl
        · exact ha j hop_mv
        · exact hb j hop_mv
      · simp only [Bool.and_eq_true] at h
        rcases hop_mem with rfl | rfl
        · exact opMoved_lt_of_operandOkB hop_mv h.1.2
        · exact opMoved_lt_of_operandOkB hop_mv h.2
    · cases bop <;> simp only [copyRv, rvalueOkO] at h <;> try cases h
      obtain ⟨ha, hb⟩ := opMoved_lt_of_relOperandsOk h
      rcases hop_mem with rfl | rfl
      · exact ha j hop_mv
      · exact hb j hop_mv
    · simp only [copyRv, rvalueOkTuple, Bool.and_eq_true] at h
      rcases hop_mem with rfl | rfl
      · exact opMoved_lt_of_operandOk hop_mv h.1.2
      · exact opMoved_lt_of_operandOk hop_mv h.2
  | .aggregate ak ops, hop_mem, hok =>
    rcases hok with ⟨it, h⟩ | h | h | ⟨it, h⟩
    · simp [copyRv, rvalueOk] at h
    · simp [copyRv, rvalueOkB] at h
    · simp [copyRv, rvalueOkO] at h
    · cases ak <;> try (simp [copyRv, rvalueOkTuple] at h)
      match ops, hop_mem, h with
      | [a, b], hop_mem, h =>
        simp only [List.map, Bool.and_eq_true] at h
        simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false] at hop_mem
        rcases hop_mem with rfl | rfl
        · exact opMoved_lt_of_operandOk hop_mv h.1
        · exact opMoved_lt_of_operandOkB hop_mv h.2
      | [], hop_mem, _ => simp [rvOperands] at hop_mem
      | [_], _, h => simp [List.map] at h
      | _ :: _ :: _ :: _, _, h => simp [List.map] at h
  | .copyForDeref _, hop_mem, _ | .repeat _ _, hop_mem, _ | .ref _ _, hop_mem, _
  | .rawPtr _ _, hop_mem, _ | .len _, hop_mem, _ | .discriminant _, hop_mem, _
  | .threadLocalRef _, hop_mem, _ | .nullaryOp _ _, hop_mem, _
  | .shallowInitBox _ _, hop_mem, _ | .wrapUnsafeBinder _ _, hop_mem, _ =>
    simp [rvOperands] at hop_mem

/-- Every local newly added to `mo` by `stmtMoved` on a `statementOk` statement
lies below `decls.length`. -/
theorem statementOk_stmtMoved_lt {decls : List LocalDecl} {s : MirAst.Statement}
    (hs : statementOk decls s = true) (mo : List Nat) (j : Nat)
    (hj : j ∈ stmtMoved mo s) : j ∈ mo ∨ j < decls.length := by
  obtain ⟨kind, span⟩ := s
  match kind, hs, hj with
  | .assign ⟨i, _ :: _⟩ _, hs, _ => simp [statementOk] at hs
  | .assign ⟨i, []⟩ rv, hs, hj =>
    simp only [stmtMoved] at hj
    have hj' : j ∈ (rvOperands rv).foldl moveOut mo := (List.mem_filter.mp hj).1
    rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj' with hmo | hmv
    · exact .inl hmo
    · right
      simp only [statementOk] at hs
      cases hd : decls[i]? with
      | none => simp [hd] at hs
      | some d =>
        simp only [hd] at hs
        split at hs
        · exact rvalue_filterMap_opMoved_lt hmv (.inr (.inl hs))
        · split at hs
          · exact rvalue_filterMap_opMoved_lt hmv (.inr (.inr (.inl hs)))
          · cases htup : intBoolTupleOf d.ty with
            | some it =>
              simp only [htup] at hs
              exact rvalue_filterMap_opMoved_lt hmv (.inr (.inr (.inr ⟨it, hs⟩)))
            | none =>
              simp only [htup] at hs
              cases hint : intTypeOf d.ty with
              | none => simp [hint] at hs
              | some it =>
                simp only [hint] at hs
                exact rvalue_filterMap_opMoved_lt hmv (.inl ⟨it, hs⟩)
  | .storageLive i, _, hj | .storageDead i, _, hj =>
    simp only [stmtMoved] at hj
    exact .inl (List.mem_filter.mp hj).1
  | .deinit ⟨i, []⟩, _, hj =>
    simp only [stmtMoved] at hj
    exact .inl (List.mem_filter.mp hj).1
  | .deinit ⟨_, _ :: _⟩, hs, _ => simp [statementOk] at hs
  | .placeMention _, _, hj | .setDiscriminant _ _, _, hj | .retag _ _, _, hj
  | .intrinsic _, _, hj | .coverage, _, hj | .constEvalCounter, _, hj
  | .backwardIncompatibleDropHint _, _, hj | .nop, _, hj =>
    simpa [stmtMoved] using .inl hj

/-- Every local newly added to `mo` by `termMoved` on a `terminatorOk`
terminator lies below `decls.length`. -/
theorem terminatorOk_termMoved_lt {decls : List LocalDecl} {nblocks : Nat}
    {t : MirAst.Terminator} (ht : terminatorOk decls nblocks t = true)
    (mo : List Nat) (j : Nat) (hj : j ∈ termMoved mo t) :
    j ∈ mo ∨ j < decls.length := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | switchInt discr targets =>
    simp only [termMoved, moveOut] at hj
    cases hmv : opMoved discr with
    | none => rw [hmv] at hj; exact .inl hj
    | some k =>
      simp only [hmv, List.mem_cons] at hj
      rcases hj with rfl | hmo
      · right
        simp only [terminatorOk] at ht
        cases hit : switchIntType decls (copyOp discr) with
        | none => simp [hit] at ht
        | some it =>
          simp only [hit, Bool.and_eq_true] at ht
          have hdok : discrOk decls (copyOp discr) = true := ht.1.1.1
          unfold discrOk at hdok
          split at hdok
          · exact opMoved_lt_of_operandOk hmv hdok
          · exact opMoved_lt_of_operandOkB hmv hdok
          · simp at hdok
      · exact .inl hmo
  | call _ _ _ _ _ => simp [terminatorOk] at ht
  | goto _ | unreachable | return_ | unwindResume | unwindTerminate | drop _ _ _
  | tailCall _ _ | assert _ _ _ _ | inlineAsm _ _ _ =>
    simpa [termMoved] using .inl hj

/-- On any CFG whose statements satisfy `statementOk` and whose terminators
satisfy `terminatorOk`, `iterMovedEntries` always stabilizes within
`N * (L + 1)` passes (`iterMovedEntries_stabilizes`), so `movesOk body = true`
holds if and only if every block satisfies `blockMovesOk` at
`movedAtEntry body blk` (outgoing-edge closure is automatic). -/
theorem movesOk_iff_blockMovesOk {body : CapturedMir}
    (hst : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      statementOk body.localDecls s = true)
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true) :
    movesOk body = true ↔
      ∀ blk (bb : BasicBlockData), body.basicBlocks[blk]? = some bb →
        blockMovesOk (movedAtEntry body blk) bb.statements bb.terminator = true := by
  constructor
  · intro hmv blk bb hbb
    have hlt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
    simp only [movesOk, List.all_eq_true, List.mem_range] at hmv
    have h := hmv blk hlt
    simp only [hbb, Bool.and_eq_true] at h
    exact h.1
  · intro hblk
    apply movesOk_of_fixed ?_ hterm hblk
    exact iterMovedEntries_stabilizes fun bb hbb =>
      ⟨fun s hs => statementOk_stmtMoved_lt (hst bb hbb s hs),
       terminatorOk_termMoved_lt (hterm bb hbb)⟩

/-- `stmtMoved` is monotone with respect to membership in `mo`. -/
theorem stmtMoved_mono {mo mo' : List Nat} (hsub : ∀ k ∈ mo, k ∈ mo')
    (s : MirAst.Statement) {j : Nat} (hj : j ∈ stmtMoved mo s) :
    j ∈ stmtMoved mo' s := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign p rv =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil =>
      simp only [stmtMoved, List.mem_filter] at hj ⊢
      refine ⟨(foldl_moveOut_mem (rvOperands rv) mo' j).mpr ?_, hj.2⟩
      rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj.1 with hmo | hmv
      · exact .inl (hsub j hmo)
      · exact .inr hmv
    | cons _ _ =>
      simp only [stmtMoved] at hj ⊢
      apply (foldl_moveOut_mem (rvOperands rv) mo' j).mpr
      rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj with hmo | hmv
      · exact .inl (hsub j hmo)
      · exact .inr hmv
  | storageLive i | storageDead i =>
    simp only [stmtMoved, List.mem_filter] at hj ⊢
    exact ⟨hsub j hj.1, hj.2⟩
  | deinit p =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil =>
      simp only [stmtMoved, List.mem_filter] at hj ⊢
      exact ⟨hsub j hj.1, hj.2⟩
    | cons _ _ =>
      simp only [stmtMoved] at hj ⊢
      exact hsub j hj
  | placeMention _ | setDiscriminant _ _ | retag _ _ | intrinsic _
  | coverage | constEvalCounter | backwardIncompatibleDropHint _ | nop =>
    simp only [stmtMoved] at hj ⊢
    exact hsub j hj

/-- `termMoved` is monotone with respect to membership in `mo`. -/
theorem termMoved_mono {mo mo' : List Nat} (hsub : ∀ k ∈ mo, k ∈ mo')
    (t : MirAst.Terminator) {j : Nat} (hj : j ∈ termMoved mo t) :
    j ∈ termMoved mo' t := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | switchInt discr _ =>
    simp only [termMoved, moveOut] at hj ⊢
    cases hmv : opMoved discr with
    | none =>
      simp only [hmv] at hj ⊢
      exact hsub j hj
    | some k =>
      simp only [hmv, List.mem_cons] at hj ⊢
      rcases hj with rfl | hmo
      · exact .inl rfl
      · exact .inr (hsub j hmo)
  | call _ _ dst target _ =>
    cases target with
    | none =>
      simp only [termMoved] at hj ⊢
      exact hsub j hj
    | some _ =>
      obtain ⟨i, proj⟩ := dst
      cases proj with
      | nil =>
        simp only [termMoved, List.mem_filter] at hj ⊢
        exact ⟨hsub j hj.1, hj.2⟩
      | cons _ _ =>
        simp only [termMoved] at hj ⊢
        exact hsub j hj
  | goto _ | unreachable | return_ | unwindResume | unwindTerminate | drop _ _ _
  | tailCall _ _ | assert _ _ _ _ | inlineAsm _ _ _ =>
    simp only [termMoved] at hj ⊢
    exact hsub j hj

/-- One pass of `stepMovedEntries` preserves containment inside any pre-fixed
point `entries'` of the CFG outgoing-edge constraints. -/
theorem stepMovedEntries_least {bbs : List BasicBlockData}
    {entries entries' : List (List Nat)}
    (hsub : ∀ blk < bbs.length, ∀ j ∈ entries.getD blk [], j ∈ entries'.getD blk [])
    (hpre : ∀ src dst (bb : BasicBlockData),
      bbs[src]? = some bb → dst < bbs.length → dst ∈ termTargets bb.terminator →
      ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries'.getD src [])) bb.terminator,
        j ∈ entries'.getD dst []) :
    ∀ dst < bbs.length,
      ∀ j ∈ (stepMovedEntries bbs entries).getD dst [], j ∈ entries'.getD dst [] := by
  have hfold_ss : ∀ (ss : List MirAst.Statement) {mo mo' : List Nat},
      (∀ k ∈ mo, k ∈ mo') →
      ∀ k ∈ ss.foldl stmtMoved mo, k ∈ ss.foldl stmtMoved mo' := by
    intro ss
    induction ss with
    | nil => intro _ _ h k hk; exact h k hk
    | cons s ss ih =>
      intro _ _ h k hk
      exact ih (fun _ hm => stmtMoved_mono h s hm) k hk
  intro dst hdst
  let stepFn (acc : List Nat) (src : Nat) : List Nat :=
    match bbs[src]? with
    | some bb =>
      if (termTargets bb.terminator).contains dst then
        unionLocals acc
          (termMoved (bb.statements.foldl stmtMoved (entries.getD src [])) bb.terminator)
      else acc
    | none => acc
  have hsrcs : ∀ (srcs : List Nat) (acc : List Nat),
      (∀ j ∈ acc, j ∈ entries'.getD dst []) →
      ∀ j ∈ srcs.foldl stepFn acc, j ∈ entries'.getD dst [] := by
    intro srcs
    induction srcs with
    | nil => intro acc hacc j hj; exact hacc j hj
    | cons s srcs ih =>
      intro acc hacc j hj
      apply ih (stepFn acc s) _ j hj
      intro k hk
      simp only [stepFn] at hk
      cases hbb : bbs[s]? with
      | none => simp [hbb] at hk; exact hacc k hk
      | some bb =>
        simp only [hbb] at hk
        by_cases hcont : (termTargets bb.terminator).contains dst = true
        · simp only [hcont, ↓reduceIte] at hk
          rcases (unionLocals_mem _ _ _).mp hk with h1 | h2
          · exact hacc k h1
          · have hs_lt : s < bbs.length := (List.getElem?_eq_some_iff.mp hbb).1
            have htgt : dst ∈ termTargets bb.terminator := List.contains_iff_mem.mp hcont
            have htm : k ∈ termMoved
                (bb.statements.foldl stmtMoved (entries'.getD s [])) bb.terminator :=
              termMoved_mono (hfold_ss bb.statements (hsub s hs_lt)) bb.terminator h2
            exact hpre s dst bb hbb hdst htgt k htm
        · simp only [Bool.not_eq_true] at hcont
          simp only [hcont, Bool.false_eq_true, ↓reduceIte] at hk
          exact hacc k hk
  have hget : (stepMovedEntries bbs entries).getD dst [] =
      (List.range bbs.length).foldl stepFn (entries.getD dst []) := by
    simp only [stepMovedEntries, stepFn, List.getD, List.getElem?_map,
      List.getElem?_range hdst, Option.map_some, Option.getD_some]
    rfl
  rw [hget]
  exact hsrcs (List.range bbs.length) (entries.getD dst []) (hsub dst hdst)

/-- For any `fuel`, `iterMovedEntries fuel bbs []` is contained in every
pre-fixed point `entries'` of the CFG outgoing-edge constraints. -/
theorem iterMovedEntries_least (fuel : Nat) (bbs : List BasicBlockData)
    (entries' : List (List Nat))
    (hpre : ∀ src dst (bb : BasicBlockData),
      bbs[src]? = some bb → dst < bbs.length → dst ∈ termTargets bb.terminator →
      ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries'.getD src [])) bb.terminator,
        j ∈ entries'.getD dst []) :
    ∀ dst < bbs.length,
      ∀ j ∈ (iterMovedEntries fuel bbs []).getD dst [], j ∈ entries'.getD dst [] := by
  have haux : ∀ (n : Nat) (entries : List (List Nat)),
      (∀ blk < bbs.length, ∀ j ∈ entries.getD blk [], j ∈ entries'.getD blk []) →
      ∀ dst < bbs.length,
        ∀ j ∈ (iterMovedEntries n bbs entries).getD dst [], j ∈ entries'.getD dst [] := by
    intro n
    induction n with
    | zero => intro entries hsub dst hdst; exact hsub dst hdst
    | succ m ih =>
      intro entries hsub dst hdst j hj
      simp only [iterMovedEntries] at hj
      split at hj
      · exact hsub dst hdst j hj
      · exact ih (stepMovedEntries bbs entries)
          (stepMovedEntries_least hsub hpre) dst hdst j hj
  exact haux fuel [] (fun blk _ j hj => by simp [List.getD] at hj)

/-- Least fixed-point optimality of `movedAtEntry`: for any pre-fixed point
`entries'` of `body`'s forward move-tracking equations, `movedAtEntry body dst`
is a subset of `entries'.getD dst []` at every block
`dst < body.basicBlocks.length`. -/
theorem movedAtEntry_least {body : CapturedMir} {entries' : List (List Nat)}
    (hpre : ∀ src dst (bb : BasicBlockData),
      body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
      dst ∈ termTargets bb.terminator →
      ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries'.getD src [])) bb.terminator,
        j ∈ entries'.getD dst [])
    {dst : Nat} (hdst : dst < body.basicBlocks.length) :
    ∀ j ∈ movedAtEntry body dst, j ∈ entries'.getD dst [] :=
  iterMovedEntries_least
    (body.basicBlocks.length * (body.localDecls.length + 1))
    body.basicBlocks entries' hpre dst hdst

theorem movedBefore_zero (body : CapturedMir) (blk : Nat) :
    movedBefore body blk 0 = movedAtEntry body blk := by
  unfold movedBefore
  split <;> simp

theorem movedBefore_succ {body : CapturedMir} {blk k : Nat} {bb : BasicBlockData}
    {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[k]? = some st) :
    movedBefore body blk (k + 1) = stmtMoved (movedBefore body blk k) st := by
  simp only [movedBefore, hbb]
  rw [List.take_add_one, List.foldl_append, hst]
  rfl

theorem blockMovesOk_spec (mo : List Nat) (ss : List MirAst.Statement) (t : MirAst.Terminator)
    (h : blockMovesOk mo ss t = true) :
    (∀ (k : Nat) st, ss[k]? = some st → stmtReadsOk ((ss.take k).foldl stmtMoved mo) st = true) ∧
    termReadsOk (ss.foldl stmtMoved mo) t = true := by
  induction ss generalizing mo with
  | nil => exact ⟨fun k st h => by simp at h, by simpa [blockMovesOk] using h⟩
  | cons s ss ih =>
    simp only [blockMovesOk, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := ih (stmtMoved mo s) h.2
    refine ⟨fun k st hk => ?_, by simpa using ih2⟩
    cases k with
    | zero => simp at hk; subst hk; simpa using h.1
    | succ k => simpa using ih1 k st (by simpa using hk)

/-- What `movesOk` guarantees at a statement, at a terminator, and across each
outgoing control-flow edge `(blk → t)`. -/
theorem movesOk_spec {body : CapturedMir} (h : movesOk body = true) {blk : Nat}
    {bb : BasicBlockData} (hbb : body.basicBlocks[blk]? = some bb) :
    (∀ (k : Nat) st, bb.statements[k]? = some st →
      stmtReadsOk (movedBefore body blk k) st = true) ∧
    termReadsOk (movedBefore body blk bb.statements.length) bb.terminator = true ∧
    (∀ t ∈ termTargets bb.terminator,
      ∀ j ∈ termMoved (movedBefore body blk bb.statements.length) bb.terminator,
        j ∈ movedBefore body t 0) := by
  have hlt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  simp only [movesOk, List.all_eq_true, List.mem_range] at h
  have hblk := h blk hlt
  simp only [hbb, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hblk
  obtain ⟨h1, h2⟩ := blockMovesOk_spec _ _ _ hblk.1
  have h3 := hblk.2
  refine ⟨fun k st hk => ?_, ?_, fun t ht j hj => ?_⟩
  · simpa [movedBefore, hbb] using h1 k st hk
  · simpa [movedBefore, hbb] using h2
  · rw [movedBefore_zero]
    exact h3 t ht j (by simpa [movedBefore, hbb] using hj)

theorem readsOk_mono {mo mo' : List Nat} (hsub : ∀ j ∈ mo', j ∈ mo) {ops : List Operand}
    (h : readsOk mo ops = true) : readsOk mo' ops = true := by
  induction ops generalizing mo mo' with
  | nil => rfl
  | cons op ops ih =>
    simp only [readsOk, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨hs, hr⟩, hrest⟩ := h
    refine ⟨⟨hs, ?_⟩, ih ?_ hrest⟩
    · cases hop : opRead op with
      | none => simp
      | some j =>
        simp [hop] at hr ⊢
        exact fun hj => hr (hsub j hj)
    · intro j hj
      unfold moveOut at hj ⊢
      cases hm : opMoved op with
      | none => simp only [hm] at hj ⊢; exact hsub j hj
      | some k =>
        simp only [hm, List.mem_cons] at hj ⊢
        rcases hj with hj | hj
        · exact .inl hj
        · exact .inr (hsub j hj)

/-- `stmtReadsOk` is antitone in the moved-out set `mo`. -/
theorem stmtReadsOk_antitone {mo mo' : List Nat} (hsub : ∀ j ∈ mo, j ∈ mo')
    {s : MirAst.Statement} (h : stmtReadsOk mo' s = true) :
    stmtReadsOk mo s = true := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign _ rv => exact readsOk_mono hsub h
  | placeMention _ | storageLive _ | storageDead _ | deinit _
  | setDiscriminant _ _ | retag _ _ | intrinsic _ | coverage
  | constEvalCounter | backwardIncompatibleDropHint _ | nop => rfl

/-- `termReadsOk` is antitone in the moved-out set `mo`. -/
theorem termReadsOk_antitone {mo mo' : List Nat} (hsub : ∀ j ∈ mo, j ∈ mo')
    {t : MirAst.Terminator} (h : termReadsOk mo' t = true) :
    termReadsOk mo t = true := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | switchInt discr _ => exact readsOk_mono hsub h
  | return_ =>
    simp [termReadsOk] at h ⊢
    exact fun h0 => h (hsub 0 h0)
  | call _ argOps dst _ _ =>
    obtain ⟨i, proj⟩ := dst
    have hsub' : ∀ j ∈ i :: mo, j ∈ i :: mo' := by
      intro j hj
      simp only [List.mem_cons] at hj ⊢
      rcases hj with rfl | hmo
      · exact .inl rfl
      · exact .inr (hsub j hmo)
    cases proj with
    | nil => exact readsOk_mono hsub' h
    | cons _ _ =>
      simp only [termReadsOk, Bool.and_eq_true] at h ⊢
      refine ⟨?_, readsOk_mono hsub' h.2⟩
      simp at h ⊢
      exact fun hi => h.1 (hsub i hi)
  | goto _ | unreachable | unwindResume | unwindTerminate | drop _ _ _
  | tailCall _ _ | assert _ _ _ _ | inlineAsm _ _ _ => rfl

/-- `blockMovesOk` is antitone in the moved-out set `mo`: shrinking the
incoming moved-out set preserves intra-block move safety. -/
theorem blockMovesOk_antitone {mo mo' : List Nat} (hsub : ∀ j ∈ mo, j ∈ mo')
    {ss : List MirAst.Statement} {t : MirAst.Terminator}
    (h : blockMovesOk mo' ss t = true) :
    blockMovesOk mo ss t = true := by
  induction ss generalizing mo mo' with
  | nil => exact termReadsOk_antitone hsub h
  | cons s ss ih =>
    simp only [blockMovesOk, Bool.and_eq_true] at h ⊢
    exact ⟨stmtReadsOk_antitone hsub h.1,
      ih (fun _ hk => stmtMoved_mono hsub s hk) h.2⟩

/-- **Park induction for `movesOk`.** Any inductive pre-fixed point `entries'`
of `body`'s forward move-propagation equations whose per-block entry sets
satisfy `blockMovesOk` witnesses `movesOk body = true` on a well-typed CFG,
since `movedAtEntry` is bounded above by `entries'` (`movedAtEntry_least`) and
`blockMovesOk` is antitone (`blockMovesOk_antitone`). -/
theorem movesOk_of_preFixedPoint {body : CapturedMir}
    (hst : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      statementOk body.localDecls s = true)
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true)
    (entries' : List (List Nat))
    (hpre : ∀ src dst (bb : BasicBlockData),
      body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
      dst ∈ termTargets bb.terminator →
      ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries'.getD src [])) bb.terminator,
        j ∈ entries'.getD dst [])
    (hblk : ∀ blk (bb : BasicBlockData), body.basicBlocks[blk]? = some bb →
      blockMovesOk (entries'.getD blk []) bb.statements bb.terminator = true) :
    movesOk body = true := by
  refine (movesOk_iff_blockMovesOk hst hterm).mpr fun blk bb hbb => ?_
  have hlt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  exact blockMovesOk_antitone (movedAtEntry_least hpre hlt) (hblk blk bb hbb)

/-- **Knaster–Tarski characterization of `movesOk`.** On a well-typed CFG,
`movesOk body = true` holds if and only if there exists an inductive pre-fixed
point `entries'` of the CFG move-propagation equations at which every block
satisfies `blockMovesOk`. -/
theorem movesOk_iff_exists_preFixedPoint {body : CapturedMir}
    (hst : ∀ bb ∈ body.basicBlocks, ∀ s ∈ bb.statements,
      statementOk body.localDecls s = true)
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true) :
    movesOk body = true ↔
      ∃ entries' : List (List Nat),
        (∀ src dst (bb : BasicBlockData),
          body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
          dst ∈ termTargets bb.terminator →
          ∀ j ∈ termMoved (bb.statements.foldl stmtMoved (entries'.getD src [])) bb.terminator,
            j ∈ entries'.getD dst []) ∧
        (∀ blk (bb : BasicBlockData), body.basicBlocks[blk]? = some bb →
          blockMovesOk (entries'.getD blk []) bb.statements bb.terminator = true) := by
  constructor
  · intro hmv
    refine ⟨iterMovedEntries
      (body.basicBlocks.length * (body.localDecls.length + 1)) body.basicBlocks [],
      fun src dst bb hbb _ htgt j hj => ?_,
      fun blk bb hbb => (movesOk_iff_blockMovesOk hst hterm).mp hmv blk bb hbb⟩
    have h3 := (movesOk_spec hmv hbb).2.2 dst htgt j
      (by simpa [movedBefore, hbb, List.take_length, movedAtEntry] using hj)
    simpa [movedBefore_zero, movedAtEntry] using h3
  · rintro ⟨entries', hpre, hblk⟩
    exact movesOk_of_preFixedPoint hst hterm entries' hpre hblk

/-- `opsPost` changes only the locals that `ops` move out of, to `.uninit`,
and never a dead slot. -/
theorem opsPost_get (L : List LocalSlot) (ops : List Operand) (k : Nat) :
    (opsPost L ops)[k]? = L[k]? ∨
      (k ∈ ops.filterMap opMoved ∧ (opsPost L ops)[k]? = some .uninit ∧ L[k]? ≠ some .dead) := by
  induction ops generalizing L with
  | nil => exact .inl rfl
  | cons op ops ih =>
    simp only [opsPost, List.foldl_cons] at ih ⊢
    rcases ih (opPost L op) with h | ⟨h1, h2, h3⟩
    · rcases opPost_get L op k with h' | ⟨hm, h1', s, h2', h3'⟩
      · exact .inl (h.trans h')
      · refine .inr ⟨?_, h.trans h1', by rw [h2']; simpa using h3'⟩
        rw [List.filterMap_cons_some hm]; simp
    · refine .inr ⟨?_, h2, fun hd => h3 ((opPost_dead L op k).mpr hd)⟩
      cases hm : opMoved op with
      | none => rw [List.filterMap_cons_none hm]; exact h1
      | some j => rw [List.filterMap_cons_some hm]; exact List.mem_cons_of_mem _ h1

/-! ## Stale slots -/

theorem StaleOk.agree {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    (h : StaleOk body actual view blk stmt) {j : Nat} (hj : j ∉ movedBefore body blk stmt) :
    actual[j]? = view[j]? :=
  Classical.byContradiction fun hne => hj (h.2 j hne).1

theorem StaleOk.dead_iff {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    (h : StaleOk body actual view blk stmt) (j : Nat) :
    actual[j]? = some .dead ↔ view[j]? = some .dead := by
  by_cases heq : actual[j]? = view[j]?
  · rw [heq]
  · obtain ⟨_, ha, hv⟩ := h.2 j heq
    rw [ha]
    simp [hv]

theorem StaleOk.slots {decls : List LocalDecl} {body : CapturedMir} {actual view : List LocalSlot}
    {blk stmt : Nat} (h : StaleOk body actual view blk stmt)
    (hv : ∀ (i : Nat) d slot, decls[i]? = some d → view[i]? = some slot → SlotOk (tyOf d) slot) :
    SlotsOk decls actual := by
  intro i d slot hd hs
  by_cases heq : actual[i]? = view[i]?
  · rw [heq] at hs; exact hv i d slot hd hs
  · obtain ⟨_, ha, _⟩ := h.2 i heq; rw [ha] at hs; cases hs; trivial

theorem StaleOk.readsAgree {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    (h : StaleOk body actual view blk stmt) {ops : List Operand}
    (hr : readsOk (movedBefore body blk stmt) ops = true) : ReadsAgree actual view ops :=
  fun op hop j hj => h.agree ((readsOk_spec hr op hop).2 j hj)

/-- `StaleOk` at the entry of a successor block `t` when every local moved out
before `(blk, stmt)` is in `movedBefore body t 0`. -/
theorem StaleOk.toBlock {body : CapturedMir} {actual view : List LocalSlot} {blk stmt t : Nat}
    (hsub : ∀ j ∈ movedBefore body blk stmt, j ∈ movedBefore body t 0)
    (h : StaleOk body actual view blk stmt) : StaleOk body actual view t 0 := by
  refine ⟨h.1, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 j hj
  exact ⟨hsub j h1, h2, h3⟩

/-- `StaleOk` at the entry of a successor block `t` after Anneal read the
`switchInt` discriminant `op`, which may move out of a local. -/
theorem StaleOk.toBlockMove {body : CapturedMir} {actual view : List LocalSlot} {blk stmt t : Nat}
    (op : Operand) (hsub : ∀ j ∈ moveOut (movedBefore body blk stmt) op, j ∈ movedBefore body t 0)
    (h : StaleOk body actual view blk stmt) :
    StaleOk body (opPost actual op) view t 0 := by
  refine ⟨by rw [opPost_length]; exact h.1, fun j hj => ?_⟩
  rcases opPost_get actual op j with h' | ⟨hm, h1, s, h2, h3⟩
  · rw [h'] at hj ⊢
    obtain ⟨hmo, ha, hv⟩ := h.2 j hj
    exact ⟨hsub j (by unfold moveOut; split <;> simp [hmo]), ha, hv⟩
  · refine ⟨hsub j (by simp [moveOut, hm]), h1, fun hv => h3 ?_⟩
    have := (h.dead_iff j).mpr hv
    rw [h2] at this
    exact Option.some.inj this

/-- `StaleOk` after an assignment to `_i`, from which Anneal's `move`s
de-initialize the locals the rvalue moves out of. -/
theorem StaleOk.assign {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st) {i : Nat} {rv : Rvalue}
    (hk : st.kind = .assign ⟨i, []⟩ rv) (h : StaleOk body actual view blk stmt) (x : LocalSlot) :
    StaleOk body ((rvPost actual rv).set i x) (view.set i x) blk (stmt + 1) := by
  unfold StaleOk
  rw [movedBefore_succ hbb hst]
  refine ⟨by simp [rvPost_length, h.1], fun j hj => ?_⟩
  simp only [stmtMoved, hk]
  have hji : j ≠ i := by
    intro hji
    subst hji
    apply hj
    rw [List.getElem?_set, List.getElem?_set, rvPost_length, h.1]
    simp
  rw [List.getElem?_set_ne (Ne.symm hji), List.getElem?_set_ne (Ne.symm hji)] at hj ⊢
  rcases opsPost_get actual (rvOperands rv) j with h' | ⟨hm, h1, h2⟩
  · simp only [rvPost] at hj ⊢
    rw [h'] at hj ⊢
    obtain ⟨hmo, ha, hv⟩ := h.2 j hj
    exact ⟨List.mem_filter.mpr ⟨(foldl_moveOut_mem _ _ _).mpr (.inl hmo), by simp [hji]⟩, ha, hv⟩
  · refine ⟨List.mem_filter.mpr ⟨(foldl_moveOut_mem _ _ _).mpr (.inr hm), by simp [hji]⟩, h1,
      fun hv => h2 ((h.dead_iff j).mpr hv)⟩

/-- `StaleOk` after `StorageLive(_i)`, `StorageDead(_i)`, or `Deinit(_i)`,
which set `_i` alike in both models. -/
theorem StaleOk.setBoth {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st) {i : Nat}
    (hmo : stmtMoved (movedBefore body blk stmt) st = (movedBefore body blk stmt).filter (· != i))
    (h : StaleOk body actual view blk stmt) (x : LocalSlot) :
    StaleOk body (actual.set i x) (view.set i x) blk (stmt + 1) := by
  unfold StaleOk
  rw [movedBefore_succ hbb hst, hmo]
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  have hji : j ≠ i := by
    intro hji
    subst hji
    apply hj
    rw [List.getElem?_set, List.getElem?_set, h.1]
    simp
  rw [List.getElem?_set_ne (Ne.symm hji), List.getElem?_set_ne (Ne.symm hji)] at hj ⊢
  obtain ⟨hm, ha, hv⟩ := h.2 j hj
  exact ⟨List.mem_filter.mpr ⟨hm, by simp [hji]⟩, ha, hv⟩

/-- `StaleOk` after a `PlaceMention`, which changes nothing. -/
theorem StaleOk.keep {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st)
    (hmo : stmtMoved (movedBefore body blk stmt) st = movedBefore body blk stmt)
    (h : StaleOk body actual view blk stmt) : StaleOk body actual view blk (stmt + 1) := by
  unfold StaleOk at h ⊢
  rw [movedBefore_succ hbb hst, hmo]
  exact h

/-! ## One MiniRust step on a related machine -/

/-- The machine after `reset_data_race_tracking` and the (unique) thread pick. -/
def resetPick (m : Mach) : Mach := { m with mem := { m.mem with accesses := [] }, active_thread := 0 }

theorem resetPick_shape {m : Mach} {ctx : Ctx} {frames : List Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx frames allocs) : Shape (resetPick m) ctx frames allocs :=
  ⟨h.threads, rfl, h.allocs⟩

theorem step_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {lm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] allocs) (tb : Gen.BasicBlock)
    (htb : mapGet f.blocks (bbName blk) = some tb) :
    Interp.step m = (do
      let m' ← if (stmt : Int) = (tb.statements.length : Int) then
          evalTerminator (resetPick m) tb.terminator
        else do
          let st ← listIndex tb.statements (stmt : Int) "block.statements[frame.next_stmt]"
          let m' ← evalStatement (resetPick m) st
          mutateCurFrame m' (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
      CM.check_data_races m'.mem m'.active_thread (setInsert m.synchronized_threads 0, m.mem.accesses)
      pure m') := by
  have hany : m.threads.any (fun t => decide (t.state = .Enabled)) = true := by
    simp [h.threads, thread1]
  have hpick : ∀ mm : Mach, mm.threads = m.threads → pickActiveThread mm = .ok 0 :=
    fun mm hmm => pick_eq (hmm.trans h.threads)
  have hcur : ∀ mm : Mach, mm.threads = m.threads → mm.active_thread = 0 →
      curFrame mm = .ok (calleeFrameL f ctx lm blk stmt) :=
    fun mm hmm hact => curFrame_eq ⟨hmm.trans h.threads, hact, rfl⟩
  simp only [Interp.step, hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTracking,
    h.active]
  rw [hpick { m with mem := { memory := m.mem.memory, accesses := [] }, active_thread := 0 } rfl]
  simp only [ok_bind]
  rw [hcur { m with mem := { memory := m.mem.memory, accesses := [] }, active_thread := 0 } rfl rfl]
  simp only [ok_bind, mapIndex, calleeFrameL, htb]
  rfl

/-- `ConcurrentMemory::check_data_races` passes after any step that leaves
thread `0` active: the previous step's synchronized set always contains the
previously active thread, here also thread `0`. -/
theorem check_after {m m' : Mach} {ctx : Ctx} {frames : List Frame} {allocs : List Gen.Allocation}
    (h' : Shape m' ctx frames allocs) :
    CM.check_data_races m'.mem m'.active_thread (setInsert m.synchronized_threads 0, m.mem.accesses) =
      .ok () := by
  rw [h'.active]; exact check_ok _ _ _

/-! ## `Return` -/

theorem mutateCurFrame_single {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [fr] allocs) (g : Frame → Frame) :
    ∃ m', mutateCurFrame m g = .ok m' ∧ Shape m' ctx [g fr] allocs := by
  refine ⟨{ m with threads := [thread1 ctx [g fr]] }, ?_, ⟨rfl, h.active, h.allocs⟩⟩
  simp [mutateCurFrame, activeThread, listIndex, h.threads, h.active, thread1, listSet]

/-- `Terminator::Return` from the callee: load `_0` (UB if uninitialized),
deallocate every local in the locals map, store the value into the caller's
return place, and continue the caller at `nextBlock`. -/
theorem evalReturn_frame {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (d : LocalDecl)
    (hd : body.localDecls[0]? = some d) (r : Nat) (a : Gen.Allocation)
    (hp : ctx.retPtr.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a)
    (hlive : a.live = true) (haddrr : a.addr = ctx.retPtr.addr)
    (hlenr : a.data.length = tyBytes (tyOf d))
    (halr : ctx.retPtr.addr % ((itOf d).size.bytes : Int) = 0) :
    (∀ v, locals[0]? = some (.init v) →
      ∃ m' R, evalReturn m = .ok m' ∧
        Shape m' ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]
          (ctx.base.set r { a with data := declSlotData d (.init v) } ++ R) ∧
        ∀ b ∈ R, b.live = false) ∧
    (locals[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  have hT := h.decl_localTy 0 d hd
  have hdScalar := h.decl_scalar 0 d hd
  have hloc0 := (h.hf.2 0 d hd).2
  have hact : activeThread m = .ok (thread1 ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]) := by
    simp [activeThread, listIndex, h.shape.threads, h.shape.active]
  have hs3 : Shape { m with threads := [thread1 ctx [ctx.caller]] } ctx [ctx.caller]
      m.mem.memory.allocations := ⟨rfl, h.shape.active, rfl⟩
  have hprefix : ∀ p0 : Ptr, mapGet lm (localName 0) = some p0 → evalReturn m = (do
      let (retVal, m4) ← typedLoad { m with threads := [thread1 ctx [ctx.caller]] } p0
        (tyOf d) ⟨(itOf d).size.bytes⟩ .None
      let (frame, cm) ← deallocAll lm.entries.length (calleeFrameL f ctx lm blk stmt) m4.mem
      let m5 := { m4 with mem := cm }
      match frame.stack_pop_action with
      | .BottomOfStack => terminateActiveThread m5
      | .BackToCaller nextBlock _ callerRetPtr => do
        let t ← activeThread m5
        if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
        else do
          let m6 ← typedStore m5 callerRetPtr retVal (tyOf d) ⟨(itOf d).size.bytes⟩ .None
          match nextBlock with
          | some nb => jumpToBlock m6 nb
          | none => ub "return from a function where caller did not specify next block") := by
    intro p0 hp0
    simp only [evalReturn, hact, ok_bind, thread1, List.getLast?_cons_cons, List.getLast?_singleton,
      listSet, h.shape.active, h.shape.threads]
    simp [calleeFrameL, h.hf.1, mapIndex, hloc0, hT.layout, expect_align_sized, hp0]
    rfl
  -- `_0`'s storage, for a live `_0`.
  have hstore : ∀ slot0, locals[0]? = some slot0 → slot0 ≠ .dead →
      ∃ (p0 : Ptr) (id0 : Nat), mapGet lm (localName 0) = some p0 ∧ p0.provenance = some (⟨(id0 : Int)⟩, ()) ∧
        Align.is_aligned ⟨(itOf d).size.bytes⟩ p0.addr = true ∧
        m.mem.memory.allocations[id0]? = some (stackAlloc p0.addr (itOf d) (declSlotData d slot0)) := by
    intro slot0 hs0 hne
    obtain ⟨p0, hp0⟩ := h.locs.some_of_live hs0 hne
    obtain ⟨id0, hpid0, _, haddr0, _, hA0⟩ := h.locs.storage 0 d slot0 p0 hd hs0 hp0
    exact ⟨p0, id0, hp0, hpid0, by simp only [Align.is_aligned, haddr0.1]; rfl, hA0⟩
  constructor
  · intro v hv
    obtain ⟨p0, id0, hp0, hpid0, hal0, hA0⟩ := hstore _ hv (by simp)
    have hslot0 := h.slots 0 d _ hd hv
    obtain ⟨m4, hm4, hs4⟩ := typedLoad_ptr_localTy hs3 p0 id0 hpid0 d hdScalar v hslot0 hA0 _ hal0
    obtain ⟨hidnd, hok, hlow, hown⟩ := h.locs.teardown h.hf
    obtain ⟨cm5, hcm5, hcm5mem⟩ := deallocAll_gen lm.entries.length
      (calleeFrameL f ctx lm blk stmt) m4.mem lm.entries (Nat.le_refl _) rfl h.locs.keysNodup hidnd
      (by
        intro e he
        obtain ⟨T, it, a', h1, h2, h3, h4, h5⟩ := hok e he
        exact ⟨T, it, a', h1, h2, h3, by rw [hs4.allocs]; exact h4, h5⟩)
    obtain ⟨R0, hR0⟩ := h.locs.base
    have hall : ∀ (j : Nat) b, R0[j]? = some b → b.live = true →
        ctx.base.length + j ∈ lm.entries.map (fun e => provId e.2) := by
      intro j b hb hlb
      refine hown (ctx.base.length + j) b ?_ hlb (by omega)
      rw [hR0, List.getElem?_append_right (by omega)]
      simpa using hb
    obtain ⟨R, hRk, hRdead⟩ := killAt_append_dead ctx.base R0 _ hlow hall
    rw [hs4.allocs, hR0, hRk] at hcm5mem
    have hs5 : Shape { m4 with mem := cm5 } ctx [ctx.caller] (ctx.base ++ R) :=
      ⟨hs4.threads, hs4.active, hcm5mem⟩
    have hact5 : activeThread { m4 with mem := cm5 } = .ok (thread1 ctx [ctx.caller]) := by
      simp [activeThread, listIndex, hs4.threads, hs4.active]
    obtain ⟨acc, hst⟩ := typedStore_base_localTy hs5 ctx.retPtr r a hp hr hlive haddrr d hdScalar
      hlenr v hslot0 ⟨(itOf d).size.bytes⟩ (by simp only [Align.is_aligned, halr]; rfl)
    have hs6 := withMem_shape (allocs' := ctx.base.set r { a with data := declSlotData d (.init v) } ++
        R) hs5 acc
    obtain ⟨m7, hm7, hs7⟩ := mutateCurFrame_single hs6
      (fun fr => { fr with next_block := ctx.nextBlock, next_stmt := 0 })
    refine ⟨m7, R, ?_, hs7, hRdead⟩
    rw [hprefix p0 hp0, hm4]
    simp only [ok_bind]
    rw [hcm5]
    simp only [ok_bind, calleeFrameL, hact5, thread1, hst]
    simp [jumpToBlock, hm7]
  · intro hu
    obtain ⟨p0, id0, hp0, hpid0, hal0, hA0⟩ := hstore _ hu (by simp)
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_localTy_uninit hs3 p0 id0 hpid0 d hdScalar hA0 _ hal0
    exact ⟨msg, by rw [hprefix p0 hp0, hmsg]; rfl⟩

/-! ## Shapes of fragment statements and terminators -/

theorem translateStatement_some {decls : List LocalDecl} {st : MirAst.Statement}
    {st' : Gen.Statement} (h : translateStatement decls st = some st') :
    (∃ i rv e, st.kind = .assign ⟨i, []⟩ rv ∧ translateRvalue decls (copyRv rv) = some e ∧
      st' = .Assign (.Local (localName i)) e) ∨
    (∃ p pe, st.kind = .placeMention p ∧ translatePlace p = some pe ∧
      st' = .PlaceMention pe) ∨
    (∃ i, st.kind = .storageLive i ∧ st' = .StorageLive (localName i)) ∨
    (∃ i, st.kind = .storageDead i ∧ st' = .StorageDead (localName i)) ∨
    (∃ p pe, st.kind = .deinit p ∧ translatePlace p = some pe ∧ st' = .Deinit pe) := by
  obtain ⟨kind, span⟩ := st
  simp only [translateStatement] at h ⊢
  match kind, h with
  | .assign ⟨i, []⟩ rv, h =>
    cases he : translateRvalue decls (copyRv rv) with
    | none => simp [he] at h
    | some e => simp [he] at h; exact .inl ⟨i, rv, e, rfl, he, h.symm⟩
  | .assign ⟨_, _ :: _⟩ _, h => simp at h
  | .setDiscriminant _ _, h => simp at h
  | .deinit p, h =>
    cases hpe : translatePlace p with
    | none => simp [hpe] at h
    | some pe => simp [hpe] at h; exact .inr (.inr (.inr (.inr ⟨p, pe, rfl, hpe, h.symm⟩)))
  | .storageLive i, h => simp at h; exact .inr (.inr (.inl ⟨i, rfl, h.symm⟩))
  | .storageDead i, h => simp at h; exact .inr (.inr (.inr (.inl ⟨i, rfl, h.symm⟩)))
  | .retag _ _, h => simp at h
  | .placeMention p, h =>
    cases hpe : translatePlace p with
    | none => simp [hpe] at h
    | some pe => simp [hpe] at h; exact .inr (.inl ⟨p, pe, rfl, hpe, h.symm⟩)
  | .intrinsic _, h => simp at h
  | .coverage, h => simp at h
  | .constEvalCounter, h => simp at h
  | .backwardIncompatibleDropHint _, h => simp at h
  | .nop, h => simp at h

theorem translateTerminator_some {decls : List LocalDecl} {t : MirAst.Terminator}
    {tt : Gen.Terminator} (h : translateTerminator decls t = some tt) :
    (∃ target, t.kind = .goto target ∧ tt = .Goto (bbName target)) ∨
    (∃ discr targets, t.kind = .switchInt discr targets) ∨
    (t.kind = .unreachable ∧ tt = .Unreachable) ∨
    (t.kind = .return_ ∧ tt = .Return) := by
  obtain ⟨kind, span⟩ := t
  simp only [translateTerminator] at h ⊢
  match kind, h with
  | .goto target, h => simp at h; exact .inl ⟨target, rfl, h.symm⟩
  | .switchInt discr targets, _ => exact .inr (.inl ⟨discr, targets, rfl⟩)
  | .unreachable, h => simp at h; exact .inr (.inr (.inl ⟨rfl, h.symm⟩))
  | .return_, h => simp at h; exact .inr (.inr (.inr ⟨rfl, h.symm⟩))
  | .unwindResume, h => simp at h
  | .unwindTerminate, h => simp at h
  | .drop _ _ _, h => simp at h
  | .call _ _ _ _ _, h => simp at h
  | .tailCall _ _, h => simp at h
  | .assert _ _ _ _, h => simp at h
  | .inlineAsm _ _ _, h => simp at h

theorem terminatorOk_switch {decls : List LocalDecl} {nblocks : Nat} {t : MirAst.Terminator}
    {discr : Operand} {targets : SwitchTargets}
    (h : terminatorOk decls nblocks t = true) (hk : t.kind = .switchInt discr targets) :
    ∃ it, switchIntType decls (copyOp discr) = some it ∧ discrOk decls (copyOp discr) = true ∧
    (∀ p ∈ targets.branches, p.1 < 2 ^ (8 * it.size.bytes) ∧ p.2 < nblocks) ∧
    targets.otherwise < nblocks := by
  simp only [terminatorOk, hk] at h
  cases hit : switchIntType decls (copyOp discr) with
  | none => simp [hit] at h
  | some it =>
    simp only [hit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hokd, hbr⟩, _⟩, ho⟩ := h
    exact ⟨it, rfl, hokd, hbr, ho⟩

/-- A translated fragment `switchInt`: the switch value evaluates to the
integer `int_from_bits(bits)` at the switch type `it` (for a `bool`
discriminant, through `minimize`'s transmute to `u8`), and the discriminant's
`copy` form is a fragment operand of a fragment type stored like `it`. -/
theorem switch_spec {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    {t : MirAst.Terminator} {tt : Gen.Terminator} {discr : Operand} {targets : SwitchTargets}
    (hk : t.kind = .switchInt discr targets) (htt : translateTerminator body.localDecls t = some tt)
    {it : Gen.IntType} (hit : switchIntType body.localDecls (copyOp discr) = some it)
    (hdok : discrOk body.localDecls (copyOp discr) = true) :
    (∃ T, FragTy T it ∧ OperandOkT body.localDecls T (copyOp discr)) ∧
    ∃ value, tt = .Switch value (switchCases it targets.branches) (bbName targets.otherwise) ∧
      (∀ bits, opBits locals (copyOp discr) = some bits →
        bits < 2 ^ (8 * it.size.bytes) ∧
        ∃ m', evalValue m value = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
          FrameOk body f ctx locals lm m' blk stmt) ∧
      (opBits locals (copyOp discr) = none → ∃ msg, evalValue m value = .error (.ub msg)) := by
  simp only [translateTerminator, hk, Option.bind_eq_bind] at htt
  unfold switchIntType at hit
  unfold discrOk at hdok
  cases hv : translateOperand (copyOp discr) with
  | none => simp [hv] at htt
  | some v =>
    simp only [hv, Option.bind_some] at htt
    split at hit
    · next it' hty =>
      simp only [Option.some.injEq] at hit
      subst hit
      simp only [hty] at hdok
      have htt' : tt = .Switch v (switchCases it' targets.branches) (bbName targets.otherwise) := by
        simpa [hty] using htt.symm
      have hgood := operandOk_good hdok
      refine ⟨⟨.Int it', .int it' hgood, operandOk_T hdok⟩, v, htt', ?_⟩
      exact evalValue_operand h it' (copyOp discr) hdok v hv
    · next hty =>
      simp only [Option.some.injEq] at hit
      subst hit
      simp only [hty] at hdok
      have htt' : tt = .Switch (boolToU8 v) (switchCases u8Ty targets.branches)
          (bbName targets.otherwise) := by
        simpa [hty] using htt.symm
      have hokT := operandOkB_T hdok
      refine ⟨⟨.Bool, .bool, hokT⟩, boolToU8 v, htt', ?_⟩
      obtain ⟨hsome, hnone⟩ := evalValue_operandT h .bool (copyOp discr) hokT v hv
      refine ⟨fun bits hb => ?_, fun hb => ?_⟩
      · obtain ⟨hbv, m', hm', h'⟩ := hsome bits hb
        have hb2 : bits < 2 := by simpa [ValidBits] using hbv
        refine ⟨by simp [u8Ty]; omega, m', ?_, h'⟩
        rw [evalValue_boolToU8 m m' v _ hm']
        rcases (by omega : bits = 0 ∨ bits = 1) with rfl | rfl <;> rfl
      · obtain ⟨msg, hmsg⟩ := hnone hb
        exact ⟨msg, by simp [boolToU8, evalValue, hmsg]⟩
    · simp at hit

theorem lookupSwitchTarget_lt (bits : Nat) (branches : List (Nat × Nat)) (otherwise n : Nat)
    (hbr : ∀ p ∈ branches, p.2 < n) (ho : otherwise < n) :
    MirSemantics.lookupSwitchTarget bits branches otherwise < n := by
  induction branches with
  | nil => simpa [MirSemantics.lookupSwitchTarget] using ho
  | cons p ps ih =>
    obtain ⟨v, t⟩ := p
    simp only [MirSemantics.lookupSwitchTarget]
    cases Nat.beq bits v
    · exact ih (fun q hq => hbr q (by simp [hq]))
    · exact hbr (v, t) (by simp)

theorem lookupSwitchTarget_mem (bits : Nat) (branches : List (Nat × Nat)) (otherwise : Nat) :
    MirSemantics.lookupSwitchTarget bits branches otherwise ∈
      otherwise :: branches.map Prod.snd := by
  induction branches with
  | nil => simp [MirSemantics.lookupSwitchTarget]
  | cons p ps ih =>
    obtain ⟨v, t⟩ := p
    simp only [MirSemantics.lookupSwitchTarget, List.map_cons]
    cases Nat.beq bits v
    · simp only
      rcases List.mem_cons.mp ih with h | hmem
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)
    · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem listIndex_nat {α : Type} (xs : List α) (k : Nat) (x : α) (h : xs[k]? = some x) (what : String) :
    listIndex xs (k : Int) what = .ok x := by
  simp [listIndex, h]

/-! ## Introducing `StepRel` -/

theorem StepRel.tau' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s s' : MachineState}
    {r : Interp Mach} (m' : Mach) (hr : r = .ok m') (h : StateRel body f ctx s' m') :
    StepRel body f ctx s (.tau (.running s')) r := ⟨m', hr, h⟩

theorem StepRel.emit' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {ev : MirObs} {k : PUnit → MirExecState} {r : Interp Mach} (s' : MachineState) (m' : Mach)
    (hk : k PUnit.unit = .running s') (hr : r = .ok m') (h : StateRel body f ctx s' m') :
    StepRel body f ctx s (.vis (.inr (.inl (.emit ev))) k) r := ⟨s', m', hk, hr, h⟩

theorem StepRel.ret' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {v : Value} {mem : MirSemantics.Memory} {r : Interp Mach} (m' : Mach) (hr : r = .ok m')
    (h : ReturnRel body ctx s v m') :
    StepRel body f ctx s (.ret (.normal (v, mem))) r := ⟨m', hr, h⟩

theorem StepRel.ub' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {r : Interp Mach} (msg : String) (hr : r = .error (.ub msg)) :
    StepRel body f ctx s (MirStepNode.fail .ub) r := ⟨msg, hr⟩

/-! ## Constructing `StateRel` -/

/-- The relation after a statement: Anneal advanced to the next statement with
slots `actual'` and memory `mem'`, MiniRust to the next statement with the
view `view'` and the locals map `lm'`. -/
theorem StateRelAt.advance {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach} (hrel : StateRelAt body f ctx s view m)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlt : s.frame.stmtIdx < bb.statements.length)
    (actual' view' : List LocalSlot) (mem' : MirSemantics.Memory) (lm' : Map Gen.LocalName Ptr)
    (m' : Mach)
    (hthr : m'.threads =
      [thread1 ctx [ctx.caller, calleeFrameL f ctx lm' s.frame.blockIdx (s.frame.stmtIdx + 1)]])
    (hact : m'.active_thread = 0)
    (hlo : LocalsOk body ctx view' lm' m'.mem.memory.allocations)
    (hstale : StaleOk body actual' view' s.frame.blockIdx (s.frame.stmtIdx + 1))
    (hret : view'[0]? ≠ some .dead)
    (hbor : mem'.borrows = []) (hcs : mem'.callStack = s.memory.callStack)
    (hac : mem'.activeCallee = s.memory.activeCallee)
    (hpr : mem'.activeProtectors = s.memory.activeProtectors)
    (hcl : mem'.callerLocals = s.memory.callerLocals) :
    StateRel body f ctx (advanceStmt s actual' mem') m' :=
  ⟨view', {
    frame := ⟨lm', hthr, hlo⟩
    active := hact
    blk := hrel.blk
    stmt := fun bb' hbb' => by
      simp only [advanceStmt] at hbb' ⊢
      rw [hbb] at hbb'
      cases hbb'
      show s.frame.stmtIdx + 1 ≤ bb.statements.length
      omega
    stale := hstale
    retLive := hret
    ret := hrel.ret
    baseLow := hrel.baseLow
    borrows := hbor
    callStack := hcs.trans hrel.callStack
    activeCallee := hac.trans hrel.activeCallee
    protectors := hpr.trans hrel.protectors
    callerLocals := hcl.trans hrel.callerLocals }⟩

/-- Anneal's state after jumping to block `t` with slots `locals`. -/
def jumpState (s : MachineState) (t : Nat) (locals : List LocalSlot) : MachineState :=
  { s with frame := { blockIdx := t, stmtIdx := 0, locals := locals } }

/-- The relation after a jump to the in-range block `t`. -/
theorem StateRelAt.jump {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach} (hrel : StateRelAt body f ctx s view m) {m' : Mach}
    (lm : Map Gen.LocalName Ptr) (t : Nat) (ht : t < body.basicBlocks.length)
    (actual' : List LocalSlot)
    (hthr : m'.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm t 0]])
    (hact : m'.active_thread = 0) (hlo : LocalsOk body ctx view lm m'.mem.memory.allocations)
    (hstale : StaleOk body actual' view t 0) :
    StateRel body f ctx (jumpState s t actual') m' :=
  ⟨view, {
    frame := ⟨lm, hthr, hlo⟩
    active := hact
    blk := ht
    stmt := fun _ _ => Nat.zero_le _
    stale := hstale
    retLive := hrel.retLive
    ret := hrel.ret
    baseLow := hrel.baseLow
    borrows := hrel.borrows
    callStack := hrel.callStack
    activeCallee := hrel.activeCallee
    protectors := hrel.protectors
    callerLocals := hrel.callerLocals }⟩

/-- The `moveKind` of a fragment rvalue. -/
theorem moveKind_of_rvalueOk {decls : List LocalDecl} {it : Gen.IntType} {rv : Rvalue}
    (h : rvalueOk decls it (copyRv rv) = true) : moveKind rv = true := by
  cases rv with
  | unaryOp uop op => cases uop <;> simp_all [copyRv, rvalueOk, translateUnOp, moveKind]
  | cast k op ty => cases k <;> simp_all [copyRv, rvalueOk, moveKind]
  | _ => simp_all [copyRv, rvalueOk, moveKind]

theorem moveKind_of_rvalueOkB {decls : List LocalDecl} {rv : Rvalue}
    (h : rvalueOkB decls (copyRv rv) = true) : moveKind rv = true := by
  cases rv with
  | unaryOp uop op => cases uop <;> simp_all [copyRv, rvalueOkB, moveKind]
  | _ => simp_all [copyRv, rvalueOkB, moveKind]

theorem moveKind_of_rvalueOkO {decls : List LocalDecl} {rv : Rvalue}
    (h : rvalueOkO decls (copyRv rv) = true) : moveKind rv = true := by
  cases rv <;> simp_all [copyRv, rvalueOkO, moveKind]

theorem moveKind_of_rvalueOkTuple {decls : List LocalDecl} {it : Gen.IntType} {rv : Rvalue}
    (h : rvalueOkTuple decls it (copyRv rv) = true) : moveKind rv = true := by
  cases rv with
  | aggregate k ops => cases k <;> simp_all [copyRv, rvalueOkTuple, moveKind]
  | _ => simp_all [copyRv, rvalueOkTuple, moveKind]

theorem retLive_set {view : List LocalSlot} (h : view[0]? ≠ some .dead) (i : Nat) {x : LocalSlot}
    (hx : x ≠ .dead) : (view.set i x)[0]? ≠ some .dead := by
  rw [List.getElem?_set]
  split
  · split <;> simp_all
  · exact h

/-! ## The theorem -/

/-- **Correspondence theorem (one step).** For a fragment body `body`, its
`minimize`-style translation `f`, and related states, one Anneal MIR step and
one MiniRust `Machine::step` correspond in the sense of `StepRel`. -/
theorem step_correspondence (body : CapturedMir) (f : Gen.Function) (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) :
    StepRel body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨view, hrel⟩ := hrel
  obtain ⟨hphase, hargs, hn31, hbbs, hsdOk, hmvOk, hmtOk⟩ := inFragment_spec body hfrag
  have hspec := translateFn_spec body f hf
  obtain ⟨lm, hthr, hlo⟩ := hrel.frame
  obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hrel.blk⟩
  have hbbmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
  obtain ⟨_, hstmts, hterm⟩ := hbbs bb hbbmem
  obtain ⟨tb, htb, hgetb⟩ := hspec.2.2 _ bb hbb
  obtain ⟨hlen, hstspec, htermspec⟩ := translateBlock_spec _ bb tb htb
  obtain ⟨hmvS, hmvT, hmvEdge⟩ := movesOk_spec hmvOk hbb
  have hshape : Shape m ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]
      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
  have hframe : FrameOk body f ctx view lm (resetPick m) s.frame.blockIdx s.frame.stmtIdx :=
    ⟨.of_translateFn hf, resetPick_shape hshape, hlo⟩
  have hslotsA : SlotsOk body.localDecls s.frame.locals := hrel.stale.slots hlo.slots
  have hnA : s.frame.locals.length = body.localDecls.length := hrel.stale.1.trans hlo.nlocals
  rw [step_callee hshape tb hgetb]
  have hstmt_le := hrel.stmt bb hbb
  rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with hlt | hge
  · ----------------------------------------------------------------- statement
    have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
      rw [hlen]; omega
    obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hstmem : st ∈ bb.statements := List.mem_of_getElem? hst
    obtain ⟨st', hst', htst⟩ := hstspec _ st hst
    rw [stepMirFn_stmt body s bb st hrel.activeCallee hphase hbb hst]
    have hok := hstmts st hstmem
    have hreads := hmvS _ st hst
    rcases translateStatement_some hst' with ⟨i, rv, e, hkind, he, rfl⟩ | ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨i, hkind, rfl⟩ | ⟨i, hkind, rfl⟩ | ⟨p, pe, hkind, hpe, rfl⟩
    · ------------------------------------------------------------ assign
      have hreadsMo : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) (rvOperands rv) =
          true := by
        simpa [stmtReadsOk, hkind] using hreads
      have hr0 : readsOk [] (rvOperands rv) = true :=
        readsOk_mono (fun _ h => by simp at h) hreadsMo
      have hagree := hrel.stale.readsAgree hreadsMo
      have hal : i ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals, hkind])
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      simp only [statementOk] at hok
      cases hdi : body.localDecls[i]? with
      | none => simp [hdi] at hok
      | some d =>
        have hi : i < s.frame.locals.length := by
          rw [hnA]; exact (List.getElem?_eq_some_iff.mp hdi).1
        -- Both models' results, by the destination's type.
        obtain ⟨res, hk, hMok, hMnone, hAok, hAnone⟩ : ∃ res : Option Value, moveKind rv = true ∧
            (∀ v, res = some v → view[i]? ≠ some .dead →
              ∃ m3, evalStatement (resetPick m) (.Assign (.Local (localName i)) e) = .ok m3 ∧
                FrameOk body f ctx (view.set i (.init v)) lm m3 s.frame.blockIdx s.frame.stmtIdx) ∧
            (res = none → view[i]? ≠ some .dead →
              ∃ msg, evalStatement (resetPick m) (.Assign (.Local (localName i)) e) =
                .error (.ub msg)) ∧
            (∀ v, res = some v →
              evalRvalue s.frame.locals (copyRv rv) s.memory body.localDecls body.layouts =
                .ok v s.frame.locals s.memory) ∧
            (res = none →
              evalRvalue s.frame.locals (copyRv rv) s.memory body.localDecls body.layouts = .ub) := by
          cases htup : intBoolTupleOf d.ty with
          | some it =>
            have hb := intBoolTupleOf_isBoolTy htup
            have ho := intBoolTupleOf_isOrderingTy htup
            have hitd : itOf d = it := (tyOf_tuple htup).2
            have htup' : intBoolTupleOf d.ty = some (itOf d) := by rw [hitd]; exact htup
            have hokT : rvalueOkTuple body.localDecls (itOf d) (copyRv rv) = true := by
              rw [hitd]; simpa [hdi, hb, ho, htup] using hok
            have hgood := hframe.decl_good i d hdi
            have hfr : rvTupleBits s.frame.locals (itOf d) (copyRv rv) =
                rvTupleBits view (itOf d) (copyRv rv) := rvTupleBits_frame hagree
            obtain ⟨hA1, hA2⟩ := evalRvalue_fragTuple body.localDecls s.frame.locals hslotsA hnA
              (itOf d) hgood (copyRv rv) hokT s.memory body.layouts
            refine ⟨(rvTupleBits view (itOf d) (copyRv rv)).map
                (fun pr => .aggregate 0 [.scalar ⟨pr.1, (itOf d).size.bytes⟩, .scalar ⟨pr.2, 1⟩]),
              moveKind_of_rvalueOkTuple hokT, ?_, ?_, ?_, ?_⟩
            · intro v hv hlive
              obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
              exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv) hokT e he).1
                bits b hpb
            · intro hv hlive
              exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv) hokT e he).2
                (Option.map_eq_none_iff.mp hv)
            · intro v hv
              obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
              exact hA1 bits b (hfr.trans hpb)
            · intro hv
              exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
          | none =>
            cases hb : isBoolTy d.ty with
            | true =>
              have hit : itOf d = u8Ty := (tyOf_bool hb).2
              have hokB : rvalueOkB body.localDecls (copyRv rv) = true := by
                simpa [hdi, hb] using hok
              have hfr : rvBitsB body.localDecls s.frame.locals (copyRv rv) =
                  rvBitsB body.localDecls view (copyRv rv) := rvBitsB_frame hagree
              obtain ⟨hA1, hA2⟩ := evalRvalue_fragB body.localDecls s.frame.locals hslotsA hnA
                (copyRv rv) hokB s.memory body.layouts
              refine ⟨(rvBitsB body.localDecls view (copyRv rv)).map
                  (fun r => .scalar ⟨r, (itOf d).size.bytes⟩),
                moveKind_of_rvalueOkB hokB, ?_, ?_, ?_, ?_⟩
              · intro v hv hlive
                obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                exact (evalStatement_assignB hframe i d hdi hlive hb (copyRv rv) hokB e he).1 r hr
              · intro hv hlive
                exact (evalStatement_assignB hframe i d hdi hlive hb (copyRv rv) hokB e he).2
                  (Option.map_eq_none_iff.mp hv)
              · intro v hv
                obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                rw [hit]
                exact hA1 r (hfr.trans hr)
              · intro hv
                exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
            | false =>
              cases ho : isOrderingTy d.ty with
              | true =>
                have hit : itOf d = u8Ty := (tyOf_ordering ho).2
                have hokO : rvalueOkO body.localDecls (copyRv rv) = true := by
                  simpa [hdi, hb, ho] using hok
                have hfr : rvBitsO body.localDecls s.frame.locals (copyRv rv) =
                    rvBitsO body.localDecls view (copyRv rv) := rvBitsO_frame hagree
                obtain ⟨hA1, hA2⟩ := evalRvalue_fragO body.localDecls s.frame.locals hslotsA hnA
                  (copyRv rv) hokO s.memory body.layouts
                refine ⟨(rvBitsO body.localDecls view (copyRv rv)).map
                    (fun r => .scalar ⟨r, (itOf d).size.bytes⟩),
                  moveKind_of_rvalueOkO hokO, ?_, ?_, ?_, ?_⟩
                · intro v hv hlive
                  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                  exact (evalStatement_assignO hframe i d hdi hlive ho (copyRv rv) hokO e he).1 r hr
                · intro hv hlive
                  exact (evalStatement_assignO hframe i d hdi hlive ho (copyRv rv) hokO e he).2
                    (Option.map_eq_none_iff.mp hv)
                · intro v hv
                  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                  rw [hit]
                  exact hA1 r (hfr.trans hr)
                · intro hv
                  exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
              | false =>
                cases hit : intTypeOf d.ty with
                | none => simp [hdi, hb, ho, htup, hit] at hok
                | some it =>
                  have hitd : itOf d = it := (tyOf_int hit).2
                  have hok' : rvalueOk body.localDecls (itOf d) (copyRv rv) = true := by
                    rw [hitd]; simpa [hdi, hb, ho, htup, hit] using hok
                  have hint : intTypeOf d.ty = some (itOf d) := by rw [hitd]; exact hit
                  have hgood := hframe.decl_good i d hdi
                  have hfr : rvBits body.localDecls s.frame.locals (itOf d) (copyRv rv) =
                      rvBits body.localDecls view (itOf d) (copyRv rv) := rvBits_frame hagree
                  obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA
                    (itOf d) hgood (copyRv rv) hok' s.memory body.layouts
                  refine ⟨(rvBits body.localDecls view (itOf d) (copyRv rv)).map
                      (fun r => .scalar ⟨r, (itOf d).size.bytes⟩),
                    moveKind_of_rvalueOk hok', ?_, ?_, ?_, ?_⟩
                  · intro v hv hlive
                    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                    exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv) hok' e he).1 r hr
                  · intro hv hlive
                    exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv) hok' e he).2
                      (Option.map_eq_none_iff.mp hv)
                  · intro v hv
                    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                    exact hA1 r (hfr.trans hr)
                  · intro hv
                    exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
        obtain ⟨hA1, hA2⟩ := evalStmt_assign_move s body.localDecls body.layouts i rv span hk hr0 hi
          hrel.borrows hrel.protectors
        by_cases hdead : s.frame.locals[i]? = some .dead
        · -- A dead destination is UB in both models.
          have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
          obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
          have hA : evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ body.localDecls body.layouts =
              MirStepNode.fail .ub := by
            cases hres : res with
            | none => exact hA2 (hAnone hres)
            | some v => exact (hA1 v (hAok v hres)).2 hdead
          rw [hA]
          exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
        · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
          cases hres : res with
          | none =>
            rw [hA2 (hAnone hres)]
            obtain ⟨msg, hmsg⟩ := hMnone hres hlive
            exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
          | some v =>
            rw [(hA1 v (hAok v hres)).1 hdead]
            obtain ⟨m3, hm3, h3⟩ := hMok v hres hlive
            obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
            refine StepRel.tau' m4
              (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
            exact hrel.advance hbb hlt _ (view.set i (.init v)) _ lm m4 h4.threads h4.active
              (by rw [h4.allocs]; exact h3.locs) (hrel.stale.assign hbb hst rfl (.init v))
              (retLive_set hrel.retLive i (by simp)) rfl rfl rfl rfl rfl
    · ------------------------------------------------------------ placeMention
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      have hpOk : placeOk body.localDecls p = true := by simpa [statementOk] using hok
      have hal : p.local_ ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      obtain ⟨hpl, hMlive, hMdead⟩ := evalStatement_placeMention_place hframe p hpOk pe hpe
      by_cases hdead : s.frame.locals[p.local_]? = some .dead
      · rw [evalStmt_placeMention_dead s body.localDecls body.layouts p span hdead]
        obtain ⟨msg, hmsg⟩ := hMdead ((hrel.stale.dead_iff _).mp hdead) hal
        exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
      · have hlive : view[p.local_]? ≠ some .dead :=
          fun h => hdead ((hrel.stale.dead_iff _).mpr h)
        rw [evalStmt_placeMention_place s body.localDecls body.layouts p span hslotsA hnA hpl hdead]
        have hM := hMlive hlive
        obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee hframe.shape
        refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hM, hm4, check_after h4]) ?_
        exact hrel.advance hbb hlt _ view _ lm m4 h4.threads h4.active
          (by rw [h4.allocs]; exact hlo) (hrel.stale.keep hbb hst rfl) hrel.retLive hrel.borrows
          rfl rfl rfl rfl
    · ------------------------------------------------------------ storageLive
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      have hin : i < body.localDecls.length := by simpa [statementOk] using hok
      have hal : i ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageLive s body.localDecls body.layouts i span hi]
      obtain ⟨m3, lm3, hm3, h3⟩ := evalStatement_storageLive hframe i d hd hal hrel.baseLow hn31
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
      refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
      exact hrel.advance hbb hlt _ (view.set i .uninit) _ lm3 m4 h4.threads h4.active
        (by rw [h4.allocs]; exact h3.locs) (hrel.stale.setBoth hbb hst rfl .uninit)
        (retLive_set hrel.retLive i (by simp)) hrel.borrows rfl rfl rfl rfl
    · ------------------------------------------------------------ storageDead
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      have hin : i < body.localDecls.length := by simpa [statementOk] using hok
      have hal : i ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      have hi0 : body.argCount < i := storageDeadOk_spec hsdOk hbbmem hstmem rfl
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageDead s body.localDecls body.layouts i span hi]
      obtain ⟨m3, hm3, h3⟩ := evalStatement_storageDead hframe i d hd hal
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
      refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
      exact hrel.advance hbb hlt _ (view.set i .dead) _ _ m4 h4.threads h4.active
        (by rw [h4.allocs]; exact h3.locs) (hrel.stale.setBoth hbb hst rfl .dead)
        (by rw [List.getElem?_set_ne (by omega)]; exact hrel.retLive) hrel.borrows rfl rfl rfl rfl
    · ------------------------------------------------------------ deinit
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      obtain ⟨i, proj⟩ := p
      cases proj with
      | cons _ _ => simp [statementOk] at hok
      | nil =>
        have hin : i < body.localDecls.length := by simpa [statementOk] using hok
        simp only [translatePlace, Option.some.injEq] at hpe
        subst hpe
        have hal : i ∉ alwaysStorageLiveLocals body :=
          mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
        obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
        have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
        obtain ⟨hMlive, hMdead⟩ := evalStatement_deinit hframe i d hd
        obtain ⟨hAlive, hAdead⟩ := evalStmt_deinit s body.localDecls body.layouts i span hi
        by_cases hdead : s.frame.locals[i]? = some .dead
        · rw [hAdead hdead]
          obtain ⟨msg, hmsg⟩ := hMdead ((hrel.stale.dead_iff i).mp hdead) hal
          exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
        · rw [hAlive hdead]
          obtain ⟨m3, hm3, h3⟩ := hMlive (fun h => hdead ((hrel.stale.dead_iff i).mpr h))
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
          refine StepRel.tau' m4
            (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
          exact hrel.advance hbb hlt _ (view.set i .uninit) _ lm m4 h4.threads h4.active
            (by rw [h4.allocs]; exact h3.locs) (hrel.stale.setBoth hbb hst rfl .uninit)
            (retLive_set hrel.retLive i (by simp)) hrel.borrows rfl rfl rfl rfl
  · ----------------------------------------------------------------- terminator
    have heq : s.frame.stmtIdx = bb.statements.length := by omega
    have hif : ((s.frame.stmtIdx : Nat) : Int) = (tb.statements.length : Int) := by rw [hlen, heq]
    rw [stepMirFn_term body s bb hrel.activeCallee hphase hbb heq]
    simp only [hif, ↓reduceIte]
    have hstale_end : StaleOk body s.frame.locals view s.frame.blockIdx bb.statements.length := by
      rw [← heq]; exact hrel.stale
    rcases translateTerminator_some htermspec with
      ⟨t, hk, htt⟩ | ⟨discr, targets, hk⟩ | ⟨hk, htt⟩ | ⟨hk, htt⟩
    · -------------------------------------------------------------- goto
      have ht : t < body.basicBlocks.length := by
        simpa [terminatorOk, hk] using hterm
      obtain ⟨m3, hm3, h3⟩ := jumpToBlock_callee hframe.shape t
      have hA : evalTerminator s bb.terminator (some body) =
          MirStepNode.step (jumpState s t s.frame.locals) := by
        simp [MirSemantics.evalTerminator, hk, jumpState]
      have hsub : ∀ j ∈ movedBefore body s.frame.blockIdx bb.statements.length,
          j ∈ movedBefore body t 0 := by
        simpa [termTargets, termMoved, hk] using hmvEdge t (by simp [termTargets, hk])
      rw [hA]
      exact StepRel.tau' m3 (by simp [htt, Interp.evalTerminator, hm3, check_after h3])
        (hrel.jump lm t ht _ h3.threads h3.active (by rw [h3.allocs]; exact hlo)
          (hstale_end.toBlock hsub))
    · -------------------------------------------------------------- switchInt
      obtain ⟨it, hit, hdok, hbr, hother⟩ := terminatorOk_switch hterm hk
      obtain ⟨⟨T, hT, hokT⟩, v, htt, hMok, hMnone⟩ := switch_spec hframe hk htermspec hit hdok
      have hreadsD : readsOk (movedBefore body s.frame.blockIdx bb.statements.length) [discr] =
          true := by
        simpa [termReadsOk, hk] using hmvT
      have hsimple : simpleOp discr = true := (readsOk_spec hreadsD discr (by simp)).1
      have hbitsEq : opBits s.frame.locals (copyOp discr) = opBits view (copyOp discr) :=
        opBits_frame _ (by
          rw [opRead_copyOp]
          exact fun j hj => hstale_end.agree ((readsOk_spec hreadsD discr (by simp)).2 j hj))
      obtain ⟨hAok, hAnone⟩ := evalOperand_fragT body.localDecls s.frame.locals hslotsA hnA hT
        (copyOp discr) hokT s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals
      have hmove := evalOperand_move s.frame.locals discr hsimple s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals
      cases hb : opBits view (copyOp discr) with
      | none =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk, hmove, hAnone (hbitsEq.trans hb), opWithLocals]
        rw [hA]
        obtain ⟨msg, hmsg⟩ := hMnone hb
        exact StepRel.ub' msg (by simp [htt, Interp.evalTerminator, hmsg])
      | some bits =>
        obtain ⟨hblt, m3, hm3, h3⟩ := hMok bits hb
        have hlookup := switch_lookup it bits hblt targets.branches (fun p hp => (hbr p hp).1)
          targets.otherwise
        have htgt := lookupSwitchTarget_lt bits targets.branches targets.otherwise
          body.basicBlocks.length (fun p hp => (hbr p hp).2) hother
        have htgtMem : MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise ∈
            termTargets bb.terminator := by
          rw [termTargets, hk]
          exact lookupSwitchTarget_mem bits targets.branches targets.otherwise
        have hsub : ∀ j ∈ moveOut (movedBefore body s.frame.blockIdx bb.statements.length) discr,
            j ∈ movedBefore body
              (MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise) 0 := by
          simpa [termMoved, hk] using hmvEdge _ htgtMem
        obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape
          (MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise)
        have hA : evalTerminator s bb.terminator (some body) =
            MirStepNode.emitStep (.event bits)
              (jumpState s (MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise)
                (opPost s.frame.locals discr)) := by
          simp [MirSemantics.evalTerminator, hk, hmove, hAok bits (hbitsEq.trans hb), opWithLocals,
            jumpState]
        rw [hA]
        have hM : evalTerminator (resetPick m) tb.terminator = .ok m4 := by
          rw [htt]
          simp only [Interp.evalTerminator, hm3, ok_bind]
          rw [hlookup]
          exact hm4
        exact StepRel.emit' _ m4 rfl (by simp [hM, check_after h4])
          (hrel.jump lm _ htgt _ h4.threads h4.active (by rw [h4.allocs]; exact h3.locs)
            (hstale_end.toBlockMove discr hsub))
    · -------------------------------------------------------------- unreachable
      have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
        simp [MirSemantics.evalTerminator, hk]
      rw [hA]
      exact StepRel.ub' "reached unreachable code" (by simp [htt, Interp.evalTerminator, ub])
    · -------------------------------------------------------------- return
      have hn0 : 0 < body.localDecls.length := by omega
      obtain ⟨d0, hd0⟩ : ∃ d, body.localDecls[0]? = some d := ⟨_, List.getElem?_eq_getElem hn0⟩
      obtain ⟨r0, a0, hp, hr0, hlive, haddrr, hlenr, halr⟩ := hrel.ret d0 hd0
      have hRet := evalReturn_frame hframe d0 hd0 r0 a0 hp hr0 hlive haddrr hlenr halr
      have h0mo : 0 ∉ movedBefore body s.frame.blockIdx bb.statements.length := by
        simpa [termReadsOk, hk] using hmvT
      have h0eq : s.frame.locals[0]? = view[0]? := hstale_end.agree h0mo
      obtain ⟨slot0, hs0⟩ : ∃ slot, view[0]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hn0)⟩
      have hslot0 := hlo.slots 0 d0 slot0 hd0 hs0
      have hsA : s.frame.locals[0]? = some slot0 := h0eq.trans hs0
      match slot0, hslot0, hs0, hsA with
      | .dead, _, hs0, _ => exact absurd hs0 hrel.retLive
      | .uninit, _, hs0, hsA =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk, get?, hsA]
        rw [hA]
        obtain ⟨msg, hmsg⟩ := hRet.2 hs0
        exact StepRel.ub' msg (by simp [htt, Interp.evalTerminator, hmsg])
      | .init v, hv0, hs0, hsA =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.retNormal v s.memory := by
          simp [MirSemantics.evalTerminator, hk, get?, hsA, hrel.callStack]
        rw [hA]
        obtain ⟨m', R, hm', hs', hR⟩ := hRet.1 v hs0
        exact StepRel.ret' m' (by simp [htt, Interp.evalTerminator, hm', check_after hs'])
          ⟨r0, a0, d0, R, hd0, hv0, hp, hr0, hs'.threads, hs'.allocs, hR⟩

/-! ## Entry block (`f.start`) -/

theorem steps_add (a b : Nat) (m : Mach) :
    Interp.steps (a + b) m = Interp.steps a m >>= Interp.steps b := by
  induction a generalizing m with
  | zero => simp [Interp.steps]
  | succ a ih =>
    rw [Nat.add_right_comm a 1 b]
    simp only [Interp.steps]
    cases h : Interp.step m with
    | error e => simp
    | ok m1 => simp [ih]

theorem steps_one {m m' : Mach} (h : Interp.step m = .ok m') : Interp.steps 1 m = .ok m' := by
  simp [Interp.steps, h]

/-- The number of MiniRust steps of `minimize`'s init block: one per
`StorageLive` of `alwaysStorageLiveLocals`, then `Goto(bb0)`. -/
def initLen (body : CapturedMir) : Nat := (alwaysStorageLiveLocals body).length + 1

theorem alwaysStorageLiveLocals_spec {body : CapturedMir} {j : Nat}
    (h : j ∈ alwaysStorageLiveLocals body) : body.argCount + 1 ≤ j ∧ j < body.localDecls.length := by
  simp only [alwaysStorageLiveLocals, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.2.1, h.1⟩

theorem alwaysStorageLiveLocals_nodup (body : CapturedMir) : (alwaysStorageLiveLocals body).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

/-- At `f.start`, the locals map holds the return place and the arguments in
their initial allocations, and no temporary of the init block is allocated
yet. -/
theorem StartRel.localsOk {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {mInit : Mach} (hstart : StartRel body f ctx s mInit)
    (hargs : body.argCount + 1 ≤ body.localDecls.length) :
    LocalsOkA body ctx [] s.frame.locals (localsMap ctx (body.argCount + 1))
      mInit.mem.memory.allocations := by
  have hmap : ∀ j, mapGet (localsMap ctx (body.argCount + 1)) (localName j) =
      if j < body.argCount + 1 then some (localPtr ctx j) else none := by
    intro j
    simp only [localsMap]
    exact mapGet_range_map _ _ _
  have hR := hstart.allocs
  have hn := hstart.nlocals
  have hLlen : (localAllocs ctx (body.localDecls.take (body.argCount + 1)) s.frame.locals).length =
      body.argCount + 1 := by
    simp [localAllocs, localAllocsFrom_length, hn]; omega
  have hget : ∀ (i : Nat) d slot, i < body.argCount + 1 → body.localDecls[i]? = some d →
      s.frame.locals[i]? = some slot →
      mInit.mem.memory.allocations[ctx.base.length + i]? =
        some (stackAlloc (ctx.addrs.getD i 0) (itOf d) (declSlotData d slot)) := by
    intro i d slot hi hd hs
    rw [hR, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, localAllocs]
    rw [localAllocsFrom_getElem? ctx 0 _ _ i d slot (by rw [List.getElem?_take_of_lt hi]; exact hd) hs]
    simp [localAlloc]
  refine {
    nlocals := hn
    slots := hstart.slots
    base := ⟨_, hR⟩
    keysNodup := ?_
    keysLocal := ?_
    live := ?_
    storage := ?_
    inj := ?_
    owned := ?_ }
  · simp only [localsMap, List.map_map]
    exact nodup_map_of_inj_on _ _ List.nodup_range
      (fun x _ y _ h => by simpa [Function.comp, localName_inj] using h)
  · intro e he
    simp only [localsMap, List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    exact ⟨i, by omega, rfl⟩
  · intro i slot hs
    have hil : i < body.localDecls.length := by
      rw [← hn]; exact (List.getElem?_eq_some_iff.mp hs).1
    rw [hmap i]
    split
    · next hi =>
      simp only [Option.isSome_some, true_iff]
      exact .inl (hstart.argsLive i slot (by omega) hs)
    · next hi =>
      have := hstart.tempsDead i (by omega) hil
      rw [hs] at this
      cases this
      simp
  · intro i d slot p hd hs hp
    rw [hmap i] at hp
    split at hp
    · next hi =>
      cases hp
      exact ⟨ctx.base.length + i, rfl, by omega,
        (hstart.addrs i d (by omega) hd).1,
        .inl (hstart.addrs i d (by omega) hd).2, hget i d slot hi hd hs⟩
    · cases hp
  · intro i j p q hp hq hpq
    rw [hmap] at hp hq
    split at hp <;> split at hq <;> simp only [Option.some.injEq, reduceCtorEq] at hp hq
    subst hp hq
    simp only [localPtr, Option.some.injEq, Prod.mk.injEq, and_true] at hpq
    have : ((ctx.base.length + i : Nat) : Int) = ((ctx.base.length + j : Nat) : Int) := by
      simpa using congrArg (fun x => x._0) hpq
    omega
  · intro id a ha hlive hb
    have hlt : id - ctx.base.length < body.argCount + 1 := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [hR, List.length_append, hLlen] at this
      omega
    refine ⟨id - ctx.base.length, localPtr ctx (id - ctx.base.length), by rw [hmap]; simp [hlt], ?_⟩
    simp only [localPtr]
    congr
    omega

/-- **Init block.** From `StartRel` (Anneal at `(0, 0)` and MiniRust at
`f.start`), `initLen body` MiniRust steps execute `minimize`'s init block
(`StorageLive` of each temporary of `alwaysStorageLiveLocals`, then
`Goto(bb0)`) and land in `StateRel`. -/
theorem step_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit) :
    ∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRel body f ctx s m0 := by
  obtain ⟨_, hargs, hn31, _, _, _, _⟩ := inFragment_spec body hfrag
  obtain ⟨hfstart, hinit⟩ := translateFn_start body f hf
  have hAnd := alwaysStorageLiveLocals_nodup body
  have hlenS : (initBlock body).statements.length = (alwaysStorageLiveLocals body).length := by
    simp [initBlock]
  -- The init-block invariant after `k` steps.
  have key : ∀ k, k ≤ (alwaysStorageLiveLocals body).length → ∃ m lm,
      Interp.steps k mInit = .ok m ∧
      Shape m ctx [ctx.caller, calleeFrameL f ctx lm body.basicBlocks.length k]
        m.mem.memory.allocations ∧
      LocalsOkA body ctx ((alwaysStorageLiveLocals body).take k) s.frame.locals lm
        m.mem.memory.allocations := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨mInit, localsMap ctx (body.argCount + 1), rfl, ⟨?_, hstart.active, rfl⟩,
        by simpa using hstart.localsOk hargs⟩
      rw [hstart.threads]
      simp [calleeFrame, calleeFrameL, hfstart]
    | succ k ih =>
      intro hk
      obtain ⟨m, lm, hm, hsh, hlo⟩ := ih (by omega)
      have hkA : k < (alwaysStorageLiveLocals body).length := by omega
      obtain ⟨hlo1, hlo2⟩ := alwaysStorageLiveLocals_spec
        (List.getElem_mem (l := alwaysStorageLiveLocals body) hkA)
      have hnot : (alwaysStorageLiveLocals body)[k] ∉ (alwaysStorageLiveLocals body).take k := by
        intro hmem
        obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
        rw [List.getElem_take] at hjk
        have := hAnd.getElem_inj.mp hjk
        simp at hj
        omega
      have hst : (initBlock body).statements[k]? =
          some (.StorageLive (localName (alwaysStorageLiveLocals body)[k])) := by
        simp [initBlock, List.getElem?_map, List.getElem?_eq_getElem hkA]
      have htake : (alwaysStorageLiveLocals body).take (k + 1) =
          (alwaysStorageLiveLocals body).take k ++ [(alwaysStorageLiveLocals body)[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkA, Option.toList_some]
      generalize (alwaysStorageLiveLocals body)[k] = a at hnot hlo1 hlo2 hst htake
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[a]? = some d := ⟨_, List.getElem?_eq_getElem hlo2⟩
      have hsa : s.frame.locals[a]? = some .dead := hstart.tempsDead a (by omega) hlo2
      have hpa : mapGet lm (localName a) = none := by
        cases hp : mapGet lm (localName a) with
        | none => rfl
        | some p =>
          have := (hlo.live a .dead hsa).mp (by simp [hp])
          simp [hnot] at this
      obtain ⟨m3, lm3, hm3, hsh3, hlo3⟩ := evalStatement_storageLive_init hf (resetPick_shape hsh)
        hlo a d hd hsa hpa hstart.baseLow hn31
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee hsh3
      have hne : ((k : Nat) : Int) ≠ ((initBlock body).statements.length : Int) := by
        rw [hlenS]; omega
      have hstep : Interp.step m = .ok m4 := by
        rw [step_callee hsh (initBlock body) hinit]
        simp [hne, listIndex_nat _ _ _ hst, hm3, hm4, check_after h4]
      refine ⟨m4, lm3, ?_, ⟨h4.threads, h4.active, rfl⟩, ?_⟩
      · rw [steps_add, hm, ok_bind, steps_one hstep]
      · rw [htake, h4.allocs]
        exact hlo3
  obtain ⟨m, lm, hm, hsh, hlo⟩ := key _ (Nat.le_refl _)
  rw [List.take_length] at hlo
  obtain ⟨m0, hm0, h0⟩ := jumpToBlock_callee (resetPick_shape hsh) 0
  have hif : (((alwaysStorageLiveLocals body).length : Nat) : Int) =
      ((initBlock body).statements.length : Int) := by rw [hlenS]
  have hstep : Interp.step m = .ok m0 := by
    rw [step_callee hsh (initBlock body) hinit]
    simp [hif, initBlock, Interp.evalTerminator, hm0, check_after h0]
  refine ⟨m0, by rw [initLen, steps_add, hm, ok_bind, steps_one hstep], s.frame.locals, ?_⟩
  have hn0 : 0 < body.localDecls.length := by omega
  exact {
    frame := ⟨lm, by rw [hstart.blk0, hstart.stmt0]; exact h0.threads,
      by rw [h0.allocs]; exact hlo⟩
    active := h0.active
    blk := by rw [hstart.blk0]; exact hstart.hasBlocks
    stmt := fun _ _ => by rw [hstart.stmt0]; exact Nat.zero_le _
    stale := ⟨rfl, fun j hj => absurd rfl hj⟩
    retLive := by
      obtain ⟨slot0, hs0⟩ : ∃ slot, s.frame.locals[0]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hstart.nlocals]; exact hn0)⟩
      rw [hs0]
      simpa using hstart.argsLive 0 slot0 (Nat.zero_le _) hs0
    ret := hstart.ret
    baseLow := hstart.baseLow
    borrows := hstart.borrows
    callStack := hstart.callStack
    activeCallee := hstart.activeCallee
    protectors := hstart.protectors
    callerLocals := hstart.callerLocals }

theorem initLocalsAux_spec (ds : List LocalDecl) (vs : List Value) (idx : Nat)
    (h : argsOkAux (ds.take vs.length) vs = true) (hlen : vs.length ≤ ds.length) :
    (initLocalsAux (idx + 1) ds vs).length = ds.length ∧
    (∀ (j : Nat) d slot, ds[j]? = some d → (initLocalsAux (idx + 1) ds vs)[j]? = some slot →
      SlotOk (tyOf d) slot) ∧
    (∀ (j : Nat) slot, j < vs.length → (initLocalsAux (idx + 1) ds vs)[j]? = some slot →
      slot ≠ .dead) ∧
    (∀ (j : Nat), vs.length ≤ j → j < ds.length → (initLocalsAux (idx + 1) ds vs)[j]? = some .dead) := by
  induction ds generalizing vs idx with
  | nil =>
    cases vs with
    | nil => simp [initLocalsAux]
    | cons _ _ => simp at hlen
  | cons d ds ih =>
    cases vs with
    | nil =>
      have hcons : initLocalsAux (idx + 1) (d :: ds) [] = .dead :: initLocalsAux (idx + 1) ds [] :=
        rfl
      obtain ⟨hl, hs, _, hd⟩ := ih [] idx (by simp [argsOkAux]) (by simp)
      rw [hcons]
      refine ⟨by simp [hl], fun j d' slot hd' hs' => ?_, fun j _ hj => by simp at hj, fun j _ hj => ?_⟩
      · cases j with
        | zero => simp at hs'; subst hs'; trivial
        | succ j => simp at hd' hs'; exact hs j d' slot hd' hs'
      · cases j with
        | zero => rfl
        | succ j => simpa using hd j (Nat.zero_le _) (by simpa using hj)
    | cons v vs =>
      simp only [List.length_cons, List.take_succ_cons, argsOkAux, Bool.and_eq_true] at h
      obtain ⟨hv, hvs⟩ := h
      have hcons : initLocalsAux (idx + 1) (d :: ds) (v :: vs) =
          .init v :: initLocalsAux (idx + 1) ds vs := rfl
      obtain ⟨hl, hs, hlive, hd⟩ := ih vs idx hvs (by simpa using hlen)
      have hvslot : SlotOk (tyOf d) (.init v) := by
        match v, hv with
        | .scalar sc, hv =>
          simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at hv
          exact ⟨hv.1, (validBits_iff _ _).mp hv.2⟩
        | .aggregate 0 [.scalar sc0, .scalar sc1], hv =>
          simp only [argOk] at hv
          cases ht : tupleIntOfTy (tyOf d) with
          | none => simp [ht] at hv
          | some it =>
            simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hv
            exact ⟨it, ht, hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩
      rw [hcons]
      refine ⟨by simp [hl], fun j d' slot hd' hs' => ?_, fun j slot hj hs' => ?_, fun j hj1 hj2 => ?_⟩
      · cases j with
        | zero => simp at hd' hs'; subst hd' hs'; exact hvslot
        | succ j => simp at hd' hs'; exact hs j d' slot hd' hs'
      · cases j with
        | zero => simp at hs'; subst hs'; simp
        | succ j => simp at hs' hj; exact hlive j slot (by omega) hs'
      · cases j with
        | zero => simp at hj1
        | succ j => simpa using hd j (by simp at hj1; omega) (by simpa using hj2)

/-- General entry-state bridge: for any fragment `body`, well-typed `args`, and
well-formed caller context `ctx`, Anneal's `initMachineState body args`
(the initial state of `mirCallTree body args`) satisfies `StartRel` against any
MiniRust machine positioned at `f.start` whose stack holds the callee frame
with the return place and the arguments, allocated in local order. -/
theorem initMachineState_startRel {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx (body.argCount + 1) 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs ctx (body.localDecls.take (body.argCount + 1))
        (initMachineState body args).frame.locals) :
    StartRel body f ctx (initMachineState body args) mInit := by
  have hbne : body.basicBlocks ≠ [] := by
    simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq] at hfrag
    exact hfrag.1.1.1.1.1.2
  obtain ⟨_, hdeclLen, _⟩ := inFragment_spec body hfrag
  cases hdecls : body.localDecls with
  | nil => simp [hdecls] at hdeclLen
  | cons d0 ds =>
    rw [hdecls] at hdeclLen
    have hargs' : argsOkAux (ds.take body.argCount) args = true := by
      simpa [argsOk, hdecls] using hargs
    have hlenA : args.length = body.argCount := by
      have key : ∀ (ds' : List LocalDecl) (vs : List Value), argsOkAux ds' vs = true →
          vs.length = ds'.length := by
        intro ds'
        induction ds' with
        | nil => intro vs h; cases vs <;> simp_all [argsOkAux]
        | cons d' ds' ih =>
          intro vs h
          cases vs with
          | nil => simp [argsOkAux] at h
          | cons v vs =>
            simp only [argsOkAux, Bool.and_eq_true] at h
            simp [ih vs h.2]
      have := key _ _ hargs'
      simp at this hdeclLen
      omega
    obtain ⟨hlen, hslots, hlive, hdead⟩ :=
      initLocalsAux_spec ds args 0 (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega)
    have hinit : (initMachineState body args).frame.locals = .uninit :: initLocalsAux 1 ds args := by
      simp [initMachineState, hdecls, initLocalsAux]
    refine {
      threads := hthreads
      active := hactive
      allocs := hallocs
      blk0 := rfl
      stmt0 := rfl
      hasBlocks := by
        cases hbbs : body.basicBlocks with | nil => exact absurd hbbs hbne | cons _ _ => simp
      nlocals := by simp [hinit, hdecls, hlen]
      slots := ?_
      argsLive := ?_
      tempsDead := ?_
      addrs := hctx.addrs
      ret := hctx.ret
      baseLow := hctx.baseLow
      borrows := rfl
      callStack := rfl
      activeCallee := rfl
      protectors := rfl
      callerLocals := rfl }
    · intro i d slot hd hs
      rw [hdecls] at hd
      rw [hinit] at hs
      cases i with
      | zero => simp at hd hs; subst hs; trivial
      | succ k => simp at hd hs; exact hslots k d slot hd hs
    · intro i slot hi hs
      rw [hinit] at hs
      cases i with
      | zero => simp at hs; subst hs; simp
      | succ k => simp at hs; exact hlive k slot (by omega) hs
    · intro i hi1 hi2
      rw [hinit]
      cases i with
      | zero => omega
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hdead k (by omega) (by rw [hdecls] at hi2; simpa using hi2)

/-! ## Multi-function & multi-frame stack simulation (`MR-4.1`) -/

theorem step_callee_stack {m : Mach} {rootCtx curCtx : Ctx} {callerFrames : List Frame}
    {f : Gen.Function} {lm : Map Gen.LocalName Ptr} {blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m rootCtx (callerFrames ++ [calleeFrameL f curCtx lm blk stmt]) allocs)
    (tb : Gen.BasicBlock) (htb : mapGet f.blocks (bbName blk) = some tb) :
    Interp.step m = (do
      let m' ← if (stmt : Int) = (tb.statements.length : Int) then
          evalTerminator (resetPick m) tb.terminator
        else do
          let st ← listIndex tb.statements (stmt : Int) "block.statements[frame.next_stmt]"
          let m' ← evalStatement (resetPick m) st
          mutateCurFrame m' (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
      CM.check_data_races m'.mem m'.active_thread (setInsert m.synchronized_threads 0, m.mem.accesses)
      pure m') := by
  have hany : m.threads.any (fun t => decide (t.state = .Enabled)) = true := by
    simp [h.threads, thread1]
  have hpick : ∀ mm : Mach, mm.threads = m.threads → pickActiveThread mm = .ok 0 :=
    fun mm hmm => pick_eq (hmm.trans h.threads)
  have hcur : ∀ mm : Mach, mm.threads = m.threads → mm.active_thread = 0 →
      curFrame mm = .ok (calleeFrameL f curCtx lm blk stmt) :=
    fun mm hmm hact => curFrame_append ⟨hmm.trans h.threads, hact, rfl⟩
  simp only [Interp.step, hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTracking,
    h.active]
  rw [hpick { m with mem := { memory := m.mem.memory, accesses := [] }, active_thread := 0 } rfl]
  simp only [ok_bind]
  rw [hcur { m with mem := { memory := m.mem.memory, accesses := [] }, active_thread := 0 } rfl rfl]
  simp only [ok_bind, mapIndex, calleeFrameL, htb]
  rfl

theorem progInFragment_spec {entry : CapturedMir} {callees : List CapturedMir}
    (h : progInFragment entry callees = true) :
    ((entry :: callees).map (·.defPath)).Nodup ∧
    (∀ b ∈ entry :: callees, bodyInProgFragment (fnNameMap entry callees) callees b = true) ∧
    ∃ rootBudget, maxStackLocalsAux (callees.length + 1) callees entry = some rootBudget ∧
      rootBudget < 2 ^ 31 := by
  simp only [progInFragment, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnd, hall⟩, hmax⟩, _⟩ := h
  cases hm : maxStackLocals entry callees with
  | none => simp [hm] at hmax
  | some rb =>
    simp only [hm, decide_eq_true_eq] at hmax
    exact ⟨hnd, hall, rb, hm, hmax⟩

theorem bodyInProgFragment_spec {fnMap : FnMap}
    {callees : List CapturedMir} {body : CapturedMir}
    (h : bodyInProgFragment fnMap callees body = true) :
    body.phase = .runtimePostCleanup ∧
    body.argCount + 1 ≤ body.localDecls.length ∧
    body.localDecls.length < 2 ^ 31 ∧
    body.basicBlocks ≠ [] ∧
    (∀ blk bb, body.basicBlocks[blk]? = some bb →
      bb.isCleanup = false ∧
      (∀ st ∈ bb.statements, statementOk body.localDecls st = true) ∧
      (terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true ∨
        callTerminatorOk callees body blk bb.terminator = true)) ∧
    storageDeadOk body = true ∧
    movesOk body = true ∧
    mentionsOk body = true ∧
    livenessOk body = true ∧
    tupleInitOk body = true := by
  simp only [bodyInProgFragment, MirAst.CapturedMir.isRuntimePostCleanup, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hph, harg⟩, hn31⟩, _⟩, hbne⟩, hbbs⟩, hsd⟩, hmv⟩, hmt⟩, hlv⟩, hti⟩, _⟩ := h
  refine ⟨by cases hp : body.phase <;> simp_all, harg, hn31, hbne, fun blk bb hbb => ?_,
    hsd, hmv, hmt, hlv, hti⟩
  have hlt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  have hb := hbbs blk hlt
  simp only [hbb, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    terminatorInProgOk, Bool.or_eq_true] at hb
  exact ⟨hb.1.1, hb.1.2, hb.2⟩

private theorem list_mapM_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (hm : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at hm
    cases hfa : f a with
    | none => simp [hfa] at hm
    | some b =>
      cases hrest : xs.mapM f with
      | none => simp [hfa, hrest] at hm
      | some bs =>
        simp [hfa, hrest] at hm
        subst hm
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨b, List.mem_cons_self, hfa⟩
        · obtain ⟨y, hy, hfy⟩ := ih hrest hmem
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

private theorem le_foldl_max {ys : List Nat} (acc : Nat) :
    acc ≤ ys.foldl Nat.max acc ∧ ∀ y ∈ ys, y ≤ ys.foldl Nat.max acc := by
  induction ys generalizing acc with
  | nil => simp
  | cons b ys ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (Nat.max acc b)
    have hm1 : acc ≤ Nat.max acc b := Nat.le_max_left acc b
    have hm2 : b ≤ Nat.max acc b := Nat.le_max_right acc b
    refine ⟨Nat.le_trans hm1 h1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Nat.le_trans hm2 h1
    · exact h2 y hmem

theorem maxStackLocalsAux_ge {fuel : Nat} {callees : List CapturedMir} {body : CapturedMir}
    {b : Nat} (h : maxStackLocalsAux fuel callees body = some b) :
    body.localDecls.length ≤ b ∧ ∃ fuel', fuel = fuel' + 1 := by
  cases fuel with
  | zero => simp [maxStackLocalsAux] at h
  | succ fuel' =>
    simp only [maxStackLocalsAux, Option.bind_eq_bind] at h
    cases hsub : (callCalleesOf body).mapM (fun dp =>
        (MirSemantics.findCallee? callees dp).bind fun callee =>
          maxStackLocalsAux fuel' callees callee) with
    | none => simp [hsub] at h
    | some sb =>
      rw [hsub] at h
      simp at h
      subst h
      exact ⟨by omega, fuel', rfl⟩

theorem maxStackLocalsAux_callee {fuel : Nat} {callees : List CapturedMir}
    {body callee : CapturedMir} {b : Nat}
    (h : maxStackLocalsAux (fuel + 1) callees body = some b)
    {bb : BasicBlockData} (hbb : bb ∈ body.basicBlocks)
    {func : Operand} {argOps : List Operand} {dst : Place}
    {target : Option BasicBlockIdx} {unwind : UnwindAction} {dp : String}
    (hk : bb.terminator.kind = .call func argOps dst target unwind)
    (hextr : extractFnDefPath func = some dp)
    (hfind : MirSemantics.findCallee? callees dp = some callee) :
    ∃ cb, maxStackLocalsAux fuel callees callee = some cb ∧
      body.localDecls.length + cb ≤ b := by
  simp only [maxStackLocalsAux, Option.bind_eq_bind] at h
  let g := fun d : String =>
    (MirSemantics.findCallee? callees d).bind fun c =>
      maxStackLocalsAux fuel callees c
  cases hsub : (callCalleesOf body).mapM g with
  | none => rw [hsub] at h; simp at h
  | some sb =>
    rw [hsub] at h
    simp at h
    subst h
    have hdpMem : dp ∈ callCalleesOf body :=
      List.mem_filterMap.mpr ⟨bb, hbb, by simp [hk, hextr]⟩
    obtain ⟨cb, hcbMem, hg⟩ := list_mapM_mem hsub hdpMem
    simp only [g, hfind, Option.bind_some] at hg
    have hle := (le_foldl_max (ys := sb) 0).2 cb hcbMem
    exact ⟨cb, hg, by omega⟩

/-! ### `LiveInv` and `TupleInv` preservation -/

theorem mustLiveBefore_zero (body : CapturedMir) (blk : Nat) :
    mustLiveBefore body blk 0 = liveAtEntry body blk := by
  unfold mustLiveBefore
  split <;> simp

theorem mustLiveBefore_succ {body : CapturedMir} {blk k : Nat} {bb : BasicBlockData}
    {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[k]? = some st) :
    mustLiveBefore body blk (k + 1) = stmtMustLive (mustLiveBefore body blk k) st := by
  simp only [mustLiveBefore, hbb]
  rw [List.take_add_one, List.foldl_append, hst]
  rfl

theorem livenessOk_entry0 {body : CapturedMir} (h : livenessOk body = true) :
    ∀ i ∈ liveAtEntry body 0, i ≤ body.argCount := by
  simp only [livenessOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem livenessOk_edge {body : CapturedMir} (h : livenessOk body = true)
    {blk : Nat} {bb : BasicBlockData} (hbb : body.basicBlocks[blk]? = some bb)
    {t : Nat} (ht : t ∈ termTargets bb.terminator) :
    ∀ i ∈ liveAtEntry body t, i ∈ mustLiveBefore body blk bb.statements.length := by
  have hlt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  simp only [livenessOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hblk := h.2 blk hlt
  simp only [hbb, List.all_eq_true, List.contains_iff_mem] at hblk
  intro i hi
  simpa [mustLiveBefore, hbb] using hblk t ht i hi

/-- Return local `_0` is never killed by `StorageDead` under `storageDeadOk`, so
`0 ∈ liveAtEntry body blk` for every in-bounds block `blk`. -/
theorem liveAtEntry_zero_mem {body : CapturedMir}
    (harg : body.argCount + 1 ≤ body.localDecls.length)
    (hsd : storageDeadOk body = true) :
    ∀ blk < body.basicBlocks.length, 0 ∈ liveAtEntry body blk := by
  have hst_zero : ∀ bb ∈ body.basicBlocks, ∀ st ∈ bb.statements, ∀ lv : List Nat,
      0 ∈ lv → 0 ∈ stmtMustLive lv st := by
    intro bb hbb st hst lv h0
    obtain ⟨kind, span⟩ := st
    cases kind with
    | storageLive i =>
      simp only [stmtMustLive]
      split
      · exact h0
      · exact List.mem_cons_of_mem _ h0
    | storageDead i =>
      have hi : body.argCount < i := storageDeadOk_spec hsd hbb hst rfl
      simp only [stmtMustLive, List.mem_filter]
      exact ⟨h0, by simp [show (0 : Nat) ≠ i by omega]⟩
    | _ => simpa [stmtMustLive] using h0
  have hfold_zero : ∀ bb ∈ body.basicBlocks, ∀ ss : List MirAst.Statement,
      (∀ st ∈ ss, st ∈ bb.statements) → ∀ lv : List Nat,
        0 ∈ lv → 0 ∈ ss.foldl stmtMustLive lv := by
    intro bb hbb ss
    induction ss with
    | nil => intro _ lv h0; exact h0
    | cons st ss ih =>
      intro hsub lv h0
      exact ih (fun s hs => hsub s (List.mem_cons_of_mem _ hs)) _
        (hst_zero bb hbb st (hsub st List.mem_cons_self) lv h0)
  have hinit : (initLiveEntries body).length = body.basicBlocks.length ∧
      ∀ blk < body.basicBlocks.length, 0 ∈ (initLiveEntries body).getD blk [] := by
    refine ⟨by simp [initLiveEntries], fun blk hblk => ?_⟩
    simp only [initLiveEntries, List.getD, List.getElem?_map, List.getElem?_range hblk,
      Option.map_some, Option.getD_some]
    split <;> simp <;> omega
  have hstep : ∀ entries : List (List Nat),
      entries.length = body.basicBlocks.length →
      (∀ blk < body.basicBlocks.length, 0 ∈ entries.getD blk []) →
      (stepLiveEntries body entries).length = body.basicBlocks.length ∧
        ∀ dst < body.basicBlocks.length, 0 ∈ (stepLiveEntries body entries).getD dst [] := by
    intro entries hlen hent
    refine ⟨by simp [stepLiveEntries], fun dst hdst => ?_⟩
    let initAcc :=
      if dst == 0 then List.range (body.argCount + 1)
      else entries.getD dst (List.range body.localDecls.length)
    have h0init : 0 ∈ initAcc := by
      simp only [initAcc]
      split
      · simp
      · have hltE : dst < entries.length := by omega
        have heq : entries.getD dst (List.range body.localDecls.length) = entries.getD dst [] := by
          simp [List.getD, List.getElem?_eq_getElem hltE]
        rw [heq]
        exact hent dst hdst
    let stepFn (acc : List Nat) (src : Nat) : List Nat :=
      match body.basicBlocks[src]? with
      | some bb =>
        if (termTargets bb.terminator).contains dst then
          let exitLv := bb.statements.foldl stmtMustLive (entries.getD src [])
          acc.filter (fun i => exitLv.contains i)
        else acc
      | none => acc
    have hsrcs : ∀ (srcs : List Nat) (acc : List Nat), 0 ∈ acc → 0 ∈ srcs.foldl stepFn acc := by
      intro srcs
      induction srcs with
      | nil => intro acc h0; exact h0
      | cons src srcs ih =>
        intro acc h0
        apply ih
        simp only [stepFn]
        cases hbb : body.basicBlocks[src]? with
        | none => exact h0
        | some bb =>
          simp only
          split
          · have hsrcLt : src < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
            have hbbMem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
            have h0exit : 0 ∈ bb.statements.foldl stmtMustLive (entries.getD src []) :=
              hfold_zero bb hbbMem bb.statements (fun _ hs => hs) _ (hent src hsrcLt)
            exact List.mem_filter.mpr ⟨h0, List.contains_iff_mem.mpr h0exit⟩
          · exact h0
    have hget : (stepLiveEntries body entries).getD dst [] =
        (List.range body.basicBlocks.length).foldl stepFn initAcc := by
      simp only [stepLiveEntries, initAcc, stepFn, List.getD, List.getElem?_map,
        List.getElem?_range hdst, Option.map_some, Option.getD_some]
      rfl
    rw [hget]
    exact hsrcs _ initAcc h0init
  have hiter : ∀ (fuel : Nat) (entries : List (List Nat)),
      entries.length = body.basicBlocks.length →
      (∀ blk < body.basicBlocks.length, 0 ∈ entries.getD blk []) →
      ∀ blk < body.basicBlocks.length, 0 ∈ (iterLiveEntries fuel body entries).getD blk [] := by
    intro fuel
    induction fuel with
    | zero => intro entries _ hent; exact hent
    | succ n ih =>
      intro entries hlen hent blk hblk
      simp only [iterLiveEntries]
      split
      · exact hent blk hblk
      · obtain ⟨hlen', hent'⟩ := hstep entries hlen hent
        exact ih _ hlen' hent' blk hblk
  exact hiter _ _ hinit.1 hinit.2

theorem LiveInv.init {body : CapturedMir} {fr : StackFrame}
    (hlv : livenessOk body = true) (hb0 : fr.blockIdx = 0) (hs0 : fr.stmtIdx = 0)
    (hargs : ∀ (i : Nat) slot, i ≤ body.argCount → fr.locals[i]? = some slot → slot ≠ .dead) :
    LiveInv body fr := by
  intro i hi
  rw [hb0, hs0, mustLiveBefore_zero] at hi
  have hle := livenessOk_entry0 hlv i hi
  intro hdead
  exact hargs i .dead hle hdead rfl

private theorem set_ne_dead_of_ne_dead {locals : List LocalSlot} {k j : Nat} {x : LocalSlot}
    (hx : x ≠ .dead) (hj : locals[j]? ≠ some .dead) :
    (locals.set k x)[j]? ≠ some .dead := by
  rw [List.getElem?_set]
  split
  · split
    · simp [hx]
    · simp
  · exact hj

theorem LiveInv.advance_assign {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {i : Nat} {rv : Rvalue} {v : Value}
    {mem' : MirSemantics.Memory}
    (hlive : LiveInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .assign ⟨i, []⟩ rv) :
    LiveInv body (advanceStmt s ((rvPost s.frame.locals rv).set i (.init v)) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [mustLiveBefore_succ hbb hst,
    show stmtMustLive (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx by simp [stmtMustLive, hkind]] at hj
  apply set_ne_dead_of_ne_dead (by simp)
  intro hdead
  exact hlive j hj ((rvPost_dead s.frame.locals rv j).mp hdead)

theorem LiveInv.advance_placeMention {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {p : Place} {mem' : MirSemantics.Memory}
    (hlive : LiveInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .placeMention p) :
    LiveInv body (advanceStmt s s.frame.locals mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [mustLiveBefore_succ hbb hst,
    show stmtMustLive (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx by simp [stmtMustLive, hkind]] at hj
  exact hlive j hj

theorem LiveInv.advance_storageLive {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {i : Nat} {mem' : MirSemantics.Memory}
    (hlive : LiveInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .storageLive i) (hi : i < s.frame.locals.length) :
    LiveInv body (advanceStmt s (s.frame.locals.set i .uninit) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [mustLiveBefore_succ hbb hst] at hj
  have hsm : stmtMustLive (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      if (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx).contains i then
        mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx
      else i :: mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx := by
    simp [stmtMustLive, hkind]
  rw [hsm] at hj
  by_cases hji : j = i
  · subst hji
    simp [List.getElem?_set_self hi]
  · rw [List.getElem?_set_ne (Ne.symm hji)]
    have hjOld : j ∈ mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx := by
      split at hj
      · exact hj
      · rcases List.mem_cons.mp hj with rfl | hmem
        · exact absurd rfl hji
        · exact hmem
    exact hlive j hjOld

theorem LiveInv.advance_storageDead {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {i : Nat} {mem' : MirSemantics.Memory}
    (hlive : LiveInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .storageDead i) :
    LiveInv body (advanceStmt s (s.frame.locals.set i .dead) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [mustLiveBefore_succ hbb hst,
    show stmtMustLive _ st = (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx).filter (· != i) by
      simp [stmtMustLive, hkind]] at hj
  obtain ⟨hjOld, hjNe⟩ := List.mem_filter.mp hj
  have hne : j ≠ i := by simpa using hjNe
  rw [List.getElem?_set_ne (Ne.symm hne)]
  exact hlive j hjOld

theorem LiveInv.advance_deinit {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {i : Nat} {mem' : MirSemantics.Memory}
    (hlive : LiveInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .deinit ⟨i, []⟩) :
    LiveInv body (advanceStmt s (s.frame.locals.set i .uninit) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [mustLiveBefore_succ hbb hst,
    show stmtMustLive (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx by simp [stmtMustLive, hkind]] at hj
  exact set_ne_dead_of_ne_dead (by simp) (hlive j hj)

theorem LiveInv.jump_goto {body : CapturedMir} {s : MachineState} {bb : BasicBlockData}
    {t : Nat} (hlvOk : livenessOk body = true) (hlive : LiveInv body s.frame)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (heq : s.frame.stmtIdx = bb.statements.length)
    (ht : t ∈ termTargets bb.terminator) :
    LiveInv body (jumpState s t s.frame.locals).frame := by
  intro j hj
  simp only [jumpState, mustLiveBefore_zero] at hj ⊢
  have hjEnd := livenessOk_edge hlvOk hbb ht j hj
  rw [← heq] at hjEnd
  exact hlive j hjEnd

theorem LiveInv.jump_switchInt {body : CapturedMir} {s : MachineState} {bb : BasicBlockData}
    {discr : Operand} {t : Nat} (hlvOk : livenessOk body = true) (hlive : LiveInv body s.frame)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (heq : s.frame.stmtIdx = bb.statements.length)
    (ht : t ∈ termTargets bb.terminator) :
    LiveInv body (jumpState s t (opPost s.frame.locals discr)).frame := by
  intro j hj
  simp only [jumpState, mustLiveBefore_zero] at hj ⊢
  have hjEnd := livenessOk_edge hlvOk hbb ht j hj
  rw [← heq] at hjEnd
  intro hdead
  exact hlive j hjEnd ((opPost_dead s.frame.locals discr j).mp hdead)

theorem callArgsEval_ne_dead {locals locals' : List LocalSlot} {argOps : List Operand}
    {vs : List Value} (hev : callArgsEval locals argOps = some (vs, locals'))
    {j : Nat} (hj : locals[j]? ≠ some .dead) :
    locals'[j]? ≠ some .dead := by
  induction argOps generalizing locals vs with
  | nil =>
    simp [callArgsEval] at hev
    rcases hev with ⟨_, rfl⟩
    exact hj
  | cons op ops ih =>
    simp only [callArgsEval, Option.bind_eq_bind] at hev
    cases hv1 : callArgVal locals op with
    | none => simp [hv1] at hev
    | some v1 =>
      cases hr : callArgsEval (opMoveLocal locals op) ops with
      | none => simp [hv1, hr] at hev
      | some p =>
        obtain ⟨vsR, l2⟩ := p
        simp [hv1, hr] at hev
        rcases hev with ⟨_, rfl⟩
        apply ih hr
        unfold opMoveLocal
        cases opMoved op with
        | none => exact hj
        | some k => exact set_ne_dead_of_ne_dead (by simp) hj

theorem tupleInitBefore_zero (body : CapturedMir) (blk : Nat) :
    tupleInitBefore body blk 0 = tupleInitAtEntry body blk := by
  unfold tupleInitBefore
  split <;> simp

theorem tupleInitBefore_succ {body : CapturedMir} {blk k : Nat} {bb : BasicBlockData}
    {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[k]? = some st) :
    tupleInitBefore body blk (k + 1) =
      stmtTupleInit body.localDecls (tupleInitBefore body blk k) st := by
  simp only [tupleInitBefore, hbb]
  rw [List.take_add_one, List.foldl_append, hst]
  rfl

theorem tupleInitOk_entry0 {body : CapturedMir} (h : tupleInitOk body = true) :
    ∀ i ∈ tupleInitAtEntry body 0,
      1 ≤ i ∧ i ≤ body.argCount ∧ isTupleLocal body.localDecls i = true := by
  simp only [tupleInitOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro i hi
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 i hi
  exact ⟨h1, h2, h3⟩

theorem tupleInitOk_edge {body : CapturedMir} (h : tupleInitOk body = true)
    {blk : Nat} {bb : BasicBlockData} (hbb : body.basicBlocks[blk]? = some bb)
    {t : Nat} (ht : t ∈ termTargets bb.terminator) :
    ∀ i ∈ tupleInitAtEntry body t,
      i ∈ termTupleInit body.localDecls
        (tupleInitBefore body blk bb.statements.length) bb.terminator := by
  have hlt : blk < body.basicBlocks.length := (List.getElem?_eq_some_iff.mp hbb).1
  simp only [tupleInitOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hblk := h.2 blk hlt
  simp only [hbb, List.all_eq_true, List.contains_iff_mem] at hblk
  intro i hi
  simpa [tupleInitBefore, hbb] using hblk t ht i hi

/-- Every index in `tupleInitAtEntry body blk` is declared as an `(Int, bool)`
2-tuple local (`isTupleLocal body.localDecls i = true`). -/
theorem tupleInitAtEntry_isTupleLocal (body : CapturedMir) (blk : Nat) :
    ∀ i ∈ tupleInitAtEntry body blk, isTupleLocal body.localDecls i = true := by
  let allTuples := (List.range body.localDecls.length).filter (isTupleLocal body.localDecls)
  let paramTuples :=
    ((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls)
  have hall : ∀ i ∈ allTuples, isTupleLocal body.localDecls i = true :=
    fun _ hi => (List.mem_filter.mp hi).2
  have hparam : ∀ i ∈ paramTuples, isTupleLocal body.localDecls i = true :=
    fun _ hi => (List.mem_filter.mp hi).2
  have hgetD : ∀ (entries : List (List Nat)),
      (∀ b, ∀ i ∈ entries.getD b [], isTupleLocal body.localDecls i = true) →
      ∀ b, ∀ i ∈ entries.getD b allTuples, isTupleLocal body.localDecls i = true := by
    intro entries hent b i hi
    simp only [List.getD] at hi
    cases hbe : entries[b]? with
    | none => simp [hbe] at hi; exact hall i hi
    | some xs =>
      simp [hbe] at hi
      exact hent b i (by simp [List.getD, hbe, hi])
  have hinit : ∀ b, ∀ i ∈ (initTupleEntries body).getD b [],
      isTupleLocal body.localDecls i = true := by
    intro b i hi
    simp only [initTupleEntries, List.getD, List.getElem?_map] at hi
    cases hr : (List.range body.basicBlocks.length)[b]? with
    | none => simp [hr] at hi
    | some idx =>
      simp only [hr, Option.map_some, Option.getD_some] at hi
      split at hi
      · exact hparam i hi
      · exact hall i hi
  have hstep : ∀ entries : List (List Nat),
      (∀ b, ∀ i ∈ entries.getD b [], isTupleLocal body.localDecls i = true) →
      ∀ b, ∀ i ∈ (stepTupleInitEntries body entries).getD b [],
        isTupleLocal body.localDecls i = true := by
    intro entries hent b i hi
    simp only [stepTupleInitEntries, List.getD, List.getElem?_map] at hi
    cases hr : (List.range body.basicBlocks.length)[b]? with
    | none => simp [hr] at hi
    | some dst =>
      simp only [hr, Option.map_some, Option.getD_some] at hi
      let stepFn (acc : List Nat) (src : Nat) : List Nat :=
        match body.basicBlocks[src]? with
        | some bb =>
          if (termTargets bb.terminator).contains dst then
            let midTi := bb.statements.foldl (stmtTupleInit body.localDecls) (entries.getD src [])
            let exitTi := termTupleInit body.localDecls midTi bb.terminator
            acc.filter (fun j => exitTi.contains j)
          else acc
        | none => acc
      have hsub : ∀ (srcs : List Nat) (acc : List Nat),
          i ∈ srcs.foldl stepFn acc → i ∈ acc := by
        intro srcs
        induction srcs with
        | nil => intro acc h; exact h
        | cons src srcs ih =>
          intro acc h
          have h1 := ih (stepFn acc src) h
          simp only [stepFn] at h1
          cases hbb : body.basicBlocks[src]? with
          | none => simpa [hbb] using h1
          | some bb =>
            simp only [hbb] at h1
            split at h1
            · exact (List.mem_filter.mp h1).1
            · exact h1
      have hinitSub := hsub (List.range body.basicBlocks.length) _ hi
      split at hinitSub
      · exact hparam i hinitSub
      · exact hgetD entries hent dst i hinitSub
  have hiter : ∀ (fuel : Nat) (entries : List (List Nat)),
      (∀ b, ∀ i ∈ entries.getD b [], isTupleLocal body.localDecls i = true) →
      ∀ b, ∀ i ∈ (iterTupleInitEntries fuel body entries).getD b [],
        isTupleLocal body.localDecls i = true := by
    intro fuel
    induction fuel with
    | zero => intro entries hent; exact hent
    | succ n ih =>
      intro entries hent b i hi
      simp only [iterTupleInitEntries] at hi
      split at hi
      · exact hent b i hi
      · exact ih _ (hstep entries hent) b i hi
  exact hiter _ _ hinit blk

theorem slotOk_tuple_of_isTupleLocal {decls : List LocalDecl} {i : Nat} {v : Value}
    (htup : isTupleLocal decls i = true)
    (hslot : ∀ d, decls[i]? = some d → SlotOk (tyOf d) (.init v)) :
    ∃ sc0 sc1, v = .aggregate 0 [.scalar sc0, .scalar sc1] := by
  simp only [isTupleLocal] at htup
  cases hd : decls[i]? with
  | none => simp [hd] at htup
  | some d =>
    simp only [hd, Option.isSome_iff_exists] at htup
    obtain ⟨it, hit⟩ := htup
    have hv := hslot d hd
    rw [(tyOf_tuple hit).1] at hv
    match v, hv with
    | .scalar sc, ⟨_, hvb⟩ => simp [intBoolTupleTy, ValidBits] at hvb
    | .unit, hv | .ptr _ _, hv => simp [SlotOk] at hv
    | .aggregate 0 [.scalar sc0, .scalar sc1], _ => exact ⟨sc0, sc1, rfl⟩
    | .aggregate (_ + 1) _, hv | .aggregate 0 [], hv | .aggregate 0 [_], hv
    | .aggregate 0 (_ :: _ :: _ :: _), hv
    | .aggregate 0 [.unit, _], hv | .aggregate 0 [.ptr _ _, _], hv
    | .aggregate 0 [.aggregate _ _, _], hv
    | .aggregate 0 [.scalar _, .unit], hv | .aggregate 0 [.scalar _, .ptr _ _], hv
    | .aggregate 0 [.scalar _, .aggregate _ _], hv => simp [SlotOk] at hv

theorem dropMovedFrom_mem {ti : List Nat} {ops : List Operand} {j : Nat}
    (hj : j ∈ dropMovedFrom ti ops) :
    j ∈ ti ∧ ∀ op ∈ ops, opMoved op ≠ some j := by
  induction ops generalizing ti with
  | nil => exact ⟨hj, fun _ h => by simp at h⟩
  | cons op ops ih =>
    simp only [dropMovedFrom, List.foldl_cons] at hj
    obtain ⟨h1, h2⟩ := ih hj
    refine ⟨?_, fun op' hop' => ?_⟩
    · cases hm : opMoved op with
      | none => simpa [hm] using h1
      | some k =>
        rw [hm] at h1
        exact (List.mem_filter.mp h1).1
    · rcases List.mem_cons.mp hop' with rfl | hrest
      · cases hm : opMoved op' with
        | none => simp
        | some k =>
          rw [hm] at h1
          have hne : j ≠ k := by simpa using (List.mem_filter.mp h1).2
          simp [Ne.symm hne]
      · exact h2 op' hrest

theorem callArgsEval_get_of_not_moved {locals locals' : List LocalSlot} {argOps : List Operand}
    {vs : List Value} (hev : callArgsEval locals argOps = some (vs, locals'))
    {j : Nat} (hnot : ∀ op ∈ argOps, opMoved op ≠ some j) :
    locals'[j]? = locals[j]? := by
  induction argOps generalizing locals vs with
  | nil =>
    simp [callArgsEval] at hev
    rcases hev with ⟨_, rfl⟩
    rfl
  | cons op ops ih =>
    simp only [callArgsEval, Option.bind_eq_bind] at hev
    cases hv1 : callArgVal locals op with
    | none => simp [hv1] at hev
    | some v1 =>
      cases hr : callArgsEval (opMoveLocal locals op) ops with
      | none => simp [hv1, hr] at hev
      | some p =>
        obtain ⟨vsR, l2⟩ := p
        simp [hv1, hr] at hev
        rcases hev with ⟨_, rfl⟩
        rw [ih hr (fun o ho => hnot o (List.mem_cons_of_mem _ ho))]
        unfold opMoveLocal
        cases hm : opMoved op with
        | none => rfl
        | some k =>
          have hne : k ≠ j := fun heq => hnot op List.mem_cons_self (heq ▸ hm)
          exact List.getElem?_set_ne hne

theorem TupleInv.init {body : CapturedMir} {fr : StackFrame}
    (hti : tupleInitOk body = true) (hb0 : fr.blockIdx = 0) (hs0 : fr.stmtIdx = 0)
    (hargs : ∀ (i : Nat) d, 1 ≤ i → i ≤ body.argCount → body.localDecls[i]? = some d →
      ∃ v, fr.locals[i]? = some (.init v) ∧ SlotOk (tyOf d) (.init v)) :
    TupleInv body fr := by
  intro i hi
  rw [hb0, hs0, tupleInitBefore_zero] at hi
  obtain ⟨h1, h2, htup⟩ := tupleInitOk_entry0 hti i hi
  have hdSome : ∃ d, body.localDecls[i]? = some d := by
    simp only [isTupleLocal] at htup
    cases hd : body.localDecls[i]? with
    | none => simp [hd] at htup
    | some d => exact ⟨d, rfl⟩
  obtain ⟨d, hd⟩ := hdSome
  obtain ⟨v, hv, hslot⟩ := hargs i d h1 h2 hd
  obtain ⟨sc0, sc1, rfl⟩ := slotOk_tuple_of_isTupleLocal htup (fun d' hd' => by
    rw [hd] at hd'; cases hd'; exact hslot)
  exact ⟨sc0, sc1, hv⟩

theorem TupleInv.advance_assign {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {i : Nat} {d : LocalDecl}
    {rv : Rvalue} {v : Value} {mem' : MirSemantics.Memory}
    (htinv : TupleInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .assign ⟨i, []⟩ rv) (hd : body.localDecls[i]? = some d)
    (hi : i < s.frame.locals.length) (hvOk : SlotOk (tyOf d) (.init v)) :
    TupleInv body (advanceStmt s ((rvPost s.frame.locals rv).set i (.init v)) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [tupleInitBefore_succ hbb hst] at hj
  have hstTi : stmtTupleInit body.localDecls
      (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      let ti' := dropMovedFrom (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) (rvOperands rv)
      if isTupleLocal body.localDecls i then
        if ti'.contains i then ti' else i :: ti'
      else ti'.filter (· != i) := by
    simp [stmtTupleInit, hkind]
  rw [hstTi] at hj
  dsimp only at hj
  have hil : i < (rvPost s.frame.locals rv).length := by rw [rvPost_length]; exact hi
  by_cases hji : j = i
  · subst hji
    by_cases htup : isTupleLocal body.localDecls j = true
    · obtain ⟨sc0, sc1, rfl⟩ := slotOk_tuple_of_isTupleLocal htup (fun d' hd' => by
        rw [hd] at hd'; cases hd'; exact hvOk)
      exact ⟨sc0, sc1, List.getElem?_set_self hil⟩
    · simp only [Bool.not_eq_true] at htup
      rw [htup] at hj
      simp at hj
  · rw [List.getElem?_set_ne (Ne.symm hji)]
    have hjDrop : j ∈ dropMovedFrom
        (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) (rvOperands rv) := by
      split at hj
      · split at hj
        · exact hj
        · rcases List.mem_cons.mp hj with rfl | hmem
          · exact absurd rfl hji
          · exact hmem
      · exact (List.mem_filter.mp hj).1
    obtain ⟨hjOld, hnotMv⟩ := dropMovedFrom_mem hjDrop
    rw [rvPost, opsPost_get_of_not_mem _ _ _ hnotMv]
    exact htinv j hjOld

theorem TupleInv.advance_placeMention {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {p : Place} {mem' : MirSemantics.Memory}
    (htinv : TupleInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .placeMention p) :
    TupleInv body (advanceStmt s s.frame.locals mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [tupleInitBefore_succ hbb hst,
    show stmtTupleInit body.localDecls
        (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx by simp [stmtTupleInit, hkind]] at hj
  exact htinv j hj

theorem TupleInv.advance_clear {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {i : Nat} {slot : LocalSlot}
    {mem' : MirSemantics.Memory}
    (htinv : TupleInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hsm : stmtTupleInit body.localDecls
      (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx).filter (· != i)) :
    TupleInv body (advanceStmt s (s.frame.locals.set i slot) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [tupleInitBefore_succ hbb hst, hsm] at hj
  obtain ⟨hjOld, hjNe⟩ := List.mem_filter.mp hj
  have hne : j ≠ i := by simpa using hjNe
  rw [List.getElem?_set_ne (Ne.symm hne)]
  exact htinv j hjOld

theorem TupleInv.jump_goto {body : CapturedMir} {s : MachineState} {bb : BasicBlockData}
    {t : Nat} (htiOk : tupleInitOk body = true) (htinv : TupleInv body s.frame)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (heq : s.frame.stmtIdx = bb.statements.length)
    (hk : bb.terminator.kind = .goto t) :
    TupleInv body (jumpState s t s.frame.locals).frame := by
  intro j hj
  simp only [jumpState, tupleInitBefore_zero] at hj ⊢
  have ht : t ∈ termTargets bb.terminator := by simp [termTargets, hk]
  have hjEnd := tupleInitOk_edge htiOk hbb ht j hj
  simp only [termTupleInit, hk, ← heq] at hjEnd
  exact htinv j hjEnd

theorem TupleInv.jump_switchInt {body : CapturedMir} {s : MachineState} {bb : BasicBlockData}
    {discr : Operand} {targets : SwitchTargets} {t : Nat}
    (htiOk : tupleInitOk body = true) (htinv : TupleInv body s.frame)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (heq : s.frame.stmtIdx = bb.statements.length)
    (hk : bb.terminator.kind = .switchInt discr targets)
    (ht : t ∈ termTargets bb.terminator) :
    TupleInv body (jumpState s t (opPost s.frame.locals discr)).frame := by
  intro j hj
  simp only [jumpState, tupleInitBefore_zero] at hj ⊢
  have hjEnd := tupleInitOk_edge htiOk hbb ht j hj
  simp only [termTupleInit, hk, ← heq] at hjEnd
  obtain ⟨hjOld, hnotMv⟩ := dropMovedFrom_mem hjEnd
  rw [opPost_get_of_ne _ _ _ (hnotMv discr List.mem_cons_self)]
  exact htinv j hjOld

/-- Running `minimize`'s `initBlock` (`initLen body` MiniRust steps) on top of an
arbitrary stack prefix `callerFrames`: allocates `alwaysStorageLiveLocals body`
via `evalStatement_storageLive_init_cand` (lifted by `evalStatement_rethread`)
and jumps to `bb0`. -/
theorem steps_initBlock_stack {body : CapturedMir} {f : Gen.Function}
    {rootCtx curCtx : Ctx} {callerFrames : List Frame}
    {locals : List LocalSlot} {lm0 : Map Gen.LocalName Ptr} {mInit : Mach}
    {candBound : Nat}
    (hf : FnLocalsSpec body f)
    (hinit : mapGet f.blocks (bbName body.basicBlocks.length) = some (initBlock body))
    (hsh0 : Shape mInit rootCtx
      (callerFrames ++ [calleeFrameL f curCtx lm0 body.basicBlocks.length 0])
      mInit.mem.memory.allocations)
    (hlo0 : LocalsOkA body curCtx [] locals lm0 mInit.mem.memory.allocations)
    (htemps : ∀ (i : Nat), body.argCount < i → i < body.localDecls.length →
      locals[i]? = some .dead)
    (hbase : BaseCandBounded curCtx.base candBound)
    (hn : candBound + body.localDecls.length < 2 ^ 31) :
    ∃ m0 lm,
      Interp.steps (initLen body) mInit = .ok m0 ∧
      Shape m0 rootCtx (callerFrames ++ [calleeFrameL f curCtx lm 0 0])
        m0.mem.memory.allocations ∧
      m0.prog = mInit.prog ∧ m0.fn_ptrs = mInit.fn_ptrs ∧
      LocalsOk body curCtx locals lm m0.mem.memory.allocations := by
  have hAnd := alwaysStorageLiveLocals_nodup body
  have hlenS : (initBlock body).statements.length = (alwaysStorageLiveLocals body).length := by
    simp [initBlock]
  have key : ∀ k, k ≤ (alwaysStorageLiveLocals body).length → ∃ m lm,
      Interp.steps k mInit = .ok m ∧
      Shape m rootCtx (callerFrames ++ [calleeFrameL f curCtx lm body.basicBlocks.length k])
        m.mem.memory.allocations ∧
      m.prog = mInit.prog ∧ m.fn_ptrs = mInit.fn_ptrs ∧
      LocalsOkA body curCtx ((alwaysStorageLiveLocals body).take k) locals lm
        m.mem.memory.allocations := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨mInit, lm0, rfl, hsh0, rfl, rfl, by simpa using hlo0⟩
    | succ k ih =>
      intro hk
      obtain ⟨m, lm, hm, hsh, hprog, hfp, hlo⟩ := ih (by omega)
      have hkA : k < (alwaysStorageLiveLocals body).length := by omega
      obtain ⟨hlo1, hlo2⟩ := alwaysStorageLiveLocals_spec
        (List.getElem_mem (l := alwaysStorageLiveLocals body) hkA)
      have hnot : (alwaysStorageLiveLocals body)[k] ∉ (alwaysStorageLiveLocals body).take k := by
        intro hmem
        obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
        rw [List.getElem_take] at hjk
        have := hAnd.getElem_inj.mp hjk
        simp at hj
        omega
      have hst : (initBlock body).statements[k]? =
          some (.StorageLive (localName (alwaysStorageLiveLocals body)[k])) := by
        simp [initBlock, List.getElem?_map, List.getElem?_eq_getElem hkA]
      have htake : (alwaysStorageLiveLocals body).take (k + 1) =
          (alwaysStorageLiveLocals body).take k ++ [(alwaysStorageLiveLocals body)[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkA, Option.toList_some]
      generalize (alwaysStorageLiveLocals body)[k] = a at hnot hlo1 hlo2 hst htake
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[a]? = some d := ⟨_, List.getElem?_eq_getElem hlo2⟩
      have hsa : locals[a]? = some .dead := htemps a (by omega) hlo2
      have hpa : mapGet lm (localName a) = none := by
        cases hp : mapGet lm (localName a) with
        | none => rfl
        | some p =>
          have := (hlo.live a .dead hsa).mp (by simp [hp])
          simp [hnot] at this
      let fr := calleeFrameL f curCtx lm body.basicBlocks.length k
      let mR := rethread (resetPick m) curCtx [curCtx.caller, fr]
      have hshR : Shape mR curCtx [curCtx.caller, fr] mR.mem.memory.allocations :=
        ⟨rfl, rfl, rfl⟩
      obtain ⟨m3R, lm3, hm3R, hsh3R, hlo3⟩ :=
        evalStatement_storageLive_init_cand hf hshR hlo a d hd hsa hpa hbase hn
      obtain ⟨hm3, hsh3, hp3, hfp3⟩ :=
        (evalStatement_rethread (.StorageLive (localName a)) (resetPick m) rootCtx curCtx
          callerFrames fr hsh.threads rfl).1 m3R
          (calleeFrameL f curCtx lm3 body.basicBlocks.length k)
          m3R.mem.memory.allocations hm3R hsh3R
      have hm4 := bumpStmt_append hsh3
      let m4 := rethread
        (rethread m3R rootCtx (callerFrames ++ [calleeFrameL f curCtx lm3 body.basicBlocks.length k]))
        rootCtx (callerFrames ++ [calleeFrameL f curCtx lm3 body.basicBlocks.length (k + 1)])
      have hsh4 : Shape m4 rootCtx
          (callerFrames ++ [calleeFrameL f curCtx lm3 body.basicBlocks.length (k + 1)])
          m3R.mem.memory.allocations := ⟨rfl, hsh3.active, hsh3.allocs⟩
      have hne : ((k : Nat) : Int) ≠ ((initBlock body).statements.length : Int) := by
        rw [hlenS]; omega
      have hstep : Interp.step m = .ok m4 := by
        rw [step_callee_stack hsh (initBlock body) hinit]
        simp [hne, listIndex_nat _ _ _ hst, hm3, hm4, check_after hsh4, m4]
      refine ⟨m4, lm3, ?_, ⟨rfl, hsh3.active, rfl⟩, hp3.trans hprog, hfp3.trans hfp, ?_⟩
      · rw [steps_add, hm, ok_bind, steps_one hstep]
      · rw [htake]
        exact hlo3
  obtain ⟨m, lm, hm, hsh, hprog, hfp, hlo⟩ := key _ (Nat.le_refl _)
  rw [List.take_length] at hlo
  have hjmp := jumpToBlock_append (resetPick_shape hsh) 0
  let m0 := rethread (resetPick m) rootCtx (callerFrames ++ [calleeFrameL f curCtx lm 0 0])
  have hsh0' : Shape m0 rootCtx (callerFrames ++ [calleeFrameL f curCtx lm 0 0])
      m.mem.memory.allocations := ⟨rfl, rfl, rfl⟩
  have hif : (((alwaysStorageLiveLocals body).length : Nat) : Int) =
      ((initBlock body).statements.length : Int) := by rw [hlenS]
  have hstep : Interp.step m = .ok m0 := by
    rw [step_callee_stack hsh (initBlock body) hinit]
    simp [hif, initBlock, Interp.evalTerminator, hjmp, check_after hsh0', m0]
  exact ⟨m0, lm, by rw [initLen, steps_add, hm, ok_bind, steps_one hstep],
    ⟨rfl, rfl, rfl⟩, hprog, hfp, hlo⟩

theorem MultiStepRel.tau1 {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s s' : MachineState} {m : Mach}
    (m' : Mach) (hm : Interp.step m = .ok m')
    (hrel : MultiStateRel entry callees prog rootCtx s' m') :
    MultiStepRel entry callees prog rootCtx s (.tau (.running s')) m :=
  ⟨1, m', Nat.le_refl 1, steps_one hm, hrel⟩

theorem MultiStepRel.tauK {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s s' : MachineState} {m : Mach}
    (k : Nat) (m' : Mach) (hk : 1 ≤ k) (hm : Interp.steps k m = .ok m')
    (hrel : MultiStateRel entry callees prog rootCtx s' m') :
    MultiStepRel entry callees prog rootCtx s (.tau (.running s')) m :=
  ⟨k, m', hk, hm, hrel⟩

theorem MultiStepRel.emit' {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s : MachineState}
    {ev : MirObs} {k : PUnit → MirExecState} {m : Mach}
    (s' : MachineState) (m' : Mach) (hk : k PUnit.unit = .running s')
    (hm : Interp.step m = .ok m')
    (hrel : MultiStateRel entry callees prog rootCtx s' m') :
    MultiStepRel entry callees prog rootCtx s (.vis (.inr (.inl (.emit ev))) k) m :=
  ⟨s', m', hk, hm, hrel⟩

theorem MultiStepRel.ret' {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s : MachineState}
    {v : Value} {mem : MirSemantics.Memory} {m : Mach}
    (m' : Mach) (hm : Interp.step m = .ok m')
    (hr : ReturnRel entry rootCtx s v m') :
    MultiStepRel entry callees prog rootCtx s (.ret (.normal (v, mem))) m :=
  ⟨m', hm, hr⟩

theorem MultiStepRel.ub' {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s : MachineState} {m : Mach}
    (msg : String) (hm : Interp.step m = .error (.ub msg)) :
    MultiStepRel entry callees prog rootCtx s (MirStepNode.fail .ub) m :=
  ⟨msg, hm⟩

theorem CallStackRel.payloads {entry : CapturedMir} {callees : List CapturedMir}
    {fnMap : FnMap} {rootCtx : Ctx}
    {cs : List SavedCallerFrame} {cfs : List Frame} {curBody : CapturedMir}
    {curCtx : Ctx} {cb rf : Nat}
    (h : CallStackRel entry callees fnMap rootCtx cs cfs curBody curCtx cb rf) :
    curCtx.payloads = rootCtx.payloads := by
  cases h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ hPayloads => exact hPayloads

theorem CallStackRel.nil_body_eq {entry : CapturedMir} {callees : List CapturedMir}
    {fnMap : FnMap} {rootCtx : Ctx}
    {cfs : List Frame} {curBody : CapturedMir} {curCtx : Ctx} {cb rf : Nat}
    (h : CallStackRel entry callees fnMap rootCtx [] cfs curBody curCtx cb rf) :
    curBody = entry := by
  cases h
  rfl

theorem CallStackRel.inv_nil {entry : CapturedMir} {callees : List CapturedMir}
    {fnMap : FnMap} {rootCtx : Ctx}
    {callerFrames : List Frame} {curBody : CapturedMir} {curCtx : Ctx}
    {candBound remFuel : Nat}
    (h : CallStackRel entry callees fnMap rootCtx [] callerFrames curBody curCtx
      candBound remFuel) :
    callerFrames = [rootCtx.caller] ∧ curBody = entry ∧ curCtx = rootCtx ∧
    candBound = 0 ∧ BaseLow rootCtx ∧
    (∀ d, entry.localDecls[0]? = some d → RetPlaceOk rootCtx (tyOf d) (itOf d)) := by
  cases h with
  | nil hBase hRet _ _ _ => exact ⟨rfl, rfl, rfl, rfl, hBase, hRet⟩

theorem CallStackRel.inv_cons {entry : CapturedMir} {callees : List CapturedMir}
    {fnMap : FnMap} {rootCtx : Ctx}
    {savedCaller : SavedCallerFrame} {restStack : List SavedCallerFrame}
    {callerFrames : List Frame} {curBody : CapturedMir} {curCtx : Ctx}
    {candBound remFuel : Nat}
    (h : CallStackRel entry callees fnMap rootCtx (savedCaller :: restStack)
      callerFrames curBody curCtx candBound remFuel) :
    ∃ (preFrames : List Frame) (callerBody : CapturedMir) (callerFn : Gen.Function)
      (callerCtx : Ctx) (callerCandBound : Nat)
      (callerView : List LocalSlot) (callerLm : Map Gen.LocalName Ptr)
      (calleeRetDecl : LocalDecl) (callerBudget : Nat),
      callerFrames = preFrames ++ [curCtx.caller] ∧
      CallStackRel entry callees fnMap rootCtx restStack preFrames
        callerBody callerCtx callerCandBound (remFuel + 1) ∧
      savedCaller.callerBody = callerBody ∧
      callerBody ∈ entry :: callees ∧
      translateFnInProg fnMap callerBody = some callerFn ∧
      savedCaller.callerProtector = none ∧
      savedCaller.calleeProtectors = [] ∧
      savedCaller.returnTarget < callerBody.basicBlocks.length ∧
      curCtx.nextBlock = bbName savedCaller.returnTarget ∧
      curCtx.caller = calleeFrameL callerFn callerCtx callerLm
        savedCaller.frame.blockIdx savedCaller.frame.stmtIdx ∧
      curBody.localDecls[0]? = some calleeRetDecl ∧
      CallerDestRel callerBody callerCtx savedCaller.frame.locals callerView
        callerLm calleeRetDecl curCtx.base curCtx.retPtr savedCaller.destination ∧
      BaseCandBounded callerCtx.base callerCandBound ∧
      maxStackLocalsAux (remFuel + 1) callees callerBody = some callerBudget ∧
      callerCandBound + callerBudget < 2 ^ 31 ∧
      savedCaller.frame.locals.length = callerView.length ∧
      (∀ j : Nat, j ≠ savedCaller.destination.local_ →
        savedCaller.frame.locals[j]? ≠ callerView[j]? →
        j ∈ movedBefore callerBody savedCaller.returnTarget 0 ∧
          savedCaller.frame.locals[j]? = some .uninit ∧ callerView[j]? ≠ some .dead) ∧
      (∀ i ∈ liveAtEntry callerBody savedCaller.returnTarget,
        i ≠ savedCaller.destination.local_ → savedCaller.frame.locals[i]? ≠ some .dead) ∧
      (∀ i ∈ tupleInitAtEntry callerBody savedCaller.returnTarget,
        i ≠ savedCaller.destination.local_ →
        ∃ sc0 sc1, savedCaller.frame.locals[i]? =
          some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) := by
  cases h with
  | cons hRest hCallerEq hCallerMem hCallerFn hProtNone hCalleeProts hTargetLt _
      hNextBlk hCallerFrame hCalleeRetDecl hDest hCallerCand hCallerBudget _ _
      hCallerBudgetLt hPostLen hPostStale hPostLive hPostTuple =>
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, hRest, hCallerEq, hCallerMem, hCallerFn,
      hProtNone, hCalleeProts, hTargetLt, hNextBlk, hCallerFrame, hCalleeRetDecl,
      hDest, hCallerCand, hCallerBudget, hCallerBudgetLt, hPostLen, hPostStale,
      hPostLive, hPostTuple⟩

theorem writeCallDest_length (callerSlots : List LocalSlot) (destination : Place) (v : Value) :
    (writeCallDest callerSlots destination v).length = callerSlots.length := by
  unfold writeCallDest
  split
  · simp
  · split <;> simp
  · split <;> simp
  · rfl

theorem CallerDestRel.writeCallDest_isInit {callerBody : CapturedMir} {callerCtx : Ctx}
    {callerActual callerView : List LocalSlot} {callerLm : Map Gen.LocalName Ptr}
    {calleeRetDecl : LocalDecl} {calleeBase : List Gen.Allocation} {calleeRetPtr : Ptr}
    {destination : Place}
    (h : CallerDestRel callerBody callerCtx callerActual callerView callerLm
      calleeRetDecl calleeBase calleeRetPtr destination) (retVal : Value) :
    ∃ w, (writeCallDest callerActual destination retVal)[destination.local_]? = some (.init w) := by
  cases h with
  | root dst _ _ hActual =>
    have hlt : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
    exact ⟨retVal, by simp [writeCallDest, List.getElem?_set_self hlt]⟩
  | field0 dst _ _ _ sc0 sc1 _ _ hActual =>
    have hlt : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
    exact ⟨.aggregate 0 [retVal, .scalar sc1],
      by simp [writeCallDest, hActual, List.getElem?_set_self hlt]⟩
  | field1 dst _ _ _ sc0 sc1 _ _ _ hActual =>
    have hlt : dst < callerActual.length := (List.getElem?_eq_some_iff.mp hActual).1
    exact ⟨.aggregate 0 [.scalar sc0, retVal],
      by simp [writeCallDest, hActual, List.getElem?_set_self hlt]⟩

private theorem initLocalsAux_getElem? (idx : Nat) (decls : List LocalDecl) (args : List Value) :
    (MirSemantics.initLocalsAux idx decls args).length = decls.length ∧
    ∀ k, k < decls.length →
      (MirSemantics.initLocalsAux idx decls args)[k]? =
        if idx = 0 ∧ k = 0 then some .uninit
        else if k < (if idx = 0 then args.length + 1 else args.length) then
          some (.init (args[if idx = 0 then k - 1 else k]?.getD (.scalar ⟨0, 0⟩)))
        else some .dead := by
  induction decls generalizing idx args with
  | nil => simp [MirSemantics.initLocalsAux]
  | cons d ds ih =>
    cases idx with
    | zero =>
      obtain ⟨hlen, hget⟩ := ih 1 args
      refine ⟨by simp [MirSemantics.initLocalsAux, hlen], fun k hk => ?_⟩
      cases k with
      | zero => simp [MirSemantics.initLocalsAux]
      | succ k =>
        simp only [MirSemantics.initLocalsAux, List.getElem?_cons_succ]
        rw [hget k (by simp at hk; omega)]
        simp
    | succ n =>
      cases args with
      | nil =>
        obtain ⟨hlen, hget⟩ := ih (n + 1) []
        refine ⟨by simp [MirSemantics.initLocalsAux, Nat.add_eq, hlen], fun k hk => ?_⟩
        cases k with
        | zero => simp [MirSemantics.initLocalsAux]
        | succ k =>
          simp only [MirSemantics.initLocalsAux, Nat.add_eq, List.getElem?_cons_succ]
          rw [hget k (by simp at hk; omega)]
          simp
      | cons a rest =>
        obtain ⟨hlen, hget⟩ := ih (n + 1) rest
        refine ⟨by simp [MirSemantics.initLocalsAux, Nat.add_eq, hlen], fun k hk => ?_⟩
        cases k with
        | zero => simp [MirSemantics.initLocalsAux]
        | succ k =>
          simp only [MirSemantics.initLocalsAux, Nat.add_eq, List.getElem?_cons_succ]
          rw [hget k (by simp at hk; omega)]
          simp [Nat.succ_lt_succ_iff]

/-- Slot properties of `MirSemantics.initLocals callee vs` when `vs` matches
`callee`'s parameter declarations. -/
theorem initLocals_callee_spec {callee : CapturedMir} {vs : List Value}
    (hargc : callee.argCount + 1 ≤ callee.localDecls.length)
    (hlen : vs.length = callee.argCount)
    (hvsOk : ∀ (r : Nat) pd v,
      ((callee.localDecls.drop 1).take callee.argCount)[r]? = some pd →
      vs[r]? = some v → SlotOk (tyOf pd) (.init v)) :
    (MirSemantics.initLocals callee vs).length = callee.localDecls.length ∧
    (MirSemantics.initLocals callee vs)[0]? = some .uninit ∧
    (∀ (i : Nat) slot, i ≤ callee.argCount →
      (MirSemantics.initLocals callee vs)[i]? = some slot → slot ≠ .dead) ∧
    (∀ (i : Nat) d, 1 ≤ i → i ≤ callee.argCount → callee.localDecls[i]? = some d →
      ∃ v, (MirSemantics.initLocals callee vs)[i]? = some (.init v) ∧ SlotOk (tyOf d) (.init v)) ∧
    (∀ (i : Nat), callee.argCount < i → i < callee.localDecls.length →
      (MirSemantics.initLocals callee vs)[i]? = some .dead) := by
  obtain ⟨hILlen, hILget⟩ := initLocalsAux_getElem? 0 callee.localDecls vs
  refine ⟨hILlen, ?_, ?_, ?_, ?_⟩
  · rw [MirSemantics.initLocals, hILget 0 (by omega)]
    simp
  · intro i slot hi hs
    rw [MirSemantics.initLocals, hILget i (by omega)] at hs
    by_cases hi0 : i = 0
    · subst hi0; simp at hs; subst hs; simp
    · have hik : i < vs.length + 1 := by omega
      simp [hi0, hik] at hs
      subst hs; simp
  · intro i d hi1 hi2 hd
    have hik : i < vs.length + 1 := by omega
    have hrlt : i - 1 < vs.length := by omega
    obtain ⟨v, hv⟩ : ∃ v, vs[i - 1]? = some v := ⟨_, List.getElem?_eq_getElem hrlt⟩
    have hpd : ((callee.localDecls.drop 1).take callee.argCount)[i - 1]? = some d := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        show 1 + (i - 1) = i by omega]
      exact hd
    refine ⟨v, ?_, hvsOk (i - 1) d v hpd hv⟩
    rw [MirSemantics.initLocals, hILget i (by omega)]
    have hi0 : i ≠ 0 := by omega
    simp [hi0, hik, hv]
  · intro i hi1 hi2
    rw [MirSemantics.initLocals, hILget i hi2]
    have hi0 : i ≠ 0 := by omega
    have hik : ¬ (i < vs.length + 1) := by omega
    simp [hi0, hik]

/-- Lift a single-frame `evalStatement` error on `rethread (resetPick m)` to a
1-step `Interp.step` error on `m`. -/
private theorem lift_stmt_ub {curFn : Gen.Function}
    {rootCtx curCtx : Ctx} {callerFrames : List Frame} {curLm : Map Gen.LocalName Ptr}
    {blk stmt : Nat} {m : Mach} {tb : Gen.BasicBlock} {st' : Gen.Statement} {msg : String}
    (hshape : Shape m rootCtx (callerFrames ++ [calleeFrameL curFn curCtx curLm blk stmt])
      m.mem.memory.allocations)
    (htb : mapGet curFn.blocks (bbName blk) = some tb)
    (hne : ((stmt : Nat) : Int) ≠ (tb.statements.length : Int))
    (htst : tb.statements[stmt]? = some st')
    (hmsg : evalStatement
      (rethread (resetPick m) curCtx [curCtx.caller, calleeFrameL curFn curCtx curLm blk stmt])
      st' = .error (.ub msg)) :
    Interp.step m = .error (.ub msg) := by
  have hmErr :=
    (evalStatement_rethread st' (resetPick m) rootCtx curCtx callerFrames
      (calleeFrameL curFn curCtx curLm blk stmt) hshape.threads rfl).2 (.ub msg) hmsg
  rw [step_callee_stack hshape tb htb]
  simp [hne, listIndex_nat _ _ _ htst, hmErr]

/-- Lift a single-frame `evalStatement` success (`FrameOk`) on
`rethread (resetPick m)` to a 1-step `Interp.step` transition on `m`. -/
private theorem lift_stmt_ok {curBody : CapturedMir} {curFn : Gen.Function}
    {rootCtx curCtx : Ctx} {callerFrames : List Frame} {view' : List LocalSlot}
    {curLm lm' : Map Gen.LocalName Ptr} {blk stmt : Nat} {m m3R : Mach}
    {tb : Gen.BasicBlock} {st' : Gen.Statement}
    (hshape : Shape m rootCtx (callerFrames ++ [calleeFrameL curFn curCtx curLm blk stmt])
      m.mem.memory.allocations)
    (htb : mapGet curFn.blocks (bbName blk) = some tb)
    (hne : ((stmt : Nat) : Int) ≠ (tb.statements.length : Int))
    (htst : tb.statements[stmt]? = some st')
    (hm3R : evalStatement
      (rethread (resetPick m) curCtx [curCtx.caller, calleeFrameL curFn curCtx curLm blk stmt])
      st' = .ok m3R)
    (h3 : FrameOk curBody curFn curCtx view' lm' m3R blk stmt) :
    ∃ m4 : Mach,
      Interp.step m = .ok m4 ∧
      Shape m4 rootCtx (callerFrames ++ [calleeFrameL curFn curCtx lm' blk (stmt + 1)])
        m4.mem.memory.allocations ∧
      m4.prog = m.prog ∧ m4.fn_ptrs = m.fn_ptrs ∧
      LocalsOk curBody curCtx view' lm' m4.mem.memory.allocations := by
  obtain ⟨hm3, hsh3, hp3, hfp3⟩ :=
    (evalStatement_rethread st' (resetPick m) rootCtx curCtx callerFrames
      (calleeFrameL curFn curCtx curLm blk stmt) hshape.threads rfl).1 m3R
      (calleeFrameL curFn curCtx lm' blk stmt) m3R.mem.memory.allocations hm3R h3.shape
  have hm4 := bumpStmt_append hsh3
  let m4 := rethread
    (rethread m3R rootCtx (callerFrames ++ [calleeFrameL curFn curCtx lm' blk stmt]))
    rootCtx (callerFrames ++ [calleeFrameL curFn curCtx lm' blk (stmt + 1)])
  have hsh4 : Shape m4 rootCtx
      (callerFrames ++ [calleeFrameL curFn curCtx lm' blk (stmt + 1)])
      m3R.mem.memory.allocations := ⟨rfl, hsh3.active, hsh3.allocs⟩
  have hstep : Interp.step m = .ok m4 := by
    rw [step_callee_stack hshape tb htb]
    simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after hsh4, m4]
  exact ⟨m4, hstep, ⟨rfl, hsh3.active, rfl⟩, hp3, hfp3, h3.locs⟩

theorem MultiStateRelAt.advance {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach}
    (hrel : MultiStateRelAt entry callees prog rootCtx s view m)
    {bb : BasicBlockData}
    (hbb : (s.memory.activeCallee.getD entry).basicBlocks[s.frame.blockIdx]? = some bb)
    (hlt : s.frame.stmtIdx < bb.statements.length)
    {callerFrames : List Frame} {curCtx : Ctx} {curFn : Gen.Function}
    {lm' : Map Gen.LocalName Ptr} {candBound remFuel curBudget : Nat}
    (hcurMem : (s.memory.activeCallee.getD entry) ∈ entry :: callees)
    (hcurFn : translateFnInProg (fnNameMap entry callees) (s.memory.activeCallee.getD entry) =
      some curFn)
    (hstack : CallStackRel entry callees (fnNameMap entry callees) rootCtx s.memory.callStack
      callerFrames (s.memory.activeCallee.getD entry) curCtx candBound remFuel)
    (hpay : curCtx.payloads = rootCtx.payloads)
    (hcand : BaseCandBounded curCtx.base candBound)
    (hbud : maxStackLocalsAux remFuel callees (s.memory.activeCallee.getD entry) = some curBudget)
    (hbudLt : candBound + curBudget < 2 ^ 31)
    (actual' view' : List LocalSlot) (mem' : MirSemantics.Memory) (m' : Mach)
    (hthr : m'.threads =
      [thread1 rootCtx
        (callerFrames ++ [calleeFrameL curFn curCtx lm' s.frame.blockIdx (s.frame.stmtIdx + 1)])])
    (hact : m'.active_thread = 0)
    (hp : m'.prog = m.prog) (hfp : m'.fn_ptrs = m.fn_ptrs)
    (hlo : LocalsOk (s.memory.activeCallee.getD entry) curCtx view' lm' m'.mem.memory.allocations)
    (hstale : StaleOk (s.memory.activeCallee.getD entry) actual' view'
      s.frame.blockIdx (s.frame.stmtIdx + 1))
    (hret : view'[0]? ≠ some .dead)
    (hlive : LiveInv (s.memory.activeCallee.getD entry) (advanceStmt s actual' mem').frame)
    (htup : TupleInv (s.memory.activeCallee.getD entry) (advanceStmt s actual' mem').frame)
    (hcallees : mem'.callees = s.memory.callees)
    (hbor : mem'.borrows = [])
    (hcs : mem'.callStack = s.memory.callStack)
    (hac : mem'.activeCallee = s.memory.activeCallee)
    (hpr : mem'.activeProtectors = s.memory.activeProtectors)
    (hcl : mem'.callerLocals = s.memory.callerLocals) :
    MultiStateRel entry callees prog rootCtx (advanceStmt s actual' mem') m' := by
  have hacEq : (advanceStmt s actual' mem').memory.activeCallee = s.memory.activeCallee := hac
  have hcsEq : (advanceStmt s actual' mem').memory.callStack = s.memory.callStack := hcs
  refine ⟨view', {
    stack := ?_
    env := hrel.env.of_eq hp hfp
    active := hact
    blk := by simp only [advanceStmt, hac]; exact hrel.blk
    stmt := fun bb' hbb' => by
      simp only [advanceStmt, hac] at hbb' ⊢
      rw [hbb] at hbb'
      cases hbb'
      show s.frame.stmtIdx + 1 ≤ bb.statements.length
      omega
    stale := by simpa [advanceStmt, hac] using hstale
    retLive := hret
    liveInv := by simpa [hacEq] using hlive
    tupleInv := by simpa [hacEq] using htup
    calleesEq := hcallees.trans hrel.calleesEq
    activeCalleeOk := by simpa [advanceStmt, hac, hcs] using hrel.activeCalleeOk
    borrows := hbor
    protectors := hpr.trans hrel.protectors
    callerLocals := hcl.trans hrel.callerLocals }⟩
  refine ⟨callerFrames, curCtx, curFn, lm', candBound, remFuel, curBudget, ?_⟩
  simp only [advanceStmt, hac, hcs]
  exact ⟨hcurMem, hcurFn, hstack, hpay, hcand, hbud, hbudLt, hthr, hlo⟩

theorem MultiStateRelAt.jump {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach}
    (hrel : MultiStateRelAt entry callees prog rootCtx s view m)
    {callerFrames : List Frame} {curCtx : Ctx} {curFn : Gen.Function}
    {lm : Map Gen.LocalName Ptr} {candBound remFuel curBudget : Nat}
    (hcurMem : (s.memory.activeCallee.getD entry) ∈ entry :: callees)
    (hcurFn : translateFnInProg (fnNameMap entry callees) (s.memory.activeCallee.getD entry) =
      some curFn)
    (hstack : CallStackRel entry callees (fnNameMap entry callees) rootCtx s.memory.callStack
      callerFrames (s.memory.activeCallee.getD entry) curCtx candBound remFuel)
    (hpay : curCtx.payloads = rootCtx.payloads)
    (hcand : BaseCandBounded curCtx.base candBound)
    (hbud : maxStackLocalsAux remFuel callees (s.memory.activeCallee.getD entry) = some curBudget)
    (hbudLt : candBound + curBudget < 2 ^ 31)
    (t : Nat) (ht : t < (s.memory.activeCallee.getD entry).basicBlocks.length)
    (actual' : List LocalSlot) (m' : Mach)
    (hthr : m'.threads =
      [thread1 rootCtx (callerFrames ++ [calleeFrameL curFn curCtx lm t 0])])
    (hact : m'.active_thread = 0)
    (hp : m'.prog = m.prog) (hfp : m'.fn_ptrs = m.fn_ptrs)
    (hlo : LocalsOk (s.memory.activeCallee.getD entry) curCtx view lm m'.mem.memory.allocations)
    (hstale : StaleOk (s.memory.activeCallee.getD entry) actual' view t 0)
    (hlive : LiveInv (s.memory.activeCallee.getD entry) (jumpState s t actual').frame)
    (htup : TupleInv (s.memory.activeCallee.getD entry) (jumpState s t actual').frame) :
    MultiStateRel entry callees prog rootCtx (jumpState s t actual') m' :=
  ⟨view, {
    stack := ⟨callerFrames, curCtx, curFn, lm, candBound, remFuel, curBudget,
      hcurMem, hcurFn, hstack, hpay, hcand, hbud, hbudLt, hthr, hlo⟩
    env := hrel.env.of_eq hp hfp
    active := hact
    blk := ht
    stmt := fun _ _ => Nat.zero_le _
    stale := hstale
    retLive := hrel.retLive
    liveInv := hlive
    tupleInv := htup
    calleesEq := hrel.calleesEq
    activeCalleeOk := hrel.activeCalleeOk
    borrows := hrel.borrows
    protectors := hrel.protectors
    callerLocals := hrel.callerLocals }⟩

/-- Unpacking `callDestOk` at the end of a caller basic block under `LiveInv`,
`TupleInv`, `StaleOk`, and `termReadsOk`. -/
private theorem callDestOk_evalSpec {curBody : CapturedMir} {s : MachineState}
    {view : List LocalSlot} {bb : BasicBlockData} {argOps : List Operand}
    {destination : Place} {target : Option BasicBlockIdx} {unwind : UnwindAction}
    {func : Operand} {calleeRetDecl : LocalDecl}
    (hbb : curBody.basicBlocks[s.frame.blockIdx]? = some bb)
    (heq : s.frame.stmtIdx = bb.statements.length)
    (hk : bb.terminator.kind = .call func argOps destination target unwind)
    (hstale : StaleOk curBody s.frame.locals view s.frame.blockIdx bb.statements.length)
    (hmvT : termReadsOk (movedBefore curBody s.frame.blockIdx bb.statements.length)
      bb.terminator = true)
    (hliveInv : LiveInv curBody s.frame)
    (htupleInv : TupleInv curBody s.frame)
    (hdest : callDestOk curBody.localDecls
      (mustLiveBefore curBody s.frame.blockIdx bb.statements.length)
      (tupleInitBefore curBody s.frame.blockIdx bb.statements.length)
      calleeRetDecl destination = true) :
    (s.frame.locals[destination.local_]? ≠ some .dead ∧
      view[destination.local_]? ≠ some .dead) ∧
    ((∃ dst d, destination = ⟨dst, []⟩ ∧
        curBody.localDecls[dst]? = some d ∧ sameFragmentTy d.ty calleeRetDecl.ty = true) ∨
     (∃ dst fTy d it sc0 sc1, destination = ⟨dst, [.field 0 fTy]⟩ ∧
        curBody.localDecls[dst]? = some d ∧
        intBoolTupleOf d.ty = some it ∧ intTypeOf fTy = some it ∧
        intTypeOf calleeRetDecl.ty = some it ∧
        s.frame.locals[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
        view[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1]))) ∨
     (∃ dst fTy d it sc0 sc1, destination = ⟨dst, [.field 1 fTy]⟩ ∧
        curBody.localDecls[dst]? = some d ∧
        intBoolTupleOf d.ty = some it ∧ isBoolTy fTy = true ∧
        isBoolTy calleeRetDecl.ty = true ∧
        s.frame.locals[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) ∧
        view[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])))) := by
  have _ := hbb
  match destination, hk, hdest with
  | ⟨dst, []⟩, _, hdest =>
    simp only [callDestOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hdest
    obtain ⟨⟨_, hlv⟩, hdMatch⟩ := hdest
    rw [← heq] at hlv
    have haLive := hliveInv dst hlv
    have hvLive : view[dst]? ≠ some .dead := fun hd => haLive ((hstale.dead_iff dst).mpr hd)
    cases hd : curBody.localDecls[dst]? with
    | none => simp [hd] at hdMatch
    | some d =>
      rw [hd] at hdMatch
      exact ⟨⟨haLive, hvLive⟩, .inl ⟨dst, d, rfl, hd, hdMatch⟩⟩
  | ⟨dst, [.field 0 fTy]⟩, hk, hdest =>
    simp only [callDestOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hdest
    obtain ⟨⟨⟨_, hlv⟩, hti⟩, hdMatch⟩ := hdest
    rw [← heq] at hlv hti
    have haLive := hliveInv dst hlv
    have hvLive : view[dst]? ≠ some .dead := fun hd => haLive ((hstale.dead_iff dst).mpr hd)
    obtain ⟨sc0, sc1, haTup⟩ := htupleInv dst hti
    have hnotMo : dst ∉ movedBefore curBody s.frame.blockIdx bb.statements.length := by
      simp only [termReadsOk, hk, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hmvT
      exact hmvT.1
    have hvTup : view[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) :=
      (hstale.agree hnotMo).symm.trans haTup
    cases hd : curBody.localDecls[dst]? with
    | none => simp [hd] at hdMatch
    | some d =>
      rw [hd] at hdMatch
      cases ht : intBoolTupleOf d.ty with
      | none => simp [ht] at hdMatch
      | some it =>
        cases hf : intTypeOf fTy with
        | none => simp [ht, hf] at hdMatch
        | some fit =>
          cases hr : intTypeOf calleeRetDecl.ty with
          | none => simp [ht, hf, hr] at hdMatch
          | some rit =>
            simp only [ht, hf, hr, Bool.and_eq_true, decide_eq_true_eq] at hdMatch
            obtain ⟨h1, h2⟩ := hdMatch
            exact ⟨⟨haLive, hvLive⟩,
              .inr (.inl ⟨dst, fTy, d, it, sc0, sc1, rfl, hd, ht, h1 ▸ hf,
                by simp [h2], haTup, hvTup⟩)⟩
  | ⟨dst, [.field 1 fTy]⟩, hk, hdest =>
    simp only [callDestOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hdest
    obtain ⟨⟨⟨_, hlv⟩, hti⟩, hdMatch⟩ := hdest
    rw [← heq] at hlv hti
    have haLive := hliveInv dst hlv
    have hvLive : view[dst]? ≠ some .dead := fun hd => haLive ((hstale.dead_iff dst).mpr hd)
    obtain ⟨sc0, sc1, haTup⟩ := htupleInv dst hti
    have hnotMo : dst ∉ movedBefore curBody s.frame.blockIdx bb.statements.length := by
      simp only [termReadsOk, hk, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hmvT
      exact hmvT.1
    have hvTup : view[dst]? = some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) :=
      (hstale.agree hnotMo).symm.trans haTup
    cases hd : curBody.localDecls[dst]? with
    | none => simp [hd] at hdMatch
    | some d =>
      rw [hd] at hdMatch
      cases ht : intBoolTupleOf d.ty with
      | none => simp [ht] at hdMatch
      | some it =>
        cases hf : isBoolTy fTy with
        | false => simp [ht, hf] at hdMatch
        | true =>
          cases hr : isBoolTy calleeRetDecl.ty with
          | false => simp [ht, hf, hr] at hdMatch
          | true =>
            exact ⟨⟨haLive, hvLive⟩,
              .inr (.inr ⟨dst, fTy, d, it, sc0, sc1, rfl, hd, ht, hf,
                by simp, haTup, hvTup⟩)⟩
  | ⟨_, [.field (_ + 2) _]⟩, _, hdest => simp [callDestOk] at hdest
  | ⟨_, [.deref]⟩, _, hdest | ⟨_, [.index _]⟩, _, hdest | ⟨_, [.constantIndex _ _ _]⟩, _, hdest
  | ⟨_, [.subslice _ _ _]⟩, _, hdest | ⟨_, [.downcast _ _]⟩, _, hdest
  | ⟨_, [.opaqueCast _]⟩, _, hdest | ⟨_, _ :: _ :: _⟩, _, hdest =>
    simp [callDestOk] at hdest

private theorem callTerminatorOk_unpack {fnMap : FnMap}
    {callees : List CapturedMir} {curBody : CapturedMir} {blk nc1 nc2 : Nat}
    {bb : BasicBlockData} {tbTerm : Gen.Terminator}
    {ex1 : List (Gen.BbName × Gen.BasicBlock)}
    (hbb : curBody.basicBlocks[blk]? = some bb)
    (hok : callTerminatorOk callees curBody blk bb.terminator = true)
    (htr : translateTerminatorInProg fnMap curBody.localDecls nc1 bb.terminator =
      some (tbTerm, nc2, ex1)) :
    ∃ func argOps destination targetBb unwind dp callee calleeRetDecl restDecls
        fn conv argExprs retExpr unwindBb,
      bb.terminator.kind = .call func argOps destination (some targetBb) unwind ∧
      extractFnDefPath func = some dp ∧
      MirSemantics.findCallee? callees dp = some callee ∧
      callee.localDecls = calleeRetDecl :: restDecls ∧
      targetBb < curBody.basicBlocks.length ∧
      argOps.length = callee.argCount ∧
      callee.argCount ≤ restDecls.length ∧
      callArgsOk curBody.localDecls (restDecls.take callee.argCount) argOps = true ∧
      callDestOk curBody.localDecls (mustLiveBefore curBody blk bb.statements.length)
        (tupleInitBefore curBody blk bb.statements.length) calleeRetDecl destination = true ∧
      (∀ op ∈ argOps, opRead op ≠ some destination.local_) ∧
      lookupFnTarget fnMap dp = some (fn, conv) ∧
      lookupFnName fnMap dp = some fn ∧
      argOps.mapM translateCallArg = some argExprs ∧
      translatePlace destination = some retExpr ∧
      tbTerm = .Call (fnPtrExpr fn) conv argExprs retExpr (some (bbName targetBb))
        (some unwindBb) := by
  unfold callTerminatorOk at hok
  rw [hbb] at hok
  cases htk : bb.terminator.kind with
  | call func argOps destination target unwind =>
    rw [htk] at hok
    cases target with
    | none => simp at hok
    | some targetBb =>
      cases hextr : extractFnDefPath func with
      | none => simp [hextr] at hok
      | some dp =>
        cases hfind : MirSemantics.findCallee? callees dp with
        | none => simp [hextr, hfind] at hok
        | some callee =>
          cases hcd : callee.localDecls with
          | nil => simp [hextr, hfind, hcd] at hok
          | cons calleeRetDecl restDecls =>
            simp only [hextr, hfind, hcd, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true, bne_iff_ne] at hok
            obtain ⟨⟨⟨⟨⟨⟨⟨htgtLt, _⟩, _⟩, hArgLen⟩, hArgBound⟩, hArgsOk⟩, hDestOk⟩, hNotDst⟩ := hok
            simp only [translateTerminatorInProg, htk, hextr, Option.bind_eq_bind,
              Option.bind_some] at htr
            cases hlk : lookupFnTarget fnMap dp with
            | none => simp [hlk] at htr
            | some fnConv =>
              obtain ⟨fn, conv⟩ := fnConv
              cases htrArgs : argOps.mapM translateCallArg with
              | none => simp [hlk, htrArgs] at htr
              | some argExprs =>
                cases hretTr : translatePlace destination with
                | none => simp [hlk, htrArgs, hretTr] at htr
                | some retExpr =>
                  simp [hlk, htrArgs, hretTr] at htr
                  obtain ⟨rfl, _, _⟩ := htr
                  exact ⟨func, argOps, destination, targetBb, unwind, dp, callee, calleeRetDecl,
                    restDecls, fn, conv, argExprs, retExpr, (translateUnwindAction nc1 unwind).1,
                    rfl, hextr, hfind, hcd, htgtLt, hArgLen, hArgBound, hArgsOk, hDestOk,
                    hNotDst, hlk, lookupFnName_of_lookupFnTarget hlk, htrArgs, hretTr, rfl⟩
  | _ => simp [htk] at hok

private theorem list_mapM_option_spec {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      ys.length = xs.length ∧
      ∀ (j : Nat) x, xs[j]? = some x → ∃ y, f x = some y ∧ ys[j]? = some y
  | [], ys, h => by
    simp at h; subst h; exact ⟨rfl, fun _ _ hx => by simp at hx⟩
  | x0 :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hy0 : f x0 with
    | none => simp [hy0] at h
    | some y0 =>
      cases hys : xs.mapM f with
      | none => simp [hy0, hys] at h
      | some ys' =>
        simp [hy0, hys] at h
        subst h
        obtain ⟨hl, hg⟩ := list_mapM_option_spec f xs ys' hys
        refine ⟨by simp [hl], fun j x hx => ?_⟩
        cases j with
        | zero => simp at hx; subst hx; exact ⟨y0, hy0, rfl⟩
        | succ j => simp at hx; exact hg j x hx

/-- **Multi-frame step correspondence (`MR-4.1`).** For a multi-function
program `(entry, callees)` in `progInFragment` translated to `prog`, one Anneal
MIR step (`stepMirFn entry s`) and `k ≥ 1` MiniRust steps correspond in the
sense of `MultiStepRel`:
* intra-frame statements (`Assign`, `PlaceMention`, `StorageLive`,
  `StorageDead`, `Deinit`), `Goto`, `SwitchInt`, `Unreachable`, and `Return`
  (both to a suspended caller frame and from the root `entry` frame) correspond
  in `1` MiniRust step;
* `TerminatorKind.call` with UB in argument evaluation raises UB in `1`
  MiniRust step;
* `TerminatorKind.call` with valid arguments executes `Terminator::Call` (`1`
  step) followed by the callee's `initBlock` (`initLen callee` steps), reaching
  a `MultiStateRel`-related state at `(0, 0)` of `callee` in `1 + initLen callee`
  MiniRust steps. -/
theorem multi_step_correspondence (entry : CapturedMir) (callees : List CapturedMir)
    (prog : Gen.Program) (hfrag : progInFragment entry callees = true)
    (hprog : translateProg entry callees = some prog)
    (rootCtx : Ctx) (s : MachineState) (m : Mach)
    (hrel : MultiStateRel entry callees prog rootCtx s m) :
    MultiStepRel entry callees prog rootCtx s (stepMirFn entry s) m := by
  obtain ⟨view, hrel⟩ := hrel
  obtain ⟨hnd, hallFrag, _⟩ := progInFragment_spec hfrag
  let fnMap := fnNameMap entry callees
  let curBody := s.memory.activeCallee.getD entry
  obtain ⟨callerFrames, curCtx, curFn, curLm, candBound, remFuel, curBudget,
    hCurMem, hCurFn, hStackRel, hCurPay, hCurCand, hCurBud, hCandBudLt, hthr, hlo⟩ := hrel.stack
  obtain ⟨hphase, hargs, _, _, hbbs, hsdOk, hmvOk, hmtOk, hlvOk, htiOk⟩ :=
    bodyInProgFragment_spec (hallFrag curBody hCurMem)
  obtain ⟨hfCur, _, _, _, _, hBlocksCur⟩ := translateFnInProg_spec fnMap curBody curFn hCurFn
  obtain ⟨curBodyLenLe, _⟩ := maxStackLocalsAux_ge hCurBud
  have curBodyLenLe' : curBody.localDecls.length ≤ curBudget := curBodyLenLe
  have hCandCurLt : candBound + curBody.localDecls.length < 2 ^ 31 := by omega
  obtain ⟨bb, hbb⟩ : ∃ bb, curBody.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hrel.blk⟩
  have hbbmem : bb ∈ curBody.basicBlocks := List.mem_of_getElem? hbb
  obtain ⟨_, hstmts, htermOr⟩ := hbbs s.frame.blockIdx bb hbb
  obtain ⟨tbStmts, tbTerm, nc1, nc2, ex1, hstMapM, htermTr, hgetb⟩ :=
    hBlocksCur s.frame.blockIdx bb hbb
  let tb : Gen.BasicBlock := ⟨tbStmts, tbTerm, .Regular⟩
  obtain ⟨hlen, hstspec⟩ := list_mapM_option_spec (translateStatement curBody.localDecls)
    bb.statements tbStmts hstMapM
  obtain ⟨hmvS, hmvT, hmvEdge⟩ := movesOk_spec hmvOk hbb
  have hshape : Shape m rootCtx
      (callerFrames ++ [calleeFrameL curFn curCtx curLm s.frame.blockIdx s.frame.stmtIdx])
      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
  let mR := rethread (resetPick m) curCtx
    [curCtx.caller, calleeFrameL curFn curCtx curLm s.frame.blockIdx s.frame.stmtIdx]
  have hframe : FrameOk curBody curFn curCtx view curLm mR s.frame.blockIdx s.frame.stmtIdx :=
    ⟨hfCur, ⟨rfl, rfl, rfl⟩, hlo⟩
  have hslotsA : SlotsOk curBody.localDecls s.frame.locals := hrel.stale.slots hlo.slots
  have hnA : s.frame.locals.length = curBody.localDecls.length := hrel.stale.1.trans hlo.nlocals
  have hstmt_le := hrel.stmt bb hbb
  rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with hlt | hge
  · ----------------------------------------------------------------- statement
    have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
      rw [hlen]; omega
    obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hstmem : st ∈ bb.statements := List.mem_of_getElem? hst
    obtain ⟨st', hst', htst⟩ := hstspec _ st hst
    rw [stepMirFn_active_stmt entry curBody s bb st rfl hphase hbb hst]
    have hok := hstmts st hstmem
    have hreads := hmvS _ st hst
    rcases translateStatement_some hst' with ⟨i, rv, e, hkind, he, rfl⟩ | ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨i, hkind, rfl⟩ | ⟨i, hkind, rfl⟩ | ⟨p, pe, hkind, hpe, rfl⟩
    · ------------------------------------------------------------ assign
      have hreadsMo : readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx)
          (rvOperands rv) = true := by
        simpa [stmtReadsOk, hkind] using hreads
      have hr0 : readsOk [] (rvOperands rv) = true :=
        readsOk_mono (fun _ h => by simp at h) hreadsMo
      have hagree := hrel.stale.readsAgree hreadsMo
      have hal : i ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals, hkind])
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      simp only [statementOk] at hok
      cases hdi : curBody.localDecls[i]? with
      | none => simp [hdi] at hok
      | some d =>
        have hi : i < s.frame.locals.length := by
          rw [hnA]; exact (List.getElem?_eq_some_iff.mp hdi).1
        obtain ⟨res, hk, hMok, hMnone, hAok, hAnone⟩ : ∃ res : Option Value, moveKind rv = true ∧
            (∀ v, res = some v → view[i]? ≠ some .dead →
              ∃ m3R, evalStatement mR (.Assign (.Local (localName i)) e) = .ok m3R ∧
                FrameOk curBody curFn curCtx (view.set i (.init v)) curLm m3R
                  s.frame.blockIdx s.frame.stmtIdx) ∧
            (res = none → view[i]? ≠ some .dead →
              ∃ msg, evalStatement mR (.Assign (.Local (localName i)) e) = .error (.ub msg)) ∧
            (∀ v, res = some v →
              evalRvalue s.frame.locals (copyRv rv) s.memory curBody.localDecls curBody.layouts =
                .ok v s.frame.locals s.memory) ∧
            (res = none →
              evalRvalue s.frame.locals (copyRv rv) s.memory curBody.localDecls curBody.layouts =
                .ub) := by
          cases htup : intBoolTupleOf d.ty with
          | some it =>
            have hb := intBoolTupleOf_isBoolTy htup
            have ho := intBoolTupleOf_isOrderingTy htup
            have hitd : itOf d = it := (tyOf_tuple htup).2
            have htup' : intBoolTupleOf d.ty = some (itOf d) := by rw [hitd]; exact htup
            have hokT : rvalueOkTuple curBody.localDecls (itOf d) (copyRv rv) = true := by
              rw [hitd]; simpa [hdi, hb, ho, htup] using hok
            have hgood := hframe.decl_good i d hdi
            have hfr : rvTupleBits s.frame.locals (itOf d) (copyRv rv) =
                rvTupleBits view (itOf d) (copyRv rv) := rvTupleBits_frame hagree
            obtain ⟨hA1, hA2⟩ := evalRvalue_fragTuple curBody.localDecls s.frame.locals hslotsA hnA
              (itOf d) hgood (copyRv rv) hokT s.memory curBody.layouts
            refine ⟨(rvTupleBits view (itOf d) (copyRv rv)).map
                (fun pr => .aggregate 0 [.scalar ⟨pr.1, (itOf d).size.bytes⟩, .scalar ⟨pr.2, 1⟩]),
              moveKind_of_rvalueOkTuple hokT, ?_, ?_, ?_, ?_⟩
            · intro v hv hlive
              obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
              exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv) hokT e he).1
                bits b hpb
            · intro hv hlive
              exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv) hokT e he).2
                (Option.map_eq_none_iff.mp hv)
            · intro v hv
              obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
              exact hA1 bits b (hfr.trans hpb)
            · intro hv
              exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
          | none =>
            cases hb : isBoolTy d.ty with
            | true =>
              have hit : itOf d = u8Ty := (tyOf_bool hb).2
              have hokB : rvalueOkB curBody.localDecls (copyRv rv) = true := by
                simpa [hdi, hb] using hok
              have hfr : rvBitsB curBody.localDecls s.frame.locals (copyRv rv) =
                  rvBitsB curBody.localDecls view (copyRv rv) := rvBitsB_frame hagree
              obtain ⟨hA1, hA2⟩ := evalRvalue_fragB curBody.localDecls s.frame.locals hslotsA hnA
                (copyRv rv) hokB s.memory curBody.layouts
              refine ⟨(rvBitsB curBody.localDecls view (copyRv rv)).map
                  (fun r => .scalar ⟨r, (itOf d).size.bytes⟩),
                moveKind_of_rvalueOkB hokB, ?_, ?_, ?_, ?_⟩
              · intro v hv hlive
                obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                exact (evalStatement_assignB hframe i d hdi hlive hb (copyRv rv) hokB e he).1 r hr
              · intro hv hlive
                exact (evalStatement_assignB hframe i d hdi hlive hb (copyRv rv) hokB e he).2
                  (Option.map_eq_none_iff.mp hv)
              · intro v hv
                obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                rw [hit]; exact hA1 r (hfr.trans hr)
              · intro hv
                exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
            | false =>
              cases ho : isOrderingTy d.ty with
              | true =>
                have hit : itOf d = u8Ty := (tyOf_ordering ho).2
                have hokO : rvalueOkO curBody.localDecls (copyRv rv) = true := by
                  simpa [hdi, hb, ho] using hok
                have hfr : rvBitsO curBody.localDecls s.frame.locals (copyRv rv) =
                    rvBitsO curBody.localDecls view (copyRv rv) := rvBitsO_frame hagree
                obtain ⟨hA1, hA2⟩ := evalRvalue_fragO curBody.localDecls s.frame.locals hslotsA hnA
                  (copyRv rv) hokO s.memory curBody.layouts
                refine ⟨(rvBitsO curBody.localDecls view (copyRv rv)).map
                    (fun r => .scalar ⟨r, (itOf d).size.bytes⟩),
                  moveKind_of_rvalueOkO hokO, ?_, ?_, ?_, ?_⟩
                · intro v hv hlive
                  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                  exact (evalStatement_assignO hframe i d hdi hlive ho (copyRv rv) hokO e he).1 r hr
                · intro hv hlive
                  exact (evalStatement_assignO hframe i d hdi hlive ho (copyRv rv) hokO e he).2
                    (Option.map_eq_none_iff.mp hv)
                · intro v hv
                  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                  rw [hit]; exact hA1 r (hfr.trans hr)
                · intro hv
                  exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
              | false =>
                cases hit : intTypeOf d.ty with
                | none => simp [hdi, hb, ho, htup, hit] at hok
                | some it =>
                  have hitd : itOf d = it := (tyOf_int hit).2
                  have hok' : rvalueOk curBody.localDecls (itOf d) (copyRv rv) = true := by
                    rw [hitd]; simpa [hdi, hb, ho, htup, hit] using hok
                  have hint : intTypeOf d.ty = some (itOf d) := by rw [hitd]; exact hit
                  have hgood := hframe.decl_good i d hdi
                  have hfr : rvBits curBody.localDecls s.frame.locals (itOf d) (copyRv rv) =
                      rvBits curBody.localDecls view (itOf d) (copyRv rv) := rvBits_frame hagree
                  obtain ⟨hA1, hA2⟩ := evalRvalue_frag curBody.localDecls s.frame.locals hslotsA hnA
                    (itOf d) hgood (copyRv rv) hok' s.memory curBody.layouts
                  refine ⟨(rvBits curBody.localDecls view (itOf d) (copyRv rv)).map
                      (fun r => .scalar ⟨r, (itOf d).size.bytes⟩),
                    moveKind_of_rvalueOk hok', ?_, ?_, ?_, ?_⟩
                  · intro v hv hlive
                    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                    exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv) hok' e he).1
                      r hr
                  · intro hv hlive
                    exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv) hok' e he).2
                      (Option.map_eq_none_iff.mp hv)
                  · intro v hv
                    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                    exact hA1 r (hfr.trans hr)
                  · intro hv
                    exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
        obtain ⟨hA1, hA2⟩ := evalStmt_assign_move s curBody.localDecls curBody.layouts i rv span
          hk hr0 hi hrel.borrows hrel.protectors
        by_cases hdead : s.frame.locals[i]? = some .dead
        · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
          obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
          have hA : evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ curBody.localDecls curBody.layouts =
              MirStepNode.fail .ub := by
            cases hres : res with
            | none => exact hA2 (hAnone hres)
            | some v => exact (hA1 v (hAok v hres)).2 hdead
          rw [hA]
          exact MultiStepRel.ub' msg (lift_stmt_ub hshape hgetb hne htst hmsg)
        · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
          cases hres : res with
          | none =>
            rw [hA2 (hAnone hres)]
            obtain ⟨msg, hmsg⟩ := hMnone hres hlive
            exact MultiStepRel.ub' msg (lift_stmt_ub hshape hgetb hne htst hmsg)
          | some v =>
            rw [(hA1 v (hAok v hres)).1 hdead]
            obtain ⟨m3R, hm3R, h3⟩ := hMok v hres hlive
            obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
              lift_stmt_ok hshape hgetb hne htst hm3R h3
            have hvil : i < view.length := by rw [← hrel.stale.1]; exact hi
            have hvOk : SlotOk (tyOf d) (.init v) :=
              hlo4.slots i d (.init v) hdi (List.getElem?_set_self hvil)
            exact MultiStepRel.tau1 m4 hstep
              (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
                _ (view.set i (.init v)) _ m4 hsh4.threads hsh4.active hp4 hfp4 hlo4
                (hrel.stale.assign hbb hst rfl (.init v))
                (retLive_set hrel.retLive i (by simp))
                (hrel.liveInv.advance_assign hbb hst rfl)
                (hrel.tupleInv.advance_assign hbb hst rfl hdi hi hvOk)
                rfl rfl rfl rfl rfl rfl)
    · ------------------------------------------------------------ placeMention
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      have hpOk : placeOk curBody.localDecls p = true := by simpa [statementOk] using hok
      have hal : p.local_ ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      obtain ⟨hpl, hMlive, hMdead⟩ := evalStatement_placeMention_place hframe p hpOk pe hpe
      by_cases hdead : s.frame.locals[p.local_]? = some .dead
      · rw [evalStmt_placeMention_dead s curBody.localDecls curBody.layouts p span hdead]
        obtain ⟨msg, hmsg⟩ := hMdead ((hrel.stale.dead_iff _).mp hdead) hal
        exact MultiStepRel.ub' msg (lift_stmt_ub hshape hgetb hne htst hmsg)
      · have hlive : view[p.local_]? ≠ some .dead :=
          fun h => hdead ((hrel.stale.dead_iff _).mpr h)
        rw [evalStmt_placeMention_place s curBody.localDecls curBody.layouts p span
          hslotsA hnA hpl hdead]
        obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
          lift_stmt_ok hshape hgetb hne htst (hMlive hlive) hframe
        exact MultiStepRel.tau1 m4 hstep
          (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
            _ view _ m4 hsh4.threads hsh4.active hp4 hfp4 hlo4
            (hrel.stale.keep hbb hst rfl) hrel.retLive
            (hrel.liveInv.advance_placeMention hbb hst rfl)
            (hrel.tupleInv.advance_placeMention hbb hst rfl)
            rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ storageLive
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      have hin : i < curBody.localDecls.length := by simpa [statementOk] using hok
      have hal : i ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      obtain ⟨d, hd⟩ : ∃ d, curBody.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageLive s curBody.localDecls curBody.layouts i span hi]
      obtain ⟨m3R, lm3, hm3R, h3⟩ :=
        evalStatement_storageLive_cand hframe i d hd hal hCurCand hCandCurLt
      obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
        lift_stmt_ok hshape hgetb hne htst hm3R h3
      exact MultiStepRel.tau1 m4 hstep
        (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
          _ (view.set i .uninit) _ m4 hsh4.threads hsh4.active hp4 hfp4 hlo4
          (hrel.stale.setBoth hbb hst rfl .uninit)
          (retLive_set hrel.retLive i (by simp))
          (hrel.liveInv.advance_storageLive hbb hst rfl hi)
          (hrel.tupleInv.advance_clear hbb hst (by simp [stmtTupleInit]))
          rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ storageDead
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      have hin : i < curBody.localDecls.length := by simpa [statementOk] using hok
      have hal : i ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      have hi0 : curBody.argCount < i := storageDeadOk_spec hsdOk hbbmem hstmem rfl
      obtain ⟨d, hd⟩ : ∃ d, curBody.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageDead s curBody.localDecls curBody.layouts i span hi]
      obtain ⟨m3R, hm3R, h3⟩ := evalStatement_storageDead hframe i d hd hal
      obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
        lift_stmt_ok hshape hgetb hne htst hm3R h3
      exact MultiStepRel.tau1 m4 hstep
        (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
          _ (view.set i .dead) _ m4 hsh4.threads hsh4.active hp4 hfp4 hlo4
          (hrel.stale.setBoth hbb hst rfl .dead)
          (by rw [List.getElem?_set_ne (by omega)]; exact hrel.retLive)
          (hrel.liveInv.advance_storageDead hbb hst rfl)
          (hrel.tupleInv.advance_clear hbb hst (by simp [stmtTupleInit]))
          rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ deinit
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      obtain ⟨i, proj⟩ := p
      cases proj with
      | cons _ _ => simp [statementOk] at hok
      | nil =>
        have hin : i < curBody.localDecls.length := by simpa [statementOk] using hok
        simp only [translatePlace, Option.some.injEq] at hpe; subst hpe
        have hal : i ∉ alwaysStorageLiveLocals curBody :=
          mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
        obtain ⟨d, hd⟩ : ∃ d, curBody.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
        have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
        obtain ⟨hMlive, hMdead⟩ := evalStatement_deinit hframe i d hd
        obtain ⟨hAlive, hAdead⟩ := evalStmt_deinit s curBody.localDecls curBody.layouts i span hi
        by_cases hdead : s.frame.locals[i]? = some .dead
        · rw [hAdead hdead]
          obtain ⟨msg, hmsg⟩ := hMdead ((hrel.stale.dead_iff i).mp hdead) hal
          exact MultiStepRel.ub' msg (lift_stmt_ub hshape hgetb hne htst hmsg)
        · rw [hAlive hdead]
          obtain ⟨m3R, hm3R, h3⟩ := hMlive (fun h => hdead ((hrel.stale.dead_iff i).mpr h))
          obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
            lift_stmt_ok hshape hgetb hne htst hm3R h3
          exact MultiStepRel.tau1 m4 hstep
            (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
              _ (view.set i .uninit) _ m4 hsh4.threads hsh4.active hp4 hfp4 hlo4
              (hrel.stale.setBoth hbb hst rfl .uninit)
              (retLive_set hrel.retLive i (by simp))
              (hrel.liveInv.advance_deinit hbb hst rfl)
              (hrel.tupleInv.advance_clear hbb hst (by simp [stmtTupleInit]))
              rfl hrel.borrows rfl rfl rfl rfl)
  · ----------------------------------------------------------------- terminator
    have heq : s.frame.stmtIdx = bb.statements.length := by omega
    have hif : ((s.frame.stmtIdx : Nat) : Int) = (tb.statements.length : Int) := by
      rw [hlen, heq]
    rw [stepMirFn_active_term entry curBody s bb rfl hphase hbb heq]
    have hstale_end : StaleOk curBody s.frame.locals view s.frame.blockIdx bb.statements.length := by
      rw [← heq]; exact hrel.stale
    rcases htermOr with hterm | hcallOk
    · ----------------------------------------------------- non-call terminators
      have htermspec : translateTerminator curBody.localDecls bb.terminator = some tb.terminator := by
        cases htk : bb.terminator.kind with
        | call _ _ _ _ _ => simp [terminatorOk, htk] at hterm
        | _ =>
          simp only [translateTerminatorInProg, htk, Option.bind_eq_bind] at htermTr
          cases ht : translateTerminator curBody.localDecls bb.terminator with
          | none => simp [ht] at htermTr
          | some tr =>
            simp [ht] at htermTr
            rcases htermTr with ⟨rfl, _, _⟩
            rfl
      rcases translateTerminator_some htermspec with
        ⟨t, hk, htt⟩ | ⟨discr, targets, hk⟩ | ⟨hk, htt⟩ | ⟨hk, htt⟩
      · ------------------------------------------------------------ goto
        have ht : t < curBody.basicBlocks.length := by simpa [terminatorOk, hk] using hterm
        have hjmp := jumpToBlock_append (resetPick_shape hshape) t
        let m3 := rethread (resetPick m) rootCtx
          (callerFrames ++ [calleeFrameL curFn curCtx curLm t 0])
        have hsh3 : Shape m3 rootCtx (callerFrames ++ [calleeFrameL curFn curCtx curLm t 0])
            m.mem.memory.allocations := ⟨rfl, rfl, rfl⟩
        have hstep : Interp.step m = .ok m3 := by
          rw [step_callee_stack hshape tb hgetb]
          simp [hif, htt, Interp.evalTerminator, hjmp, check_after hsh3, m3]
        have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
            MirStepNode.step (jumpState s t s.frame.locals) := by
          simp [MirSemantics.evalTerminator, hk, jumpState]
        have htMem : t ∈ termTargets bb.terminator := by simp [termTargets, hk]
        have hsub : ∀ j ∈ movedBefore curBody s.frame.blockIdx bb.statements.length,
            j ∈ movedBefore curBody t 0 := by
          simpa [termTargets, termMoved, hk] using hmvEdge t htMem
        rw [hA]
        exact MultiStepRel.tau1 m3 hstep
          (hrel.jump hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
            t ht s.frame.locals m3 hsh3.threads hsh3.active rfl rfl hlo
            (hstale_end.toBlock hsub)
            (hrel.liveInv.jump_goto hlvOk hbb heq htMem)
            (hrel.tupleInv.jump_goto htiOk hbb heq hk))
      · ------------------------------------------------------------ switchInt
        obtain ⟨it, hit, hdok, hbr, hother⟩ := terminatorOk_switch hterm hk
        obtain ⟨⟨T, hT, hokT⟩, vExpr, htt, hMok, hMnone⟩ :=
          switch_spec hframe hk htermspec hit hdok
        have hreadsD : readsOk (movedBefore curBody s.frame.blockIdx bb.statements.length)
            [discr] = true := by
          simpa [termReadsOk, hk] using hmvT
        have hsimple : simpleOp discr = true := (readsOk_spec hreadsD discr (by simp)).1
        have hbitsEq : opBits s.frame.locals (copyOp discr) = opBits view (copyOp discr) :=
          opBits_frame _ (by
            rw [opRead_copyOp]
            exact fun j hj => hstale_end.agree ((readsOk_spec hreadsD discr (by simp)).2 j hj))
        obtain ⟨hAok, hAnone⟩ := evalOperand_fragT curBody.localDecls s.frame.locals hslotsA hnA hT
          (copyOp discr) hokT s.memory.borrows s.memory.globals curBody.layouts s.memory.callerLocals
        have hmove := evalOperand_move s.frame.locals discr hsimple s.memory.borrows
          s.memory.globals curBody.layouts s.memory.callerLocals
        obtain ⟨hvOkRe, hvErrRe⟩ := evalValue_rethread vExpr (resetPick m) rootCtx curCtx
          callerFrames (calleeFrameL curFn curCtx curLm s.frame.blockIdx s.frame.stmtIdx)
          hshape.threads rfl
        cases hb : opBits view (copyOp discr) with
        | none =>
          have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
              MirStepNode.fail .ub := by
            simp [MirSemantics.evalTerminator, hk, hmove, hAnone (hbitsEq.trans hb), opWithLocals]
          rw [hA]
          obtain ⟨msg, hmsgR⟩ := hMnone hb
          have hmsg := hvErrRe (.ub msg) hmsgR
          have hstep : Interp.step m = .error (.ub msg) := by
            rw [step_callee_stack hshape tb hgetb]
            simp [hif, htt, Interp.evalTerminator, hmsg]
          exact MultiStepRel.ub' msg hstep
        | some bits =>
          obtain ⟨hblt, m3R, hm3R, h3R⟩ := hMok bits hb
          obtain ⟨cm3, hcm3, hm3⟩ := hvOkRe _ m3R hm3R
          have hlookup := switch_lookup it bits hblt targets.branches (fun p hp => (hbr p hp).1)
            targets.otherwise
          have htgt := lookupSwitchTarget_lt bits targets.branches targets.otherwise
            curBody.basicBlocks.length (fun p hp => (hbr p hp).2) hother
          let tgt := MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise
          have htgtMem : tgt ∈ termTargets bb.terminator := by
            rw [termTargets, hk]
            exact lookupSwitchTarget_mem bits targets.branches targets.otherwise
          have hsub : ∀ j ∈ moveOut (movedBefore curBody s.frame.blockIdx bb.statements.length) discr,
              j ∈ movedBefore curBody tgt 0 := by
            simpa [termMoved, hk] using hmvEdge tgt htgtMem
          have hsh3 : Shape { resetPick m with mem := cm3 } rootCtx
              (callerFrames ++ [calleeFrameL curFn curCtx curLm s.frame.blockIdx s.frame.stmtIdx])
              cm3.memory.allocations := ⟨hshape.threads, rfl, rfl⟩
          have hjmp := jumpToBlock_append hsh3 tgt
          let m4 := rethread { resetPick m with mem := cm3 } rootCtx
            (callerFrames ++ [calleeFrameL curFn curCtx curLm tgt 0])
          have hsh4 : Shape m4 rootCtx (callerFrames ++ [calleeFrameL curFn curCtx curLm tgt 0])
              cm3.memory.allocations := ⟨rfl, rfl, rfl⟩
          have halloc3 : cm3.memory.allocations = m3R.mem.memory.allocations := by
            rw [hcm3]
          have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
              MirStepNode.emitStep (.event bits)
                (jumpState s tgt (opPost s.frame.locals discr)) := by
            simp [MirSemantics.evalTerminator, hk, hmove, hAok bits (hbitsEq.trans hb),
              opWithLocals, jumpState, tgt]
          rw [hA]
          have hM : Interp.evalTerminator (resetPick m) tb.terminator = .ok m4 := by
            rw [htt]
            simp only [Interp.evalTerminator, hm3, ok_bind]
            rw [hlookup]
            exact hjmp
          have hstep : Interp.step m = .ok m4 := by
            rw [step_callee_stack hshape tb hgetb]
            simp [hif, hM, check_after hsh4]
          exact MultiStepRel.emit' _ m4 rfl hstep
            (hrel.jump hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
              tgt htgt (opPost s.frame.locals discr) m4 hsh4.threads hsh4.active rfl rfl
              (by simpa [m4, rethread, halloc3] using h3R.locs)
              (hstale_end.toBlockMove discr hsub)
              (hrel.liveInv.jump_switchInt hlvOk hbb heq htgtMem)
              (hrel.tupleInv.jump_switchInt htiOk hbb heq hk htgtMem))
      · ------------------------------------------------------------ unreachable
        have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
            MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk]
        rw [hA]
        have hstep : Interp.step m = .error (.ub "reached unreachable code") := by
          rw [step_callee_stack hshape tb hgetb]
          simp [hif, htt, Interp.evalTerminator, ub]
        exact MultiStepRel.ub' "reached unreachable code" hstep
      · ------------------------------------------------------------ return
        have hn0 : 0 < curBody.localDecls.length := by omega
        obtain ⟨d0, hd0⟩ : ∃ d, curBody.localDecls[0]? = some d := ⟨_, List.getElem?_eq_getElem hn0⟩
        have h0mo : 0 ∉ movedBefore curBody s.frame.blockIdx bb.statements.length := by
          simpa [termReadsOk, hk] using hmvT
        have h0eq : s.frame.locals[0]? = view[0]? := hstale_end.agree h0mo
        obtain ⟨slot0, hs0⟩ : ∃ slot, view[0]? = some slot :=
          ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hn0)⟩
        have hslot0 := hlo.slots 0 d0 slot0 hd0 hs0
        have hsA : s.frame.locals[0]? = some slot0 := h0eq.trans hs0
        cases hcs : s.memory.callStack with
        | nil =>
          rw [hcs] at hStackRel
          obtain ⟨hcfEq, hCurEq, hCtxEq, _, _, hRetRoot⟩ := hStackRel.inv_nil
          have hshapeRoot : Shape m rootCtx
              [rootCtx.caller, calleeFrameL curFn rootCtx curLm s.frame.blockIdx s.frame.stmtIdx]
              m.mem.memory.allocations := by
            simpa [hcfEq, hCtxEq] using hshape
          have hloRoot : LocalsOk curBody rootCtx view curLm m.mem.memory.allocations :=
            hCtxEq ▸ hlo
          have hd0Entry : entry.localDecls[0]? = some d0 := hCurEq ▸ hd0
          obtain ⟨r0, a0, hp, hr0, hliveR, haddrr, hlenr, halr⟩ := hRetRoot d0 hd0Entry
          have hframeRoot : FrameOk curBody curFn rootCtx view curLm (resetPick m)
              s.frame.blockIdx s.frame.stmtIdx :=
            ⟨hfCur, resetPick_shape hshapeRoot, hloRoot⟩
          have hRet := evalReturn_frame hframeRoot d0 hd0 r0 a0 hp hr0 hliveR haddrr hlenr halr
          match slot0, hslot0, hs0, hsA with
          | .dead, _, hs0, _ => exact absurd hs0 hrel.retLive
          | .uninit, _, hs0, hsA =>
            have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
                MirStepNode.fail .ub := by
              simp [MirSemantics.evalTerminator, hk, get?, hsA]
            rw [hA]
            obtain ⟨msg, hmsg⟩ := hRet.2 hs0
            have hstep : Interp.step m = .error (.ub msg) := by
              rw [step_callee_stack hshape tb hgetb]
              simp [hif, htt, Interp.evalTerminator, hmsg]
            exact MultiStepRel.ub' msg hstep
          | .init v, hv0, hs0, hsA =>
            have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
                MirStepNode.retNormal v s.memory := by
              simp [MirSemantics.evalTerminator, hk, get?, hsA, hcs]
            rw [hA]
            obtain ⟨m', R, hm', hs', hR⟩ := hRet.1 v hs0
            have hstep : Interp.step m = .ok m' := by
              rw [step_callee_stack hshape tb hgetb]
              simp [hif, htt, Interp.evalTerminator, hm', check_after hs']
            exact MultiStepRel.ret' m' hstep
              ⟨r0, a0, d0, R, hd0Entry, hv0, hp, hr0, hs'.threads, hs'.allocs, hR⟩
        | cons savedCaller restStack =>
          rw [hcs] at hStackRel
          obtain ⟨preFrames, callerBody, callerFn, callerCtx, callerCandBound,
            callerView, callerLm, calleeRetDecl, callerBudget,
            hcfEq, hRest, hCallerEq, hCallerMem, hCallerFn, hProtNone, hCalleeProts,
            hTargetLt, hNextBlk, hCallerFrame, hCalleeRetDecl, hDest, hCallerCand,
            hCallerBudget, hCallerBudgetLt, hPostLen, hPostStale, hPostLive, hPostTuple⟩ :=
            hStackRel.inv_cons
          subst hcfEq
          have hTermEq : bb.terminator = ⟨.return_, bb.terminator.span⟩ := by
            cases hbt : bb.terminator with
            | mk kind span => rw [hbt] at hk; exact congrArg (MirAst.Terminator.mk · span) hk
          obtain ⟨hAokRet, hAubRet⟩ :=
            evalTerminator_return_caller_anneal (curBody := curBody) (span := bb.terminator.span)
              hcs hProtNone hCalleeProts hDest
          have hMRet :=
            evalReturn_caller_spec hfCur (resetPick_shape hshape) hCallerFrame hNextBlk
              hCalleeRetDecl hlo hrel.retLive hDest
          match slot0, hslot0, hs0, hsA with
          | .dead, _, hs0, _ => exact absurd hs0 hrel.retLive
          | .uninit, _, hs0, hsA =>
            rw [hTermEq, hAubRet (.inl hsA)]
            obtain ⟨msg, hmsg⟩ := hMRet.2 hs0
            have hstep : Interp.step m = .error (.ub msg) := by
              rw [step_callee_stack hshape tb hgetb]
              simp [hif, htt, Interp.evalTerminator, hmsg]
            exact MultiStepRel.ub' msg hstep
          | .init retVal, _, hs0, hsA =>
            rw [hTermEq, hAokRet retVal hsA]
            obtain ⟨callerView', m', hm', hsh', hp', hfp', hcvLen, hdstEq, hdstLive',
              hneView, hneAct, hloCaller⟩ := hMRet.1 retVal hs0
            have hstep : Interp.step m = .ok m' := by
              rw [step_callee_stack hshape tb hgetb]
              simp [hif, htt, Interp.evalTerminator, hm', check_after hsh']
            obtain ⟨_, hCallerArgs, _, _, _, hCallerSdOk, _, _, _, _⟩ :=
              bodyInProgFragment_spec (hallFrag callerBody hCallerMem)
            let postActual := writeCallDest savedCaller.frame.locals savedCaller.destination retVal
            have hStaleCaller : StaleOk callerBody postActual callerView'
                savedCaller.returnTarget 0 := by
              refine ⟨by rw [writeCallDest_length, hPostLen, hcvLen], fun j hjNe => ?_⟩
              by_cases hjDst : j = savedCaller.destination.local_
              · subst hjDst
                exact absurd hdstEq hjNe
              · rw [hneAct j hjDst, hneView j hjDst] at hjNe ⊢
                exact hPostStale j hjDst hjNe
            have hRetLiveCaller : callerView'[0]? ≠ some .dead := by
              by_cases h0Dst : (0 : Nat) = savedCaller.destination.local_
              · rwa [h0Dst]
              · have h0Mem := liveAtEntry_zero_mem hCallerArgs hCallerSdOk
                  savedCaller.returnTarget hTargetLt
                have ha0Live : postActual[0]? ≠ some .dead := by
                  rw [hneAct 0 h0Dst]
                  exact hPostLive 0 h0Mem h0Dst
                exact fun hd => ha0Live ((hStaleCaller.dead_iff 0).mpr hd)
            have hLiveCaller : LiveInv callerBody
                { savedCaller.frame with
                  blockIdx := savedCaller.returnTarget, stmtIdx := 0, locals := postActual } := by
              intro i hi
              simp only [mustLiveBefore_zero] at hi ⊢
              by_cases hiDst : i = savedCaller.destination.local_
              · subst hiDst
                rw [hdstEq]
                exact hdstLive'
              · rw [hneAct i hiDst]
                exact hPostLive i hi hiDst
            have hTupleCaller : TupleInv callerBody
                { savedCaller.frame with
                  blockIdx := savedCaller.returnTarget, stmtIdx := 0, locals := postActual } := by
              intro i hi
              simp only [tupleInitBefore_zero] at hi ⊢
              by_cases hiDst : i = savedCaller.destination.local_
              · subst hiDst
                have htupDst := tupleInitAtEntry_isTupleLocal callerBody savedCaller.returnTarget
                  savedCaller.destination.local_ hi
                obtain ⟨w, hwAct⟩ := hDest.writeCallDest_isInit retVal
                have hwView : callerView'[savedCaller.destination.local_]? = some (.init w) :=
                  hdstEq.symm.trans hwAct
                obtain ⟨sc0, sc1, rfl⟩ := slotOk_tuple_of_isTupleLocal htupDst
                  (fun d hd => hloCaller.slots _ d (.init w) hd hwView)
                exact ⟨sc0, sc1, hwAct⟩
              · rw [hneAct i hiDst]
                exact hPostTuple i hi hiDst
            refine MultiStepRel.tau1 m' hstep ⟨callerView', {
              stack := ?_
              env := hrel.env.of_eq hp' hfp'
              active := hsh'.active
              blk := by simpa [hCallerEq] using hTargetLt
              stmt := fun _ _ => Nat.zero_le _
              stale := by simpa [hCallerEq] using hStaleCaller
              retLive := hRetLiveCaller
              liveInv := by simpa [hCallerEq] using hLiveCaller
              tupleInv := by simpa [hCallerEq] using hTupleCaller
              calleesEq := hrel.calleesEq
              activeCalleeOk := ?_
              borrows := hrel.borrows
              protectors := rfl
              callerLocals := hrel.callerLocals }⟩
            · refine ⟨preFrames, callerCtx, callerFn, callerLm, callerCandBound,
                remFuel + 1, callerBudget, ?_⟩
              simp only [Option.getD_some, hCallerEq]
              exact ⟨hCallerMem, hCallerFn, hRest, hRest.payloads, hCallerCand,
                hCallerBudget, hCallerBudgetLt, hsh'.threads, hloCaller⟩
            · constructor
              · intro hrNil
                simp only at hrNil
                rw [hrNil] at hRest
                exact .inr (congrArg some (hCallerEq.trans hRest.nil_body_eq))
              · intro _
                exact ⟨savedCaller.callerBody, rfl⟩
    · ------------------------------------------------------------ call terminator
      obtain ⟨func, argOps, destination, targetBb, unwind, dp, callee, calleeRetDecl,
        restDecls, fn, conv, argExprs, retExpr, unwindBb,
        hk, hextr, hfind, hCalleeDecls, htgtLt, hArgLen, hArgBound, hArgsOk, hDestOk,
        hNotDst, hlkTgt, hlk, htrArgs, hretTr, htt⟩ :=
        callTerminatorOk_unpack hbb hcallOk htermTr
      have hfindS : MirSemantics.findCallee? s.memory.callees dp = some callee := by
        rwa [hrel.calleesEq]
      obtain ⟨idx, fCallee, hCalleeMem, hlkIdx, hlkTgtIdx, hfCallee, hgetCallee⟩ :=
        (translateProg_spec hnd hprog).2 dp callee hfind
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hlkTgt.symm.trans hlkTgtIdx))
      have hd0Callee : callee.localDecls[0]? = some calleeRetDecl := by simp [hCalleeDecls]
      have hCalleeArgc : callee.argCount + 1 ≤ callee.localDecls.length := by
        simp [hCalleeDecls]; omega
      have hpdsEq : restDecls.take callee.argCount =
          (callee.localDecls.drop 1).take callee.argCount := by
        simp [hCalleeDecls]
      obtain ⟨hdstLive, hdestEval⟩ :=
        callDestOk_evalSpec hbb heq hk hstale_end hmvT hrel.liveInv hrel.tupleInv hDestOk
      obtain ⟨retPlace, m1, view1, hplRet, hprepRet, hsh1, hp1, hfp1, hv1Ne, hv1Len, hDest1⟩ :=
        evalCallRet_spec (calleeRetDecl := calleeRetDecl) hfCur (resetPick_shape hshape) hlo
          hstale_end.1 hretTr hdstLive (by
            rcases hdestEval with
              ⟨dst, d, rfl, hd, hs⟩ |
              ⟨dst, fTy, d, it, sc0, sc1, rfl, hd, ht, hf, hr, ha, hv⟩ |
              ⟨dst, fTy, d, it, sc0, sc1, rfl, hd, ht, hf, hr, ha, hv⟩
            · exact ⟨d, hd, hs⟩
            · exact ⟨d, it, sc0, sc1, hd, ht, hf, hr, ha, hv⟩
            · exact ⟨d, it, sc0, sc1, hd, ht, hf, hr, ha, hv⟩)
      have henv1 : ProgEnvOk prog fnMap m1 := hrel.env.of_eq hp1 hfp1
      obtain ⟨fnPtr, hevFn, hfnFromPtr⟩ :=
        evalValue_fnPtr_and_lookup henv1 hlk hgetCallee
      let mo0 := movedBefore curBody s.frame.blockIdx bb.statements.length
      have hreadsArgs : readsOk mo0 argOps = true := by
        simp only [termReadsOk, hk] at hmvT
        cases destination with
        | mk dst proj =>
          cases proj with
          | nil => exact readsOk_mono (fun j hj => List.mem_cons_of_mem _ hj) hmvT
          | cons _ _ =>
            simp only [Bool.and_eq_true] at hmvT
            exact readsOk_mono (fun j hj => List.mem_cons_of_mem _ hj) hmvT.2
      have hstale1 : ∀ k : Nat, k ≠ destination.local_ → s.frame.locals[k]? ≠ view1[k]? →
          k ∈ mo0 ∧ s.frame.locals[k]? = some .uninit ∧ view1[k]? ≠ some .dead := by
        intro k hkDst hkne
        rw [hv1Ne k hkDst] at hkne ⊢
        exact hstale_end.2 k hkne
      obtain ⟨hMArgsOk, hMArgsUb⟩ :=
        evalArguments_spec hfCur hsh1 hDest1 (hstale_end.1.trans hv1Len.symm) hstale1
          (fun _ h => h) hreadsArgs hNotDst hArgsOk htrArgs
      have hTermEq : bb.terminator =
          ⟨.call func argOps destination (some targetBb) unwind, bb.terminator.span⟩ := by
        cases hbt : bb.terminator with
        | mk kind span => rw [hbt] at hk; exact congrArg (MirAst.Terminator.mk · span) hk
      obtain ⟨hACallOk, hACallUb⟩ :=
        evalTerminator_call_anneal (callerBody := curBody) (span := bb.terminator.span)
          (targetBb := targetBb) (unwind := unwind) (destination := destination)
          hextr hfindS hslotsA hnA hArgsOk htrArgs
      cases hce : callArgsEval s.frame.locals argOps with
      | none =>
        rw [hTermEq, hACallUb hce]
        obtain ⟨msg, hmsgArgs⟩ := hMArgsUb hce
        have htbTerm : tb.terminator =
            .Call (fnPtrExpr (fnName idx)) fCallee.calling_convention argExprs retExpr
              (some (bbName targetBb)) (some unwindBb) := htt
        have hstep : Interp.step m = .error (.ub msg) := by
          rw [step_callee_stack hshape tb hgetb]
          simp [hif, htbTerm, Interp.evalTerminator, hplRet, hprepRet, hevFn, hfnFromPtr, hmsgArgs]
        exact MultiStepRel.ub' msg hstep
      | some pArgs =>
        obtain ⟨argVals, locals'⟩ := pArgs
        obtain ⟨hAstep, _, _, _, _⟩ := hACallOk argVals locals' hce
        rw [hTermEq, hAstep]
        obtain ⟨hAvLen, hAvSlots, m2, view2, hmArgs, hsh2, hp2, hfp2, halen2, hstale2, hDest2⟩ :=
          hMArgsOk argVals locals' hce
        have hAvLenArgc : argVals.length = callee.argCount := by
          rw [hAvLen]; simp [Nat.min_eq_left hArgBound]
        obtain ⟨_, calleeFuel, rfl⟩ := maxStackLocalsAux_ge hCurBud
        obtain ⟨calleeBudget, hCalleeBud, hStepBud⟩ :=
          maxStackLocalsAux_callee hCurBud hbbmem hk hextr hfind
        have hStepBud' : curBody.localDecls.length + calleeBudget ≤ curBudget := hStepBud
        obtain ⟨hCalleeLenLe, _⟩ := maxStackLocalsAux_ge hCalleeBud
        have hCandCalleeLt :
            (candBound + curBody.localDecls.length) + callee.localDecls.length < 2 ^ 31 := by
          omega
        have hbase2 : BaseCandBounded m2.mem.memory.allocations
            (candBound + curBody.localDecls.length) :=
          hDest2.baseCandBounded hCurCand (fun i d hd => (hfCur.2 i d hd).1)
        obtain ⟨hfCalleeSpec, _, hargsC, hstartC, hinitC, _⟩ :=
          translateFnInProg_spec fnMap callee fCallee hfCallee
        obtain ⟨calleeLm0, mCall, hmCall, hshCall, hpCall, hfpCall, hloCall0⟩ :=
          evalCall_spec (retPlace := retPlace) (targetBb := bbName targetBb) (unwindBb := unwindBb)
            hsh2 (.inr ⟨hfCalleeSpec, hargsC, hstartC⟩)
            hd0Callee hCalleeArgc hpdsEq hAvLenArgc hAvSlots hbase2 hCandCalleeLt
        have htbTerm : tb.terminator =
            .Call (fnPtrExpr (fnName idx)) fCallee.calling_convention argExprs retExpr
              (some (bbName targetBb)) (some unwindBb) := htt
        have hstep1 : Interp.step m = .ok mCall := by
          rw [step_callee_stack hshape tb hgetb]
          simp [hif, htbTerm, Interp.evalTerminator, hplRet, hprepRet, hevFn, hfnFromPtr,
            hmArgs, hmCall, check_after hshCall]
        obtain ⟨_, _, hCalleeHasBbs, _, _, _, _, hCalleeLvOk, hCalleeTiOk⟩ :=
          (bodyInProgFragment_spec (hallFrag callee hCalleeMem)).2
        have hAvSlots' : ∀ (r : Nat) pd v,
            ((callee.localDecls.drop 1).take callee.argCount)[r]? = some pd →
            argVals[r]? = some v → SlotOk (tyOf pd) (.init v) := by
          rw [← hpdsEq]; exact hAvSlots
        obtain ⟨_, hIL0, hILlive, hILinit, hILdead⟩ :=
          initLocals_callee_spec hCalleeArgc hAvLenArgc hAvSlots'
        let calleeCtx : Ctx := {
          caller := calleeFrameL curFn curCtx curLm s.frame.blockIdx s.frame.stmtIdx
          payloads := rootCtx.payloads
          base := m2.mem.memory.allocations
          addrs := []
          nextBlock := bbName targetBb
          unwindBlock := some unwindBb
          retPtr := retPlace.ptr.thin_pointer
        }
        obtain ⟨mCallee0, calleeLm, hstepsInit, hshCallee0, hpInit, hfpInit, hloCallee⟩ :=
          steps_initBlock_stack hfCalleeSpec hinitC hshCall hloCall0 hILdead hbase2 hCandCalleeLt
        have hkSteps : Interp.steps (1 + initLen callee) m = .ok mCallee0 := by
          rw [steps_add, steps_one hstep1, ok_bind, hstepsInit]
        have htgtMem : targetBb ∈ termTargets bb.terminator := by simp [termTargets, hk]
        have hPostStale' : ∀ j : Nat, j ≠ destination.local_ →
            locals'[j]? ≠ view2[j]? →
            j ∈ movedBefore curBody targetBb 0 ∧
              locals'[j]? = some .uninit ∧ view2[j]? ≠ some .dead := by
          intro j hjDst hjNe
          obtain ⟨hjMo0, hjUninit, hjLive⟩ := hstale2 j hjDst hjNe
          refine ⟨hmvEdge targetBb htgtMem j ?_, hjUninit, hjLive⟩
          cases destination with
          | mk dst proj =>
            cases proj with
            | nil =>
              simp only [termMoved, hk]
              exact List.mem_filter.mpr ⟨hjMo0, by simpa using hjDst⟩
            | cons _ _ =>
              simp only [termMoved, hk]
              exact hjMo0
        have hPostLive' : ∀ i ∈ liveAtEntry curBody targetBb,
            i ≠ destination.local_ → locals'[i]? ≠ some .dead := by
          intro i hi _
          have hiEnd := livenessOk_edge hlvOk hbb htgtMem i hi
          rw [← heq] at hiEnd
          exact callArgsEval_ne_dead hce (hrel.liveInv i hiEnd)
        have hPostTuple' : ∀ i ∈ tupleInitAtEntry curBody targetBb,
            i ≠ destination.local_ →
            ∃ sc0 sc1, locals'[i]? =
              some (.init (.aggregate 0 [.scalar sc0, .scalar sc1])) := by
          intro i hi hiDst
          have hiEnd := tupleInitOk_edge htiOk hbb htgtMem i hi
          have hiDrop : i ∈ dropMovedFrom
              (tupleInitBefore curBody s.frame.blockIdx bb.statements.length) argOps := by
            cases destination with
            | mk dst proj =>
              cases proj with
              | nil =>
                simp only [termTupleInit, hk] at hiEnd
                simp only at hiDst
                split at hiEnd
                · split at hiEnd
                  · exact hiEnd
                  · rcases List.mem_cons.mp hiEnd with rfl | hm
                    · exact absurd rfl hiDst
                    · exact hm
                · exact (List.mem_filter.mp hiEnd).1
              | cons _ _ =>
                simp only [termTupleInit, hk] at hiEnd
                exact hiEnd
          obtain ⟨hiOld, hnotMv⟩ := dropMovedFrom_mem hiDrop
          rw [← heq] at hiOld
          rw [callArgsEval_get_of_not_moved hce hnotMv]
          exact hrel.tupleInv i hiOld
        have hStackNext : CallStackRel entry callees fnMap rootCtx
            ({ callerBody := curBody
               frame := { s.frame with locals := locals' }
               destination := destination
               returnTarget := targetBb
               calleeProtectors := s.memory.activeProtectors } :: s.memory.callStack)
            (callerFrames ++ [calleeCtx.caller]) callee calleeCtx
            (candBound + curBody.localDecls.length) calleeFuel :=
          .cons hStackRel rfl hCurMem hCurFn rfl hrel.protectors htgtLt rfl rfl rfl
            hd0Callee hDest2 hCurCand hCurBud hCalleeBud hStepBud hCandBudLt halen2
            hPostStale' hPostLive' hPostTuple'
        have hCalleeBbsPos : 0 < callee.basicBlocks.length := by
          cases hcb : callee.basicBlocks with
          | nil => exact absurd hcb hCalleeHasBbs
          | cons _ _ => simp
        refine MultiStepRel.tauK (1 + initLen callee) mCallee0 (by omega) hkSteps
          ⟨MirSemantics.initLocals callee argVals, {
            stack := ?_
            env := hrel.env.of_eq
              (hpInit.trans (hpCall.trans (hp2.trans hp1)))
              (hfpInit.trans (hfpCall.trans (hfp2.trans hfp1)))
            active := hshCallee0.active
            blk := by simpa using hCalleeBbsPos
            stmt := fun _ _ => Nat.zero_le _
            stale := ⟨rfl, fun _ hj => absurd rfl hj⟩
            retLive := by rw [hIL0]; simp
            liveInv := LiveInv.init hCalleeLvOk rfl rfl hILlive
            tupleInv := TupleInv.init hCalleeTiOk rfl rfl hILinit
            calleesEq := hrel.calleesEq
            activeCalleeOk := ⟨fun hc => by simp at hc, fun _ => ⟨callee, rfl⟩⟩
            borrows := hrel.borrows
            protectors := hrel.protectors
            callerLocals := hrel.callerLocals }⟩
        refine ⟨callerFrames ++ [calleeCtx.caller], calleeCtx, fCallee, calleeLm,
          candBound + curBody.localDecls.length, calleeFuel, calleeBudget, ?_⟩
        simp only [Option.getD_some]
        exact ⟨hCalleeMem, hfCallee, hStackNext, rfl, hbase2, hCalleeBud,
          by omega, hshCallee0.threads, hloCallee⟩

/-- Initial locals map at `fEntry.start` under `MultiStartRel`. -/
theorem MultiStartRel.localsOk {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function} {rootCtx : Ctx}
    {s : MachineState} {mInit : Mach}
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hargs : entry.argCount + 1 ≤ entry.localDecls.length) :
    LocalsOkA entry rootCtx [] s.frame.locals (localsMap rootCtx (entry.argCount + 1))
      mInit.mem.memory.allocations := by
  have hs1 : StartRel entry fEntry rootCtx s mInit := {
    threads := hstart.threads
    active := hstart.active
    allocs := hstart.allocs
    blk0 := hstart.blk0
    stmt0 := hstart.stmt0
    hasBlocks := hstart.hasBlocks
    nlocals := hstart.nlocals
    slots := hstart.slots
    argsLive := hstart.argsLive
    tempsDead := hstart.tempsDead
    addrs := hstart.addrs
    ret := hstart.ret
    baseLow := hstart.baseLow
    borrows := hstart.borrows
    callStack := hstart.callStack
    activeCallee := hstart.activeCallee
    protectors := hstart.protectors
    callerLocals := hstart.callerLocals
  }
  exact hs1.localsOk hargs

/-- **Multi-function init block (`fEntry.start`).** From `MultiStartRel`
(Anneal at `(0, 0)` of `entry` with `callees` loaded and MiniRust at
`fEntry.start`), `initLen entry` MiniRust steps execute `minimize`'s `initBlock`
and land in `MultiStateRel`. -/
theorem multi_step_start {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function} {rootCtx : Ctx}
    {s : MachineState} {mInit : Mach}
    (hfrag : progInFragment entry callees = true)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit) :
    ∃ m0, Interp.steps (initLen entry) mInit = .ok m0 ∧
      MultiStateRel entry callees prog rootCtx s m0 := by
  obtain ⟨_, hallFrag, rootBudget, hRootBud, hRootBudLt⟩ := progInFragment_spec hfrag
  obtain ⟨_, hargs, hn31, _, _, _, _, _, hlvOk, htiOk⟩ :=
    bodyInProgFragment_spec (hallFrag entry List.mem_cons_self)
  obtain ⟨hfSpec, _, _, hfStart, hInitBlk, _⟩ :=
    translateFnInProg_spec (fnNameMap entry callees) entry fEntry hstart.hfEntry
  have hsh0 : Shape mInit rootCtx
      ([rootCtx.caller] ++
        [calleeFrameL fEntry rootCtx (localsMap rootCtx (entry.argCount + 1))
          entry.basicBlocks.length 0])
      mInit.mem.memory.allocations := by
    refine ⟨?_, hstart.active, rfl⟩
    rw [hstart.threads]
    simp [calleeFrame, calleeFrameL, hfStart]
  obtain ⟨m0, lm, hm0, hsh, hp0, hfp0, hlo0⟩ :=
    steps_initBlock_stack hfSpec hInitBlk hsh0 (hstart.localsOk hargs)
      hstart.tempsDead hstart.baseLow.toBaseCandBounded (by omega)
  refine ⟨m0, hm0, s.frame.locals, {
    stack := ?_
    env := hstart.env.of_eq hp0 hfp0
    active := hsh.active
    blk := by rw [hstart.activeCallee, Option.getD_none, hstart.blk0]; exact hstart.hasBlocks
    stmt := fun _ _ => by rw [hstart.stmt0]; exact Nat.zero_le _
    stale := ⟨rfl, fun _ hj => absurd rfl hj⟩
    retLive := by
      have hn0 : 0 < entry.localDecls.length := by omega
      obtain ⟨slot0, hs0⟩ : ∃ slot, s.frame.locals[0]? = some slot :=
        ⟨_, List.getElem?_eq_getElem (by rw [hstart.nlocals]; exact hn0)⟩
      rw [hs0]
      simpa using hstart.argsLive 0 slot0 (Nat.zero_le _) hs0
    liveInv := by
      rw [hstart.activeCallee, Option.getD_none]
      exact LiveInv.init hlvOk hstart.blk0 hstart.stmt0 hstart.argsLive
    tupleInv := by
      rw [hstart.activeCallee, Option.getD_none]
      exact TupleInv.init htiOk hstart.blk0 hstart.stmt0 hstart.argsInit
    calleesEq := hstart.calleesEq
    activeCalleeOk := ⟨fun _ => .inl hstart.activeCallee,
      fun hc => absurd hstart.callStack hc⟩
    borrows := hstart.borrows
    protectors := hstart.protectors
    callerLocals := hstart.callerLocals }⟩
  refine ⟨[rootCtx.caller], rootCtx, fEntry, lm, 0, callees.length + 1, rootBudget, ?_⟩
  rw [hstart.activeCallee, Option.getD_none, hstart.callStack,
    hstart.blk0, hstart.stmt0]
  exact ⟨List.mem_cons_self, hstart.hfEntry,
    .nil hstart.baseLow hstart.ret rootBudget hRootBud hRootBudLt,
    rfl, hstart.baseLow.toBaseCandBounded, hRootBud, by omega, hsh.threads, hlo0⟩

private theorem initLocalsAux_argsInit (ds : List LocalDecl) (vs : List Value) (idx : Nat)
    (h : argsOkAux (ds.take vs.length) vs = true) (hlen : vs.length ≤ ds.length) :
    ∀ (j : Nat) d, j < vs.length → ds[j]? = some d →
      ∃ v, (initLocalsAux (idx + 1) ds vs)[j]? = some (.init v) ∧ SlotOk (tyOf d) (.init v) := by
  induction ds generalizing vs idx with
  | nil => intro j _ hj _; cases vs <;> simp at hj hlen
  | cons d0 ds ih =>
    cases vs with
    | nil => intro j _ hj _; simp at hj
    | cons v vs =>
      simp only [List.length_cons, List.take_succ_cons, argsOkAux, Bool.and_eq_true] at h
      obtain ⟨hv, hvs⟩ := h
      have hvslot : SlotOk (tyOf d0) (.init v) := by
        match v, hv with
        | .scalar sc, hv =>
          simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at hv
          exact ⟨hv.1, (validBits_iff _ _).mp hv.2⟩
        | .aggregate 0 [.scalar sc0, .scalar sc1], hv =>
          simp only [argOk] at hv
          cases ht : tupleIntOfTy (tyOf d0) with
          | none => simp [ht] at hv
          | some it =>
            simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hv
            exact ⟨it, ht, hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩
      intro j d hj hd
      cases j with
      | zero =>
        simp at hd; subst hd
        exact ⟨v, rfl, hvslot⟩
      | succ j =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
        simp only [List.getElem?_cons_succ] at hd
        simp only [initLocalsAux, Nat.add_eq, List.getElem?_cons_succ]
        exact ih vs idx hvs (by simpa using hlen) j d hj hd

/-- General multi-function entry-state bridge: for any `(entry, callees)` in
`progInFragment`, well-typed `args`, and well-formed external caller context
`rootCtx`, Anneal's `initMachineStateWithCallees entry args callees` satisfies
`MultiStartRel` against any MiniRust machine positioned at `fEntry.start` with
`ProgEnvOk`. -/
theorem initMachineStateWithCallees_startRel {entry : CapturedMir}
    {callees : List CapturedMir} {prog : Gen.Program} {fEntry : Gen.Function}
    (hfrag : progInFragment entry callees = true)
    (hfEntry : translateFnInProg (fnNameMap entry callees) entry = some fEntry)
    (rootCtx : Ctx) (hctx : CtxOk entry rootCtx)
    (args : List Value) (hargs : argsOk entry args = true)
    (mInit : Mach) (henv : ProgEnvOk prog (fnNameMap entry callees) mInit)
    (hthreads : mInit.threads =
      [thread1 rootCtx [rootCtx.caller,
        { calleeFrame fEntry rootCtx (entry.argCount + 1) 0 0 with next_block := fEntry.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      rootCtx.base ++ localAllocs rootCtx (entry.localDecls.take (entry.argCount + 1))
        (initMachineStateWithCallees entry args callees).frame.locals) :
    MultiStartRel entry callees prog fEntry rootCtx
      (initMachineStateWithCallees entry args callees) mInit := by
  obtain ⟨_, hallFrag, _⟩ := progInFragment_spec hfrag
  obtain ⟨_, hdeclLen, _, hbne, _⟩ :=
    bodyInProgFragment_spec (hallFrag entry List.mem_cons_self)
  cases hdecls : entry.localDecls with
  | nil => simp [hdecls] at hdeclLen
  | cons d0 ds =>
    rw [hdecls] at hdeclLen
    have hargs' : argsOkAux (ds.take entry.argCount) args = true := by
      simpa [argsOk, hdecls] using hargs
    have hlenA : args.length = entry.argCount := by
      have key : ∀ (ds' : List LocalDecl) (vs : List Value), argsOkAux ds' vs = true →
          vs.length = ds'.length := by
        intro ds'
        induction ds' with
        | nil => intro vs h; cases vs <;> simp_all [argsOkAux]
        | cons d' ds' ih =>
          intro vs h
          cases vs with
          | nil => simp [argsOkAux] at h
          | cons v vs =>
            simp only [argsOkAux, Bool.and_eq_true] at h
            simp [ih vs h.2]
      have := key _ _ hargs'
      simp at this hdeclLen
      omega
    obtain ⟨hlen, hslots, hlive, hdead⟩ :=
      initLocalsAux_spec ds args 0 (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega)
    have hainit :=
      initLocalsAux_argsInit ds args 0 (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega)
    have hinit : (initMachineStateWithCallees entry args callees).frame.locals =
        .uninit :: initLocalsAux 1 ds args := by
      simp [initMachineStateWithCallees, hdecls, initLocalsAux]
    refine {
      hfEntry := hfEntry
      env := henv
      threads := hthreads
      active := hactive
      allocs := hallocs
      blk0 := rfl
      stmt0 := rfl
      hasBlocks := by
        cases hbbs : entry.basicBlocks with | nil => exact absurd hbbs hbne | cons _ _ => simp
      nlocals := by simp [hinit, hdecls, hlen]
      slots := ?_
      argsInit := ?_
      argsLive := ?_
      tempsDead := ?_
      addrs := hctx.addrs
      ret := hctx.ret
      baseLow := hctx.baseLow
      calleesEq := rfl
      borrows := rfl
      callStack := rfl
      activeCallee := rfl
      protectors := rfl
      callerLocals := rfl }
    · intro i d slot hd hs
      rw [hdecls] at hd; rw [hinit] at hs
      cases i with
      | zero => simp at hd hs; subst hs; trivial
      | succ k => simp at hd hs; exact hslots k d slot hd hs
    · intro i d hi1 hi2 hd
      rw [hdecls] at hd; rw [hinit]
      cases i with
      | zero => omega
      | succ k =>
        simp only [List.getElem?_cons_succ] at hd ⊢
        exact hainit k d (by omega) hd
    · intro i slot hi hs
      rw [hinit] at hs
      cases i with
      | zero => simp at hs; subst hs; simp
      | succ k => simp at hs; exact hlive k slot (by omega) hs
    · intro i hi1 hi2
      rw [hinit]
      cases i with
      | zero => omega
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hdead k (by omega) (by rw [hdecls] at hi2; simpa using hi2)

end MiniRustSpec.Correspondence
