/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointerStep
import MiniRustSpec.Correspondence.Provenance

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

`step_correspondence_N` and `step_start_N` state the same for `StateRelN`,
which adds what array, `TupleSpec`, thin raw pointer, and safe reference
(`&T` / `&mut T`) locals need: `NonScalarLive`; `BorrowsOk` (every entry of
Anneal's borrow table is `rawPtrEntry` or its `.disabled` invalidation for an
admissible initial-argument borrow target, synchronized with the flow-sensitive
CFG borrow lattice `ptrEnvBefore` across reborrows, `CopyForDeref`, dereference
writes, and multi-block loops); and `LocalsOk` at `ctxWithBorrows` (the
MiniRust bytes of every initialized pointer or reference local encode the
address and provenance of its tag's target). `step_correspondence` is the
all-scalar special case. The pointer and reference statements rest on
`MiniRustSpec.Correspondence.PointerStep`.
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

theorem translateBlock_spec (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (bb : BasicBlockData) (tb : Gen.BasicBlock)
    (h : translateBlock layouts decls bb = some tb) :
    tb.statements.length = bb.statements.length ∧
    (∀ (k : Nat) st, bb.statements[k]? = some st →
      ∃ st', translateStatement decls st layouts = some st' ∧ tb.statements[k]? = some st') ∧
    translateTerminator layouts decls bb.terminator = some tb.terminator := by
  simp only [translateBlock, Option.bind_eq_bind] at h
  cases hs : bb.statements.mapM (translateStatement decls · layouts) with
  | none => simp [hs] at h
  | some stmts =>
    cases ht : translateTerminator layouts decls bb.terminator with
    | none => simp [hs, ht] at h
    | some term =>
      simp [hs, ht] at h
      subst h
      obtain ⟨hlen, hget⟩ := mapM_option_spec (translateStatement decls · layouts) bb.statements stmts hs
      exact ⟨hlen, hget, rfl⟩

/-- Facts about a body accepted by `inFragment`. -/
theorem inFragment_spec (body : CapturedMir) (h : inFragment body = true) :
    body.phase = .runtimePostCleanup ∧ body.argCount + 1 ≤ body.localDecls.length ∧
    body.localDecls.length < 2 ^ 31 ∧
    (body.localDecls[0]? >>= (scalarTypeOf ·.ty)).isSome = true ∧
    (∀ d ∈ body.localDecls, localDeclOk body.layouts d = true) ∧
    (∀ d ∈ body.localDecls.drop (body.argCount + 1),
      (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true) ∧
    (∀ bb ∈ body.basicBlocks, bb.isCleanup = false ∧
      (∀ st ∈ bb.statements, statementOk body.localDecls st body.layouts = true) ∧
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) ∧
    storageDeadOk body = true ∧ movesOk body = true ∧ mentionsOk body = true := by
  simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hphase, hargs⟩, hn⟩, hret0⟩, hdecls⟩, _⟩, htemps⟩, _⟩, hbbs⟩, hsd⟩, hmv⟩,
    hmt⟩, _⟩, _⟩ := h
  refine ⟨?_, hargs, hn, hret0, hdecls, fun d hd => by simpa using htemps d hd, fun bb hbb => ?_,
    hsd, hmv, hmt⟩
  · unfold CapturedMir.isRuntimePostCleanup at hphase
    split at hphase <;> simp_all
  · obtain ⟨⟨hc, hst⟩, ht⟩ := hbbs bb hbb
    exact ⟨hc, hst, ht⟩

/-- The raw pointer facts of a body accepted by `inFragment`: the static
aliasing discipline `ptrAliasingOk`, and no parameter is a raw pointer. -/
theorem inFragment_ptr (body : CapturedMir) (h : inFragment body = true) :
    ptrAliasingOk body = true ∧
    ∀ (i : Nat) d, 1 ≤ i → i ≤ body.argCount → body.localDecls[i]? = some d →
      isPtrTy d.ty = false := by
  simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hparams⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hpa⟩, _⟩ := h
  refine ⟨hpa, fun i d hi1 hi2 hd => hparams d ?_⟩
  have hget : (List.take body.argCount (List.drop 1 body.localDecls))[i - 1]? = some d := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    rw [show 1 + (i - 1) = i by omega]
    exact hd
  exact List.mem_of_getElem? hget

/-- No local `_0 .. _argCount` of a fragment body (the return place and the
parameters) is a raw pointer. -/
theorem inFragment_params_not_ptr (body : CapturedMir) (h : inFragment body = true) :
    ∀ (i : Nat) d, i < body.argCount + 1 → body.localDecls[i]? = some d →
      isPtrTy d.ty = false := by
  intro i d hi hd
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · obtain ⟨_, _, _, hret0, _⟩ := inFragment_spec body h
    have hsc : (scalarTypeOf d.ty).isSome = true := by simpa [hd] using hret0
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hsc
    exact isPtrTy_false_of_scalarTypeOf hT
  · exact (inFragment_ptr body h).2 i d hpos (by omega) hd

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
theorem terminatorOk_targets_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {t : MirAst.Terminator} (ht : terminatorOk layouts decls nblocks t = true) :
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
    cases hit : switchIntType layouts decls (copyOp discr) with
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
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true)
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

private theorem opMoved_lt_of_operandOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {op : Operand} {j : Nat} (hop : opMoved op = some j)
    (hok : operandOk layouts decls it (copyOp op) = true) : j < decls.length := by
  rw [opMoved_eq_move hop] at hok
  simp only [copyOp, operandOk, placeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1

private theorem opMoved_lt_of_operandOkB {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {op : Operand} {j : Nat} (hop : opMoved op = some j)
    (hok : operandOkB layouts decls (copyOp op) = true) : j < decls.length := by
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

private theorem opMoved_lt_of_relOperandsOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {a b : Operand} (hok : relOperandsOk layouts decls (copyOp a) (copyOp b) = true) :
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

theorem operandOk_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {op : Operand} (hok : operandOk layouts decls it op = true) :
    copyOp op = op ∧ opMoved op = none := by
  cases op with
  | copy _ => exact ⟨rfl, rfl⟩
  | constant _ => exact ⟨rfl, rfl⟩
  | move _ => simp [operandOk] at hok

theorem operandOkB_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {op : Operand} (hok : operandOkB layouts decls op = true) :
    copyOp op = op ∧ opMoved op = none := by
  cases op with
  | copy _ => exact ⟨rfl, rfl⟩
  | constant _ => exact ⟨rfl, rfl⟩
  | move _ => simp [operandOkB] at hok

theorem specOperandOk_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {spec : TupleSpec} {op : Operand} (hok : specOperandOk layouts decls spec op = true) :
    copyOp op = op ∧ opMoved op = none := by
  cases spec with
  | scalar it => exact operandOk_noMove hok
  | tuple _ _ _ =>
    cases op with
    | copy _ => exact ⟨rfl, rfl⟩
    | constant _ => simp [specOperandOk] at hok
    | move _ => simp [specOperandOk] at hok

theorem tupleFieldsOperandOk_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {fields : List (Nat × TupleSpec)} {ops : List Operand}
    (hok : tupleFieldsOperandOk layouts decls fields ops = true) :
    ops.map copyOp = ops ∧ ∀ op ∈ ops, opMoved op = none := by
  induction fields generalizing ops with
  | nil =>
    cases ops with
    | nil => exact ⟨rfl, fun _ h => by simp at h⟩
    | cons _ _ => simp [tupleFieldsOperandOk] at hok
  | cons f fs ih =>
    cases ops with
    | nil => simp [tupleFieldsOperandOk] at hok
    | cons op rest =>
      simp only [tupleFieldsOperandOk, Bool.and_eq_true] at hok
      obtain ⟨h1, h2⟩ := specOperandOk_noMove hok.1
      obtain ⟨hmap, hrest⟩ := ih hok.2
      refine ⟨by simp [h1, hmap], fun o ho => ?_⟩
      rcases List.mem_cons.mp ho with rfl | hm
      · exact h2
      · exact hrest o hm

theorem rvalueOk_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {rv : Rvalue} (hok : rvalueOk layouts decls it rv = true) :
    copyRv rv = rv ∧ ∀ op ∈ rvOperands rv, opMoved op = none := by
  match rv, hok with
  | .use op, hok =>
    obtain ⟨h1, h2⟩ := operandOk_noMove hok
    exact ⟨by simp [copyRv, h1], fun o ho => by simp [rvOperands] at ho; subst ho; exact h2⟩
  | .unaryOp uop op, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    obtain ⟨h1, h2⟩ := operandOk_noMove hok.2
    exact ⟨by simp [copyRv, h1], fun o ho => by simp [rvOperands] at ho; subst ho; exact h2⟩
  | .binaryOp bop a b, hok =>
    simp only [rvalueOk] at hok
    cases htb : translateBinOp bop with
    | none => simp [htb] at hok
    | some iop =>
      simp only [htb, Bool.and_eq_true] at hok
      obtain ⟨ha1, ha2⟩ := operandOk_noMove hok.1
      have hb : copyOp b = b ∧ opMoved b = none := by
        split at hok
        · split at hok
          · exact operandOk_noMove hok.2
          · simp at hok
        · exact operandOk_noMove hok.2
      refine ⟨by simp [copyRv, ha1, hb.1], fun o ho => ?_⟩
      simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact ha2
      · exact hb.2
  | .cast .intToInt op targetTy, hok =>
    simp only [rvalueOk, Bool.and_eq_true] at hok
    have hop : copyOp op = op ∧ opMoved op = none := by
      split at hok
      · exact operandOk_noMove hok.2
      · exact operandOkB_noMove hok.2
    exact ⟨by simp [copyRv, hop.1], fun o ho => by simp [rvOperands] at ho; subst ho; exact hop.2⟩
  | .len ⟨j, []⟩, _ =>
    exact ⟨rfl, fun o ho => by simp [rvOperands] at ho; subst ho; rfl⟩

theorem arrayRvalueOk_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {elemIt : Gen.IntType} {count : Nat} {rv : Rvalue}
    (hok : arrayRvalueOk layouts decls elemIt count rv = true) :
    copyRv rv = rv ∧ ∀ op ∈ rvOperands rv, opMoved op = none := by
  match rv, hok with
  | .use (.copy ⟨j, []⟩), _ =>
    exact ⟨rfl, fun o ho => by simp [rvOperands] at ho; subst ho; rfl⟩
  | .aggregate (.array elemTy) ops, hok =>
    simp only [arrayRvalueOk, Bool.and_eq_true, List.all_eq_true] at hok
    have hmap : ∀ l : List Operand, (∀ op ∈ l, operandOk layouts decls elemIt op = true) →
        l.map copyOp = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp [(operandOk_noMove (hl x (by simp))).1, ih (fun y hy => hl y (by simp [hy]))]
    exact ⟨by simp [copyRv, hmap ops hok.2],
      fun o ho => (operandOk_noMove (hok.2 o (by simpa [rvOperands] using ho))).2⟩
  | .repeat op n, hok =>
    simp only [arrayRvalueOk, Bool.and_eq_true] at hok
    obtain ⟨h1, h2⟩ := operandOk_noMove hok.2
    exact ⟨by simp [copyRv, h1], fun o ho => by simp [rvOperands] at ho; subst ho; exact h2⟩

theorem tupleRvalueOk_noMove {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {dstTy : MirAst.Ty} {fields : List (Nat × TupleSpec)} {size align : Nat} {rv : Rvalue}
    (hok : tupleRvalueOk layouts decls dstTy fields size align rv = true) :
    copyRv rv = rv ∧ ∀ op ∈ rvOperands rv, opMoved op = none := by
  match rv, hok with
  | .use (.copy p), _ =>
    exact ⟨rfl, fun o ho => by simp [rvOperands] at ho; subst ho; rfl⟩
  | .aggregate agg ops, hok =>
    simp only [tupleRvalueOk, Bool.and_eq_true] at hok
    obtain ⟨hmap, hmv⟩ := tupleFieldsOperandOk_noMove hok.2
    exact ⟨by simp [copyRv, hmap], fun o ho => hmv o (by simpa [rvOperands] using ho)⟩

theorem foldl_moveOut_of_noMove {ops : List Operand}
    (h : ∀ op ∈ ops, opMoved op = none) (mo : List Nat) :
    ops.foldl moveOut mo = mo := by
  induction ops generalizing mo with
  | nil => rfl
  | cons op ops ih =>
    have h1 := h op (by simp)
    simp only [List.foldl_cons, moveOut, h1]
    exact ih (fun o ho => h o (by simp [ho])) mo

theorem rvPost_of_noMove {rv : Rvalue}
    (h : ∀ op ∈ rvOperands rv, opMoved op = none) (L : List LocalSlot) :
    rvPost L rv = L := by
  have key : ∀ (ops : List Operand), (∀ op ∈ ops, opMoved op = none) →
      ∀ X, opsPost X ops = X := by
    intro ops hops
    induction ops with
    | nil => intro X; rfl
    | cons op rest ih =>
      intro X
      have h1 := hops op (by simp)
      have hopX : opPost X op = X := by
        cases op with
        | copy _ => rfl
        | constant _ => rfl
        | move p => rcases p with ⟨_, projs⟩; cases projs <;> simp [opMoved] at h1 <;> rfl
      simp only [opsPost, List.foldl_cons, hopX]
      exact ih (fun o ho => hops o (by simp [ho])) X
  exact key (rvOperands rv) h L

private theorem rvalue_filterMap_opMoved_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {rv : Rvalue} {j : Nat}
    (hj : j ∈ (rvOperands rv).filterMap opMoved)
    (hok : (∃ it, rvalueOk layouts decls it (copyRv rv) = true) ∨
      rvalueOkB layouts decls (copyRv rv) = true ∨
      rvalueOkO layouts decls (copyRv rv) = true ∨
      (∃ it, rvalueOkTuple layouts decls it (copyRv rv) = true)) :
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
  | .repeat _ _, _, hok =>
    rcases hok with ⟨it, h⟩ | h | h | ⟨it, h⟩ <;>
      simp [copyRv, rvalueOk, rvalueOkB, rvalueOkO, rvalueOkTuple] at h
  | .len _, hop_mem, _ | .copyForDeref _, hop_mem, _ =>
    simp [rvOperands] at hop_mem; subst hop_mem; simp [opMoved] at hop_mv
  | .ref _ _, hop_mem, _
  | .rawPtr _ _, hop_mem, _ | .discriminant _, hop_mem, _
  | .threadLocalRef _, hop_mem, _ | .nullaryOp _ _, hop_mem, _
  | .shallowInitBox _ _, hop_mem, _ | .wrapUnsafeBinder _ _, hop_mem, _ =>
    simp [rvOperands] at hop_mem

/-- The operands of a pointer-copying fragment rvalue move out of declared
locals only. -/
private theorem ptrRvalueOk_moved_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {isRef : Bool} {rv : Rvalue}
    (h : ptrRvalueOk layouts decls mutbl pointeeIt isRef (copyRv rv) = true) {j : Nat}
    (hj : j ∈ (rvOperands rv).filterMap opMoved) : j < decls.length := by
  obtain ⟨op, hop, hmv⟩ := List.mem_filterMap.mp hj
  have hop_eq := opMoved_eq_move hmv
  subst hop_eq
  cases rv with
  | use o =>
    simp only [rvOperands, List.mem_singleton] at hop
    subst hop
    simp only [copyRv, copyOp, ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  | cast k o ty =>
    simp only [rvOperands, List.mem_singleton] at hop
    subst hop
    cases k with
    | ptrToPtr =>
      simp only [copyRv, copyOp, ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.2
    | transmute =>
      simp only [copyRv, copyOp, ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    | _ => simp [copyRv, copyOp, ptrRvalueOk] at h
  | binaryOp bop a b =>
    simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · cases bop with
      | offset =>
        cases b with
        | constant c =>
          simp only [copyRv, copyOp, ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at h
          exact h.1.1.2
        | _ => simp [copyRv, copyOp, ptrRvalueOk] at h
      | _ => simp [copyRv, ptrRvalueOk] at h
    · cases bop with
      | offset => simp [copyRv, copyOp, ptrRvalueOk] at h
      | _ => simp [copyRv, ptrRvalueOk] at h
  | unaryOp _ _ | «repeat» _ _ | len _ | shallowInitBox _ _ | wrapUnsafeBinder _ _ =>
    simp [copyRv, ptrRvalueOk] at h
  | aggregate _ _ => simp [copyRv, ptrRvalueOk] at h
  | ref _ _ | threadLocalRef _ | rawPtr _ _ | discriminant _ | nullaryOp _ _ | copyForDeref _ =>
    simp [rvOperands] at hop

/-- A pointer or reference dereference read moves out of no local. -/
private theorem ptrDerefReadOk_noMove {decls : List LocalDecl} {it : Gen.IntType} {rv : Rvalue}
    (h : ptrDerefReadOk decls it (copyRv rv) = true) : (rvOperands rv).filterMap opMoved = [] := by
  cases rv with
  | copyForDeref _ => simp [rvOperands, opMoved]
  | use o =>
    cases o with
    | copy pl => simp [rvOperands, opMoved]
    | move pl =>
      obtain ⟨p, projs⟩ := pl
      cases projs with
      | nil => simp [copyRv, copyOp, ptrDerefReadOk] at h
      | cons _ _ => simp [rvOperands, opMoved]
    | constant c => simp [rvOperands, opMoved]
  | _ => simp_all [copyRv, ptrDerefReadOk]

/-- Every local newly added to `mo` by `stmtMoved` on a `statementOk` statement
lies below `decls.length`. -/
theorem statementOk_stmtMoved_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {s : MirAst.Statement} (hs : statementOk decls s layouts = true) (mo : List Nat) (j : Nat)
    (hj : j ∈ stmtMoved mo s) : j ∈ mo ∨ j < decls.length := by
  obtain ⟨kind, span⟩ := s
  match kind, hs, hj with
  | .assign ⟨i, []⟩ rv, hs, hj =>
    simp only [stmtMoved] at hj
    have hj' : j ∈ (rvOperands rv).foldl moveOut mo := (List.mem_filter.mp hj).1
    simp only [statementOk] at hs
    cases hd : decls[i]? with
    | none => simp [hd] at hs
    | some d =>
      simp only [hd] at hs
      split at hs
      · rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj' with hmo | hmv
        · exact .inl hmo
        · exact .inr (rvalue_filterMap_opMoved_lt hmv (.inr (.inl hs)))
      · split at hs
        · rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj' with hmo | hmv
          · exact .inl hmo
          · exact .inr (rvalue_filterMap_opMoved_lt hmv (.inr (.inr (.inl hs))))
        · cases htup : intBoolTupleOf d.ty with
          | some it =>
            simp only [htup] at hs
            rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj' with hmo | hmv
            · exact .inl hmo
            · exact .inr (rvalue_filterMap_opMoved_lt hmv (.inr (.inr (.inr ⟨it, hs⟩))))
          | none =>
            simp only [htup] at hs
            cases hint : intTypeOf d.ty with
            | some it =>
              simp only [hint, Bool.or_eq_true] at hs
              rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj' with hmo | hmv
              · exact .inl hmo
              · rcases hs with hs | hs
                · exact .inr (rvalue_filterMap_opMoved_lt hmv (.inl ⟨it, hs⟩))
                · rw [ptrDerefReadOk_noMove hs] at hmv
                  cases hmv
            | none =>
              simp only [hint] at hs
              cases ha : arrayTypeOf d.ty with
              | some p =>
                obtain ⟨elemIt, count⟩ := p
                simp only [ha] at hs
                rw [foldl_moveOut_of_noMove (arrayRvalueOk_noMove hs).2] at hj'
                exact .inl hj'
              | none =>
                simp only [ha] at hs
                cases ht : tupleTypeOf layouts d.ty with
                | none =>
                  simp only [ht] at hs
                  cases hpt : ptrPointeeOf d.ty with
                  | none => simp [hpt] at hs
                  | some pr =>
                    obtain ⟨mutbl, pointeeIt⟩ := pr
                    simp only [hpt] at hs
                    rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj' with hmo | hmv
                    · exact .inl hmo
                    · exact .inr (ptrRvalueOk_moved_lt hs hmv)
                | some p =>
                  obtain ⟨fields, size, align⟩ := p
                  simp only [ht] at hs
                  rw [foldl_moveOut_of_noMove (tupleRvalueOk_noMove hs).2] at hj'
                  exact .inl hj'
  | .assign ⟨i, proj :: rest⟩ rv, hs, hj =>
    simp only [stmtMoved] at hj
    by_cases hf : ∃ idx fieldTy, proj = .field idx fieldTy
    · obtain ⟨idx, fieldTy, rfl⟩ := hf
      simp only [statementOk, Bool.and_eq_true] at hs
      obtain ⟨_, hs⟩ := hs
      cases hpit : placeIntType layouts decls ⟨i, .field idx fieldTy :: rest⟩ with
      | some it =>
        simp only [hpit, Bool.and_eq_true] at hs
        rw [foldl_moveOut_of_noMove (rvalueOk_noMove hs.2).2] at hj
        exact .inl hj
      | none =>
        simp only [hpit] at hs
        cases htp : tuplePlaceSpec layouts decls ⟨i, .field idx fieldTy :: rest⟩ with
        | none => simp [htp] at hs
        | some p =>
          obtain ⟨fields, size, align⟩ := p
          cases hpm : placeMirTy decls ⟨i, .field idx fieldTy :: rest⟩ with
          | none => simp [htp, hpm] at hs
          | some dstTy =>
            simp only [htp, hpm] at hs
            rw [foldl_moveOut_of_noMove (tupleRvalueOk_noMove hs).2] at hj
            exact .inl hj
    · cases rest with
      | cons _ _ =>
        cases proj with
        | field idx fieldTy => exact False.elim (hf ⟨idx, fieldTy, rfl⟩)
        | _ => simp [statementOk] at hs
      | nil =>
        by_cases hderef : proj = .deref
        · subst hderef
          simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hs
          obtain ⟨_, hs⟩ := hs
          cases hpt : (decls[i]? >>= (ptrPointeeOf ·.ty)) with
          | none => simp [hpt] at hs
          | some pr =>
            obtain ⟨mutbl, pointeeIt⟩ := pr
            cases mutbl with
            | not => simp [hpt] at hs
            | «mut» =>
              simp only [hpt, Bool.or_eq_true] at hs
              rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hj with hmo | hmv
              · exact .inl hmo
              · rcases hs with hs | hs
                · exact .inr (rvalue_filterMap_opMoved_lt hmv (.inl ⟨pointeeIt, hs⟩))
                · rw [ptrDerefReadOk_noMove hs] at hmv
                  cases hmv
        have hok2 : (match decls[i]? >>= (arrayTypeOf ·.ty) with
            | some (elemIt, count) => projOk decls count proj && rvalueOk layouts decls elemIt rv
            | none => false) = true := by
          cases proj with
          | field idx fieldTy => exact False.elim (hf ⟨idx, fieldTy, rfl⟩)
          | deref => exact absurd rfl hderef
          | _ => exact hs
        cases hda : (decls[i]? >>= (arrayTypeOf ·.ty)) with
        | none => simp [hda] at hok2
        | some p =>
          obtain ⟨elemIt, count⟩ := p
          simp only [hda, Bool.and_eq_true] at hok2
          rw [foldl_moveOut_of_noMove (rvalueOk_noMove hok2.2).2] at hj
          exact .inl hj
  | .storageLive i, _, hj | .storageDead i, _, hj =>
    simp only [stmtMoved] at hj
    exact .inl (List.mem_filter.mp hj).1
  | .deinit ⟨i, []⟩, _, hj =>
    simp only [stmtMoved] at hj
    exact .inl (List.mem_filter.mp hj).1
  | .deinit ⟨_, _ :: _⟩, hs, _ => simp [statementOk] at hs
  | .intrinsic _, hs, _ => simp [statementOk] at hs
  | .placeMention _, _, hj | .setDiscriminant _ _, _, hj | .retag _ _, _, hj
  | .coverage, _, hj | .constEvalCounter, _, hj
  | .backwardIncompatibleDropHint _, _, hj | .nop, _, hj =>
    simpa [stmtMoved] using .inl hj

/-- Every local newly added to `mo` by `termMoved` on a `terminatorOk`
terminator lies below `decls.length`. -/
theorem terminatorOk_termMoved_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {t : MirAst.Terminator} (ht : terminatorOk layouts decls nblocks t = true)
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
        cases hit : switchIntType layouts decls (copyOp discr) with
        | none => simp [hit] at ht
        | some it =>
          simp only [hit, Bool.and_eq_true] at ht
          have hdok : discrOk layouts decls (copyOp discr) = true := ht.1.1.1
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
      statementOk body.localDecls s body.layouts = true)
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) :
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
  | intrinsic intr =>
    cases intr with
    | assume op =>
      simp only [stmtMoved, moveOut] at hj ⊢
      cases hmv : opMoved op with
      | none =>
        simp only [hmv] at hj ⊢
        exact hsub j hj
      | some k =>
        simp only [hmv, List.mem_cons] at hj ⊢
        rcases hj with rfl | hmo
        · exact .inl rfl
        · exact .inr (hsub j hmo)
    | copyNonOverlapping _ _ _ =>
      simp only [stmtMoved] at hj ⊢
      exact hsub j hj
  | placeMention _ | setDiscriminant _ _ | retag _ _
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
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
    obtain ⟨⟨hs, hr⟩, hrest⟩ := h
    refine ⟨⟨hs, fun k hk => ?_⟩, ih ?_ hrest⟩
    · have hrk := hr k hk
      simp only [Bool.not_eq_true', Bool.eq_false_iff, Ne, List.contains_iff_mem] at hrk ⊢
      exact fun hmo' => hrk (hsub k hmo')
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
  | assign p rv =>
    obtain ⟨i, projs⟩ := p
    cases projs with
    | nil =>
      have hderef : ∀ (p : Nat) (rest : List ProjectionElem),
          stmtReadsOk mo' ⟨.assign ⟨i, []⟩ (.use (.copy ⟨p, .deref :: rest⟩)), span⟩ = true ∨
          stmtReadsOk mo' ⟨.assign ⟨i, []⟩ (.use (.move ⟨p, .deref :: rest⟩)), span⟩ = true →
          p ∉ mo' := by
        intro p rest hp
        rcases hp with hp | hp <;> simpa [stmtReadsOk] using hp
      cases rv with
      | use op =>
        cases op with
        | copy pl =>
          obtain ⟨p, projs⟩ := pl
          cases projs with
          | nil => exact readsOk_mono hsub h
          | cons e rest =>
            cases e
            case deref =>
              have hp := hderef p rest (.inl h)
              simpa [stmtReadsOk] using fun hm => hp (hsub p hm)
            all_goals exact readsOk_mono hsub h
        | move pl =>
          obtain ⟨p, projs⟩ := pl
          cases projs with
          | nil => exact readsOk_mono hsub h
          | cons e rest =>
            cases e
            case deref =>
              have hp := hderef p rest (.inr h)
              simpa [stmtReadsOk] using fun hm => hp (hsub p hm)
            all_goals exact readsOk_mono hsub h
        | constant c => exact readsOk_mono hsub h
      | rawPtr m pl =>
        obtain ⟨p, projs⟩ := pl
        cases projs with
        | nil => exact readsOk_mono hsub h
        | cons e rest =>
          cases e
          case deref =>
            have hp : p ∉ mo' := by simpa [stmtReadsOk] using h
            simpa [stmtReadsOk] using fun hm => hp (hsub p hm)
          all_goals exact readsOk_mono hsub h
      | ref bkind pl =>
        obtain ⟨p, projs⟩ := pl
        cases projs with
        | nil => exact readsOk_mono hsub h
        | cons e rest =>
          cases e
          case deref =>
            have hp : p ∉ mo' := by simpa [stmtReadsOk] using h
            simpa [stmtReadsOk] using fun hm => hp (hsub p hm)
          all_goals exact readsOk_mono hsub h
      | copyForDeref pl =>
        obtain ⟨p, projs⟩ := pl
        cases projs with
        | nil => exact readsOk_mono hsub h
        | cons e rest =>
          cases e
          case deref =>
            have hp : p ∉ mo' := by simpa [stmtReadsOk] using h
            simpa [stmtReadsOk] using fun hm => hp (hsub p hm)
          all_goals exact readsOk_mono hsub h
      | _ => exact readsOk_mono hsub h
    | cons proj rest =>
      by_cases hd : proj = .deref ∧ rest = [] ∧ (ptrDerefReadSrc rv).isSome = true
      · obtain ⟨rfl, rfl, hsome⟩ := hd
        obtain ⟨r, hsrc⟩ := Option.isSome_iff_exists.mp hsome
        rw [stmtReadsOk_derefWrite_derefRead hsrc] at h ⊢
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne,
          List.contains_iff_mem] at h ⊢
        exact ⟨fun hr => h.1 (hsub r hr), fun hi => h.2 (hsub i hi)⟩
      · rw [stmtReadsOk_derefWrite_of_not_derefRead hd] at h ⊢
        simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
        refine ⟨readsOk_mono hsub h.1, fun j hj => ?_⟩
        have h2 := h.2 j hj
        simp only [Bool.not_eq_true', Bool.eq_false_iff, Ne, List.contains_iff_mem] at h2 ⊢
        intro hm
        apply h2
        apply (foldl_moveOut_mem (rvOperands rv) mo' j).mpr
        rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hm with hmo | hmv
        · exact .inl (hsub j hmo)
        · exact .inr hmv
  | retag _ p =>
    obtain ⟨q, projs⟩ := p
    cases projs with
    | nil =>
      simp only [stmtReadsOk, Bool.not_eq_true', Bool.eq_false_iff, Ne,
        List.contains_iff_mem] at h ⊢
      exact fun hm => h (hsub q hm)
    | cons _ _ => rfl
  | intrinsic intr =>
    cases intr with
    | assume op => exact readsOk_mono hsub h
    | copyNonOverlapping _ _ _ => rfl
  | placeMention _ | storageLive _ | storageDead _ | deinit _
  | setDiscriminant _ _ | coverage
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
      statementOk body.localDecls s body.layouts = true)
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true)
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
      statementOk body.localDecls s body.layouts = true)
    (hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) :
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

theorem StaleOk.slots {layouts : Layout.LayoutTable} {decls : List LocalDecl} {body : CapturedMir}
    {actual view : List LocalSlot} {blk stmt : Nat} (h : StaleOk body actual view blk stmt)
    (hv : ∀ (i : Nat) d slot, decls[i]? = some d → view[i]? = some slot → DeclSlotOk d slot layouts) :
    SlotsOk layouts decls actual := by
  intro i d slot hd hs
  by_cases heq : actual[i]? = view[i]?
  · rw [heq] at hs; exact hv i d slot hd hs
  · obtain ⟨_, ha, _⟩ := h.2 i heq; rw [ha] at hs; cases hs; exact declSlotOk_uninit d layouts

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

/-- `StaleOk` after a dereference write `(*_i) = rv` that updates target local
`_k` to `x` and de-initializes any locals moved out of by `rv`. -/
theorem StaleOk.assignDeref {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st) {i : Nat} {rv : Rvalue}
    (hk : st.kind = .assign ⟨i, [.deref]⟩ rv) (h : StaleOk body actual view blk stmt)
    (k : Nat) (x : LocalSlot) :
    StaleOk body ((rvPost actual rv).set k x) (view.set k x) blk (stmt + 1) := by
  unfold StaleOk
  rw [movedBefore_succ hbb hst]
  refine ⟨by simp [rvPost_length, h.1], fun j hj => ?_⟩
  simp only [stmtMoved, hk]
  have hjk : j ≠ k := by
    intro hjk
    subst hjk
    apply hj
    rw [List.getElem?_set, List.getElem?_set, rvPost_length, h.1]
    simp
  rw [List.getElem?_set_ne (Ne.symm hjk), List.getElem?_set_ne (Ne.symm hjk)] at hj ⊢
  rcases opsPost_get actual (rvOperands rv) j with h' | ⟨hm, h1, h2⟩
  · simp only [rvPost] at hj ⊢
    rw [h'] at hj ⊢
    obtain ⟨hmo, ha, hv⟩ := h.2 j hj
    exact ⟨(foldl_moveOut_mem _ _ _).mpr (.inl hmo), ha, hv⟩
  · exact ⟨(foldl_moveOut_mem _ _ _).mpr (.inr hm), h1, fun hv => h2 ((h.dead_iff j).mpr hv)⟩

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

/-- `StaleOk` after a projected assignment to `_i.proj = rv` whose rvalue does
not move out of any local (`stmtMoved mo st = mo`), updating `_i` alike in both
models. -/
theorem StaleOk.setBothKeep {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st) {i : Nat}
    (hmo : stmtMoved (movedBefore body blk stmt) st = movedBefore body blk stmt)
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
  exact h.2 j hj

/-- `StaleOk` after a `PlaceMention`, which changes nothing. -/
theorem StaleOk.keep {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st)
    (hmo : stmtMoved (movedBefore body blk stmt) st = movedBefore body blk stmt)
    (h : StaleOk body actual view blk stmt) : StaleOk body actual view blk (stmt + 1) := by
  unfold StaleOk at h ⊢
  rw [movedBefore_succ hbb hst, hmo]
  exact h

/-- `StaleOk` after `Assume(op)`, which may move out of `op`'s root local in
Anneal while `translateOperand` lowers `move` via `ValueExpr::Load` in MiniRust. -/
theorem StaleOk.assume {body : CapturedMir} {actual view : List LocalSlot} {blk stmt : Nat}
    {bb : BasicBlockData} {st : MirAst.Statement} (hbb : body.basicBlocks[blk]? = some bb)
    (hst : bb.statements[stmt]? = some st) {op : Operand}
    (hk : st.kind = .intrinsic (.assume op)) (h : StaleOk body actual view blk stmt) :
    StaleOk body (opPost actual op) view blk (stmt + 1) := by
  unfold StaleOk
  rw [movedBefore_succ hbb hst]
  simp only [stmtMoved, hk]
  refine ⟨by rw [opPost_length]; exact h.1, fun j hj => ?_⟩
  rcases opPost_get actual op j with h' | ⟨hm, h1, s, h2, h3⟩
  · rw [h'] at hj ⊢
    obtain ⟨hmo, ha, hv⟩ := h.2 j hj
    exact ⟨by unfold moveOut; split <;> simp [hmo], ha, hv⟩
  · refine ⟨by simp [moveOut, hm], h1, fun hv => h3 ?_⟩
    have := (h.dead_iff j).mpr hv
    rw [h2] at this
    exact Option.some.inj this

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
    (hd : body.localDecls[0]? = some d) (h0scalar : (scalarTypeOf d.ty).isSome = true)
    (r : Nat) (a : Gen.Allocation)
    (hp : ctx.retPtr.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a)
    (hlive : a.live = true) (haddrr : a.addr = ctx.retPtr.addr)
    (hlenr : a.data.length = tyBytes (tyOf d body.layouts))
    (halr : ctx.retPtr.addr % ((itOf d body.layouts).size.bytes : Int) = 0) :
    (∀ v, locals[0]? = some (.init v) →
      ∃ m' R, evalReturn m = .ok m' ∧
        Shape m' ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]
          (ctx.base.set r { a with data := declSlotData d (.init v) body.layouts } ++ R) ∧
        ∀ b ∈ R, b.live = false) ∧
    (locals[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  have hT := h.decl_localTy 0 d hd
  have hdScalar : scalarTypeOf d.ty = some (tyOf d body.layouts) := by
    obtain ⟨T0, hT0⟩ := Option.isSome_iff_exists.mp h0scalar
    exact (tyOf_of_scalarTypeOf hT0) ▸ hT0
  have hspec := h.hf
  have hloc0 := (hspec.2 0 d hd).2
  have hact : activeThread m = .ok (thread1 ctx [ctx.caller, calleeFrameL f ctx lm blk stmt]) := by
    simp [activeThread, listIndex, h.shape.threads, h.shape.active]
  have hs3 : Shape { m with threads := [thread1 ctx [ctx.caller]] } ctx [ctx.caller]
      m.mem.memory.allocations := ⟨rfl, h.shape.active, rfl⟩
  have hprefix : ∀ p0 : Ptr, mapGet lm (localName 0) = some p0 → evalReturn m = (do
      let (retVal, m4) ← typedLoad { m with threads := [thread1 ctx [ctx.caller]] } p0
        (tyOf d body.layouts) ⟨(itOf d body.layouts).size.bytes⟩ .None
      let (frame, cm) ← deallocAll lm.entries.length (calleeFrameL f ctx lm blk stmt) m4.mem
      let m5 := { m4 with mem := cm }
      match frame.stack_pop_action with
      | .BottomOfStack => terminateActiveThread m5
      | .BackToCaller nextBlock _ callerRetPtr => do
        let t ← activeThread m5
        if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
        else do
          let m6 ← typedStore m5 callerRetPtr retVal (tyOf d body.layouts) ⟨(itOf d body.layouts).size.bytes⟩ .None
          match nextBlock with
          | some nb => jumpToBlock m6 nb
          | none => ub "return from a function where caller did not specify next block") := by
    intro p0 hp0
    simp only [evalReturn, hact, ok_bind, thread1, List.getLast?_cons_cons, List.getLast?_singleton,
      listSet, h.shape.active, h.shape.threads]
    simp [calleeFrameL, hspec.1, mapIndex, hloc0, hT.layout, expect_align_sized, hp0]
    rfl
  -- `_0`'s storage, for a live `_0`.
  have hstore : ∀ slot0, locals[0]? = some slot0 → slot0 ≠ .dead →
      ∃ (p0 : Ptr) (id0 : Nat), mapGet lm (localName 0) = some p0 ∧ p0.provenance = some (⟨(id0 : Int)⟩, ()) ∧
        Align.is_aligned ⟨(itOf d body.layouts).size.bytes⟩ p0.addr = true ∧
        m.mem.memory.allocations[id0]? =
          some (stackAlloc p0.addr (itOf d body.layouts) (declSlotData d slot0 body.layouts)) := by
    intro slot0 hs0 hne
    obtain ⟨p0, hp0⟩ := h.locs.some_of_live hs0 hne
    obtain ⟨id0, hpid0, _, haddr0, _, _, hA0⟩ :=
      h.locs.storage_nonptr 0 d slot0 p0 hd hs0 hp0 (isPtrTy_false_of_scalarTypeOf hdScalar)
    exact ⟨p0, id0, hp0, hpid0, by simp only [Align.is_aligned, haddr0.1]; rfl, hA0⟩
  constructor
  · intro v hv
    obtain ⟨p0, id0, hp0, hpid0, hal0, hA0⟩ := hstore _ hv (by simp)
    have hslot0 : SlotOk (tyOf d body.layouts) (.init v) :=
      (DeclSlotOk_of_scalarTypeOf hdScalar (.init v)).mp (h.slots 0 d _ hd hv)
    obtain ⟨m4, hm4, hs4⟩ := typedLoad_ptr_localTy hs3 p0 id0 hpid0 d hdScalar v hslot0 hA0 _ hal0
    obtain ⟨hidnd, hok, hlow, hown⟩ := h.locs.teardown h.hf h.declsOk
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
      hlenr v hslot0 ⟨(itOf d body.layouts).size.bytes⟩ (by simp only [Align.is_aligned, halr]; rfl)
    have hs6 := withMem_shape (allocs' := ctx.base.set r { a with data := declSlotData d (.init v) body.layouts } ++
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

/-- `evalReturn_frame` specialized to an integer return local `_0`. -/
theorem evalReturn_callee {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt) (d : LocalDecl)
    (hd : body.localDecls[0]? = some d)
    (h0int : intTypeOf d.ty = some (itOf d body.layouts))
    (r : Nat) (a : Gen.Allocation)
    (hp : ctx.retPtr.provenance = some (⟨(r : Int)⟩, ())) (hr : ctx.base[r]? = some a)
    (hlive : a.live = true) (haddrr : a.addr = ctx.retPtr.addr)
    (hlenr : a.data.length = (itOf d body.layouts).size.bytes)
    (halr : ctx.retPtr.addr % ((itOf d body.layouts).size.bytes : Int) = 0) :
    (∀ sc, locals[0]? = some (.init (.scalar sc)) →
      ∃ m' R, evalReturn m = .ok m' ∧
        Shape m' ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]
          (ctx.base.set r { a with data := scalarBytes (itOf d body.layouts) sc.bits } ++ R) ∧
        ∀ b ∈ R, b.live = false) ∧
    (locals[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  have h0scalar : (scalarTypeOf d.ty).isSome = true := by
    unfold scalarTypeOf
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp [h0int]
  obtain ⟨hTd, _⟩ := tyOf_int (layouts := body.layouts) h0int
  have hfrag : FragTy (tyOf d body.layouts) (itOf d body.layouts) := by
    rw [hTd]; exact .int _ (intTypeOf_good h0int)
  have hlenr' : a.data.length = tyBytes (tyOf d body.layouts) := by
    rw [hfrag.tyBytes]; exact hlenr
  obtain ⟨h1, h2⟩ := evalReturn_frame h d hd h0scalar r a hp hr hlive haddrr hlenr' halr
  refine ⟨fun sc hsc => ?_, h2⟩
  have hdData : declSlotData d (.init (.scalar sc)) body.layouts =
      scalarBytes (itOf d body.layouts) sc.bits := by
    simp [declSlotData, intTypeOf_intBoolTupleOf h0int, h0int, slotData]
  rw [← hdData]
  exact h1 (.scalar sc) hsc

/-! ## Shapes of fragment statements and terminators -/

theorem translateStatement_some {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {st : MirAst.Statement} {st' : Gen.Statement}
    (h : translateStatement decls st layouts = some st') :
    (∃ dst rv pe e, st.kind = .assign dst rv ∧
      translatePlace decls dst = some pe ∧
      translateRvalue layouts decls (placeMirTy decls dst) (copyRv rv) = some e ∧
      st' = .Assign pe e) ∨
    (∃ p pe, st.kind = .placeMention p ∧ translatePlace decls p = some pe ∧
      st' = .PlaceMention pe) ∨
    (∃ i, st.kind = .storageLive i ∧ st' = .StorageLive (localName i)) ∨
    (∃ i, st.kind = .storageDead i ∧ st' = .StorageDead (localName i)) ∨
    (∃ p pe, st.kind = .deinit p ∧ translatePlace decls p = some pe ∧ st' = .Deinit pe) ∨
    (∃ kind p pe, st.kind = .retag kind p ∧ translatePlace decls p = some pe ∧
      st' = .Validate pe (isRetagFnEntry kind)) := by
  obtain ⟨kind, span⟩ := st
  simp only [translateStatement] at h ⊢
  match kind, h with
  | .assign dst rv, h =>
    simp only [Option.bind_eq_bind] at h
    cases hpe : translatePlace decls dst with
    | none => simp [hpe] at h
    | some pe =>
      cases he : translateRvalue layouts decls (placeMirTy decls dst) (copyRv rv) with
      | none => simp [hpe, he] at h
      | some e =>
        simp [hpe, he] at h
        exact .inl ⟨dst, rv, pe, e, rfl, hpe, he, h.symm⟩
  | .setDiscriminant _ _, h => simp at h
  | .deinit p, h =>
    cases hpe : translatePlace decls p with
    | none => simp [hpe] at h
    | some pe => simp [hpe] at h; exact .inr (.inr (.inr (.inr (.inl ⟨p, pe, rfl, hpe, h.symm⟩))))
  | .storageLive i, h => simp at h; exact .inr (.inr (.inl ⟨i, rfl, h.symm⟩))
  | .storageDead i, h => simp at h; exact .inr (.inr (.inr (.inl ⟨i, rfl, h.symm⟩)))
  | .retag kind p, h =>
    cases hpe : translatePlace decls p with
    | none => simp [hpe] at h
    | some pe =>
      simp [hpe] at h
      exact .inr (.inr (.inr (.inr (.inr ⟨kind, p, pe, rfl, hpe, h.symm⟩))))
  | .placeMention ⟨i, []⟩, h =>
    simp at h
    exact .inr (.inl ⟨⟨i, []⟩, .Local (localName i), rfl, rfl, h.symm⟩)
  | .placeMention ⟨i, p :: rest⟩, h =>
    cases p with
    | field idx fieldTy =>
      cases hpe : translateFieldPlace (.Local (localName i)) (.field idx fieldTy :: rest) with
      | none => simp [hpe] at h
      | some pe =>
        simp [hpe] at h
        exact .inr (.inl ⟨⟨i, .field idx fieldTy :: rest⟩, pe, rfl, hpe, h.symm⟩)
    | _ => simp at h
  | .intrinsic _, h => simp at h
  | .coverage, h => simp at h
  | .constEvalCounter, h => simp at h
  | .backwardIncompatibleDropHint _, h => simp at h
  | .nop, h => simp at h

theorem statementOk_assign_single_nonfield {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {proj : ProjectionElem} {rv : Rvalue} {span : String}
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy) (hnd : proj ≠ .deref) :
    statementOk decls ⟨.assign ⟨i, [proj]⟩ rv, span⟩ layouts =
      match decls[i]? >>= (arrayTypeOf ·.ty) with
      | some (elemIt, count) =>
        projOk decls count proj && rvalueOk layouts decls elemIt rv
      | none => false := by
  cases proj with
  | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
  | deref => exact absurd rfl hnd
  | _ => rfl

theorem translateTerminator_some {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {t : MirAst.Terminator} {tt : Gen.Terminator}
    (h : translateTerminator layouts decls t = some tt) :
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

theorem terminatorOk_switch {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {t : MirAst.Terminator} {discr : Operand} {targets : SwitchTargets}
    (h : terminatorOk layouts decls nblocks t = true) (hk : t.kind = .switchInt discr targets) :
    ∃ it, switchIntType layouts decls (copyOp discr) = some it ∧
      discrOk layouts decls (copyOp discr) = true ∧
      (∀ p ∈ targets.branches, p.1 < 2 ^ (8 * it.size.bytes) ∧ p.2 < nblocks) ∧
      targets.otherwise < nblocks := by
  simp only [terminatorOk, hk] at h
  cases hit : switchIntType layouts decls (copyOp discr) with
  | none => simp [hit] at h
  | some it =>
    simp only [hit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hokd, hbr⟩, _⟩, ho⟩ := h
    exact ⟨it, rfl, hokd, hbr, ho⟩

/-- A translated fragment `switchInt`: the switch value evaluates to the
integer `int_from_bits(bits)` at the switch type `it` (for a `bool`
discriminant, through `minimize`'s transmute to `u8`), and the discriminant's
`copy` form is a comparable fragment operand (`RelOperandOk`). -/
theorem switch_spec {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOk body f ctx locals lm m blk stmt)
    {t : MirAst.Terminator} {tt : Gen.Terminator} {discr : Operand} {targets : SwitchTargets}
    (hk : t.kind = .switchInt discr targets)
    (htt : translateTerminator body.layouts body.localDecls t = some tt)
    {it : Gen.IntType} (hit : switchIntType body.layouts body.localDecls (copyOp discr) = some it)
    (hdok : discrOk body.layouts body.localDecls (copyOp discr) = true) :
    (∃ T, RelTy T it ∧ RelOperandOk body.layouts body.localDecls T it (copyOp discr)) ∧
    ∃ value, tt = .Switch value (switchCases it targets.branches) (bbName targets.otherwise) ∧
      (∀ bits, opBits locals (copyOp discr) = some bits →
        bits < 2 ^ (8 * it.size.bytes) ∧
        ∃ m', evalValue m value = .ok ((.Int (intFromBits bits it), .Int it), m') ∧
          FrameOk body f ctx locals lm m' blk stmt) ∧
      (opBits locals (copyOp discr) = none → ∃ msg, evalValue m value = .error (.ub msg)) := by
  simp only [translateTerminator, hk, Option.bind_eq_bind] at htt
  unfold switchIntType at hit
  unfold discrOk at hdok
  cases hv : translateOperand body.localDecls (copyOp discr) with
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
      refine ⟨⟨.Int it', .int it' hgood, .int it' (copyOp discr) hdok⟩, v, htt', ?_⟩
      exact evalValue_operand h it' (copyOp discr) hdok v hv
    · next hty =>
      simp only [Option.some.injEq] at hit
      subst hit
      simp only [hty] at hdok
      have htt' : tt = .Switch (boolToU8 v) (switchCases u8Ty targets.branches)
          (bbName targets.otherwise) := by
        simpa [hty] using htt.symm
      have hokT := operandOkB_T hdok
      refine ⟨⟨.Bool, .bool, .bool (copyOp discr) hdok⟩, boolToU8 v, htt', ?_⟩
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
/-! ## Introducing `StateRelN` and `StepRel` -/

/-- `StateRel` bundled with what the raw pointer statements need:
`NonScalarLive` on the MiniRust view and locals map, the Anneal borrow table
invariant `BorrowsOk`, and `LocalsOk` at `ctxWithBorrows`, which ties the
bytes of every initialized raw pointer local to the address of the borrow
target its tag names. Every reachable execution state from `StartRel` (when
non-scalar locals start initialized) or from any all-scalar `StateRel`
satisfies `StateRelN`. -/
def StateRelN (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState) (m : Mach) : Prop :=
  ∃ view lm, StateRelAt body f ctx s view m ∧
    m.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]] ∧
    LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) view lm m.mem.memory.allocations ∧
    NonScalarLive body view lm ∧
    BorrowsOk body ctx view s lm

theorem StateRelN.toStateRel {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {m : Mach} (h : StateRelN body f ctx s m) :
    StateRel body f ctx s m :=
  let ⟨view, _, hrel, _, _, _, _⟩ := h
  ⟨view, hrel⟩

/-- Any `StateRel` on a body whose locals are all scalar (`scalarTypeOf d.ty = some _`)
satisfies `StateRelN`: such a body has no raw pointer locals and borrows no
local. -/
theorem StateRel.toStateRelN {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {m : Mach}
    (h : StateRel body f ctx s m)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    StateRelN body f ctx s m := by
  obtain ⟨view, hrel⟩ := h
  obtain ⟨lm, hthr, hlo⟩ := hrel.frame
  have hbor : s.memory.borrows = [] := by
    rcases hrel.borrows with h | h
    · exact h
    · exact absurd hall h
  have hsc : ∀ (i : Nat) d, body.localDecls[i]? = some d → (scalarTypeOf d.ty).isSome = true :=
    fun i d hd => (List.all_eq_true.mp hall) d (List.mem_of_getElem? hd)
  have hnp : ∀ (i : Nat) d, body.localDecls[i]? = some d → isPtrTy d.ty = false := fun i d hd => by
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (hsc i d hd)
    exact isPtrTy_false_of_scalarTypeOf hT
  refine ⟨view, lm, hrel, hthr, ?_, fun i d slot hd _ hnone _ => ?_, ?_⟩
  · rw [hbor, ctxWithBorrows_nil]; exact hlo
  · have := hsc i d hd
    simp [hnone] at this
  · exact BorrowsOk.start hbor
      (fun ⟨d, hd, hp⟩ => by
        obtain ⟨i, hi_lt, hi⟩ := List.mem_iff_getElem.mp hd
        have hi' : body.localDecls[i]? = some d := hi ▸ List.getElem?_eq_getElem hi_lt
        rw [hnp i d hi'] at hp
        cases hp)
      (fun hfrag k hk => absurd hk (bodyAddrTakenLocals_nil_of_allScalar hfrag hall k))
      (fun hfrag k hk => absurd hk (bodyAddrTakenLocals_nil_of_allScalar hfrag hall k))
      (fun p dp pv hdp hpty => absurd hpty (by rw [hnp p dp hdp]; simp))

/-- With `BorrowsOk`, the borrow table of an all-scalar fragment body is
empty (`StateRelAt.borrows`). -/
theorem BorrowsOk.borrows_nil_or {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    (hfrag : inFragment body = true) :
    s.memory.borrows = [] ∨ ¬ body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by
  by_cases hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true
  · left
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    obtain ⟨_, _, _, _, hmem, _⟩ := hb.entries_ok e he
    exact bodyAddrTakenLocals_nil_of_allScalar hfrag hall _ hmem
  · exact .inr hall

/-- `LocalsOk` at `ctxWithBorrows` gives the `LocalsOk` of `StateRelAt.frame`,
which ties raw pointer locals to no particular target. -/
theorem LocalsOk.forget_ptrTargets {body : CapturedMir} {ctx : Ctx} {borrows : List BorrowEntry}
    {view : List LocalSlot} {lm : Map Gen.LocalName Ptr} {A : List Gen.Allocation}
    (hlo : LocalsOk body (ctxWithBorrows body ctx borrows) view lm A) :
    LocalsOk body { ctx with ptrTargets := fun _ => none } view lm A :=
  LocalsOkA.extend_ptrTargets (ctx1 := ctxWithBorrows body ctx borrows)
    (ctx2 := { ctx with ptrTargets := fun _ => none }) rfl hlo
    (fun _ _ _ _ _ _ _ _ h2 => by simp at h2)

/-- Step relation preserving `StateRelN` on `.tau` and `.emit` steps. -/
def StepRelN (body : CapturedMir) (f : Gen.Function) (ctx : Ctx) (s : MachineState)
    (a : MirStepNode) (r : Interp Mach) : Prop :=
  match a with
  | .tau (.running s') => ∃ m', r = .ok m' ∧ StateRelN body f ctx s' m'
  | .vis (.inr (.inl (.emit _))) k =>
    ∃ s' m', k PUnit.unit = .running s' ∧ r = .ok m' ∧ StateRelN body f ctx s' m'
  | .ret (.normal (v, _)) => ∃ m', r = .ok m' ∧ ReturnRel body ctx s v m'
  | .vis (.inl (.fail .ub)) _ => ∃ msg, r = .error (.ub msg)
  | _ => False

theorem StepRelN.toStepRel {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {n : MirStepNode} {r : Interp Mach}
    (h : StepRelN body f ctx s n r) : StepRel body f ctx s n r := by
  unfold StepRelN at h
  unfold StepRel
  split at h
  · obtain ⟨m', hr, h'⟩ := h; exact ⟨m', hr, h'.toStateRel⟩
  · obtain ⟨s', m', hk, hr, h'⟩ := h; exact ⟨s', m', hk, hr, h'.toStateRel⟩
  · exact h
  · exact h
  · exact h.elim

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
theorem StepRelN.tau' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s s' : MachineState}
    {r : Interp Mach} (m' : Mach) (hr : r = .ok m') (h : StateRelN body f ctx s' m') :
    StepRelN body f ctx s (.tau (.running s')) r := ⟨m', hr, h⟩

theorem StepRelN.emit' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {ev : MirObs} {k : PUnit → MirExecState} {r : Interp Mach} (s' : MachineState) (m' : Mach)
    (hk : k PUnit.unit = .running s') (hr : r = .ok m') (h : StateRelN body f ctx s' m') :
    StepRelN body f ctx s (.vis (.inr (.inl (.emit ev))) k) r := ⟨s', m', hk, hr, h⟩

theorem StepRelN.ret' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {v : Value} {mem : MirSemantics.Memory} {r : Interp Mach} (m' : Mach) (hr : r = .ok m')
    (h : ReturnRel body ctx s v m') :
    StepRelN body f ctx s (.ret (.normal (v, mem))) r := ⟨m', hr, h⟩

theorem StepRelN.ub' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {r : Interp Mach} (msg : String) (hr : r = .error (.ub msg)) :
    StepRelN body f ctx s (MirStepNode.fail .ub) r := ⟨msg, hr⟩

/-! ## Constructing `StateRel` and `StateRelN` -/

/-- The relation after a statement: Anneal advanced to the next statement with
slots `actual'` and memory `mem'`, MiniRust to the next statement with the
view `view'` and the locals map `lm'`. -/
theorem StateRelAt.advanceN {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach} (hrel : StateRelAt body f ctx s view m)
    (hfrag : inFragment body = true)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hlt : s.frame.stmtIdx < bb.statements.length)
    (actual' view' : List LocalSlot) (mem' : MirSemantics.Memory) (lm' : Map Gen.LocalName Ptr)
    (m' : Mach)
    (hthr : m'.threads =
      [thread1 ctx [ctx.caller, calleeFrameL f ctx lm' s.frame.blockIdx (s.frame.stmtIdx + 1)]])
    (hact : m'.active_thread = 0)
    (hlo : LocalsOk body (ctxWithBorrows body ctx mem'.borrows) view' lm' m'.mem.memory.allocations)
    (hns : NonScalarLive body view' lm')
    (hstale : StaleOk body actual' view' s.frame.blockIdx (s.frame.stmtIdx + 1))
    (hret : view'[0]? ≠ some .dead)
    (hbo : BorrowsOk body ctx view' (advanceStmt s actual' mem') lm')
    (hcs : mem'.callStack = s.memory.callStack)
    (hac : mem'.activeCallee = s.memory.activeCallee)
    (hpr : mem'.activeProtectors = s.memory.activeProtectors)
    (hcl : mem'.callerLocals = s.memory.callerLocals) :
    StateRelN body f ctx (advanceStmt s actual' mem') m' :=
  ⟨view', lm', {
    frame := ⟨lm', hthr, hlo.forget_ptrTargets⟩
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
    borrows := hbo.borrows_nil_or hfrag
    callStack := hcs.trans hrel.callStack
    activeCallee := hac.trans hrel.activeCallee
    protectors := hpr.trans hrel.protectors
    callerLocals := hcl.trans hrel.callerLocals }, hthr, hlo, hns, hbo⟩

/-- The relation after a jump to the in-range block `t`. -/
theorem StateRelAt.jumpN {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach} (hrel : StateRelAt body f ctx s view m)
    (hfrag : inFragment body = true) {m' : Mach}
    (lm : Map Gen.LocalName Ptr) (t : Nat) (ht : t < body.basicBlocks.length)
    (actual' : List LocalSlot)
    (hthr : m'.threads = [thread1 ctx [ctx.caller, calleeFrameL f ctx lm t 0]])
    (hact : m'.active_thread = 0)
    (hlo : LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) view lm m'.mem.memory.allocations)
    (hns : NonScalarLive body view lm)
    (hstale : StaleOk body actual' view t 0)
    (hbo : BorrowsOk body ctx view (jumpState s t actual') lm) :
    StateRelN body f ctx (jumpState s t actual') m' :=
  ⟨view, lm, {
    frame := ⟨lm, hthr, hlo.forget_ptrTargets⟩
    active := hact
    blk := ht
    stmt := fun _ _ => Nat.zero_le _
    stale := hstale
    retLive := hrel.retLive
    ret := hrel.ret
    baseLow := hrel.baseLow
    borrows := hbo.borrows_nil_or hfrag
    callStack := hrel.callStack
    activeCallee := hrel.activeCallee
    protectors := hrel.protectors
    callerLocals := hrel.callerLocals }, hthr, hlo, hns, hbo⟩

/-- The `moveKind` of a fragment rvalue. -/
theorem moveKind_of_rvalueOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {rv : Rvalue}
    (h : rvalueOk layouts decls it (copyRv rv) = true) : moveKind rv = true := by
  cases rv with
  | unaryOp uop op => cases uop <;> simp_all [copyRv, rvalueOk, translateUnOp, moveKind]
  | cast k op ty => cases k <;> simp_all [copyRv, rvalueOk, moveKind]
  | _ => simp_all [copyRv, rvalueOk, moveKind]

theorem moveKind_of_rvalueOkB {layouts : Layout.LayoutTable} {decls : List LocalDecl} {rv : Rvalue}
    (h : rvalueOkB layouts decls (copyRv rv) = true) : moveKind rv = true := by
  cases rv with
  | unaryOp uop op => cases uop <;> simp_all [copyRv, rvalueOkB, moveKind]
  | _ => simp_all [copyRv, rvalueOkB, moveKind]

theorem moveKind_of_rvalueOkO {layouts : Layout.LayoutTable} {decls : List LocalDecl} {rv : Rvalue}
    (h : rvalueOkO layouts decls (copyRv rv) = true) : moveKind rv = true := by
  cases rv <;> simp_all [copyRv, rvalueOkO, moveKind]

theorem moveKind_of_rvalueOkTuple {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {it : Gen.IntType} {rv : Rvalue}
    (h : rvalueOkTuple layouts decls it (copyRv rv) = true) : moveKind rv = true := by
  cases rv with
  | aggregate k ops => cases k <;> simp_all [copyRv, rvalueOkTuple, moveKind]
  | _ => simp_all [copyRv, rvalueOkTuple, moveKind]

theorem moveKind_of_arrayRvalueOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {elemIt : Gen.IntType} {count : Nat} {rv : Rvalue}
    (h : arrayRvalueOk layouts decls elemIt count rv = true) : moveKind rv = true := by
  match rv, h with
  | .use _, _ | .repeat _ _, _ | .aggregate (.array _) _, _ => rfl

theorem moveKind_of_tupleRvalueOk {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {dstTy : MirAst.Ty} {fields : List (Nat × TupleSpec)} {size align : Nat} {rv : Rvalue}
    (h : tupleRvalueOk layouts decls dstTy fields size align rv = true) : moveKind rv = true := by
  match rv, h with
  | .use _, _ => rfl
  | .aggregate .tuple _, _ => rfl
  | .aggregate (.adt _ 0 none) _, _ => rfl
  | .aggregate (.adt _ (.succ _) _) _, h => simp [tupleRvalueOk, aggKindMatchesTy] at h
  | .aggregate (.adt _ 0 (some _)) _, h => simp [tupleRvalueOk, aggKindMatchesTy] at h
  | .aggregate (.array _) _, h => simp [tupleRvalueOk, aggKindMatchesTy] at h

theorem retLive_set {view : List LocalSlot} (h : view[0]? ≠ some .dead) (i : Nat) {x : LocalSlot}
    (hx : x ≠ .dead) : (view.set i x)[0]? ≠ some .dead := by
  rw [List.getElem?_set]
  split
  · split <;> simp_all
  · exact h

private theorem ctxWithBorrows_cons_congr (body : CapturedMir) (ctx : Ctx)
    {e1 e2 : BorrowEntry} {b1 b2 : List BorrowEntry}
    (htag : e1.tag = e2.tag) (hloc : e1.targetLocal = e2.targetLocal)
    (hproj : e1.targetProjection = e2.targetProjection)
    (htail : ctxWithBorrows body ctx b1 = ctxWithBorrows body ctx b2) :
    ctxWithBorrows body ctx (e1 :: b1) = ctxWithBorrows body ctx (e2 :: b2) := by
  unfold ctxWithBorrows at htail ⊢
  have hbt : borrowTargets body ctx b1 = borrowTargets body ctx b2 := by
    injection htail
  congr 1
  funext t
  unfold borrowTargets lookupBorrow
  rw [htag]
  cases Nat.beq e2.tag t
  · exact congrFun hbt t
  · simp [hloc, hproj]

private theorem ctxWithBorrows_rawReborrowEntry_eq (body : CapturedMir) (ctx : Ctx)
    (tag : Nat) (mutbl : MirAst.Mutability) (parentEntry : BorrowEntry) (parentTag : Nat)
    (borrows : List BorrowEntry) :
    ctxWithBorrows body ctx (rawReborrowEntry tag mutbl parentEntry parentTag :: borrows) =
      ctxWithBorrows body ctx
        (rawPtrEntry tag mutbl ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ ::
          borrows) :=
  ctxWithBorrows_cons_congr body ctx rfl rfl rfl rfl

private theorem ctxWithBorrows_freezeTreeBorrowsOnReadAtProj_eq (body : CapturedMir) (ctx : Ctx)
    (borrows : List BorrowEntry) (targetLocal : Nat) (readerTag : Option Nat)
    (targetProj : List ProjectionElem) (off len : Nat) :
    ctxWithBorrows body ctx
        (MirSemantics.freezeTreeBorrowsOnReadAtProj borrows borrows targetLocal readerTag
          targetProj off len) =
      ctxWithBorrows body ctx borrows := by
  simp only [ctxWithBorrows, freezeTreeBorrowsOnReadAtProj_eq_map]
  congr 1
  apply borrowTargets_map_eq
  have hf := updateBorrowPermOnReadAtProj_freezeOrSelf borrows targetLocal readerTag
    targetProj off len
  exact fun e => ⟨hf.tag e, hf.targetLocal e, hf.targetProjection e⟩

private theorem ctxWithBorrows_refReborrowEntry_eq (body : CapturedMir) (ctx : Ctx)
    (tag : Nat) (bkind : MirAst.BorrowKind) (parentEntry : BorrowEntry) (parentTag : Nat)
    (borrows : List BorrowEntry) :
    ctxWithBorrows body ctx
        (refReborrowEntry tag bkind parentEntry parentTag ::
          MirSemantics.freezeTreeBorrowsOnReadAtProj borrows borrows parentEntry.targetLocal
            (some parentTag) parentEntry.targetProjection parentEntry.rangeOffset
            parentEntry.rangeLen) =
      ctxWithBorrows body ctx
        (rawPtrEntry tag (borrowKindMutbl bkind)
          ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ :: borrows) :=
  ctxWithBorrows_cons_congr body ctx rfl rfl rfl
    (ctxWithBorrows_freezeTreeBorrowsOnReadAtProj_eq body ctx borrows parentEntry.targetLocal
      (some parentTag) parentEntry.targetProjection parentEntry.rangeOffset parentEntry.rangeLen)

private theorem freezeDerefReadBorrowsAt_eq_of_lookup {locals : List LocalSlot}
    {borrows : List BorrowEntry} {r : Nat} {ptrVal : ProvenancePtr} {entry : BorrowEntry}
    (hrA : locals[r]? = some (.init (.ptr ptrVal 8)))
    (hlookup : lookupBorrow borrows ptrVal.tag = some entry) :
    MirSemantics.freezeDerefReadBorrowsAt locals r [] borrows =
      MirSemantics.freezeTreeBorrowsOnReadAtProj borrows borrows entry.targetLocal
        (some ptrVal.tag) entry.targetProjection entry.rangeOffset entry.rangeLen := by
  cases hbs : borrows with
  | nil => rw [hbs] at hlookup; simp [lookupBorrow] at hlookup
  | cons b1 rest =>
    cases rest with
    | nil =>
      rw [hbs] at hlookup
      obtain ⟨hmem, htag⟩ := lookupBorrow_mem_and_tag hlookup
      have hb1 : entry = b1 := by simpa using hmem
      subst hb1
      rw [freezeDerefReadBorrowsAt_singleton, freezeTreeBorrowsOnReadAtProj_eq_map,
        List.map_singleton, updateBorrowPermOnReadAtProj_of_descendant _ _ _ _
          (by rw [htag]; exact isBorrowDescendantOrSelf_self _ _)]
    | cons b2 bs =>
      unfold MirSemantics.freezeDerefReadBorrowsAt
      rw [← hbs]
      simp [get?, hrA, hlookup, appendProjections_nil_right]

private theorem ctxWithBorrows_freezeDerefReadBorrowsAt_eq (body : CapturedMir) (ctx : Ctx)
    {locals : List LocalSlot} {borrows : List BorrowEntry} {r : Nat}
    {ptrVal : ProvenancePtr} {entry : BorrowEntry}
    (hrA : locals[r]? = some (.init (.ptr ptrVal 8)))
    (hlookup : lookupBorrow borrows ptrVal.tag = some entry) :
    ctxWithBorrows body ctx (MirSemantics.freezeDerefReadBorrowsAt locals r [] borrows) =
      ctxWithBorrows body ctx borrows := by
  rw [freezeDerefReadBorrowsAt_eq_of_lookup hrA hlookup]
  exact ctxWithBorrows_freezeTreeBorrowsOnReadAtProj_eq body ctx borrows entry.targetLocal
    (some ptrVal.tag) entry.targetProjection entry.rangeOffset entry.rangeLen

private theorem evalStmt_assign_val_mem (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (i : Nat) (rv : Rvalue) (span : String)
    (hi : i < s.frame.locals.length) :
    (∀ v (mem1 : MirSemantics.Memory),
      evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals mem1 →
      (∀ e ∈ mem1.borrows, e.targetLocal ≠ i) →
      mem1.activeProtectors = [] →
      (s.frame.locals[i]? ≠ some .dead →
        evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts =
          .tau (.running (advanceStmt s (s.frame.locals.set i (.init v)) mem1))) ∧
      (s.frame.locals[i]? = some .dead →
        evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub)) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  have hs : s.frame.locals[i]? = some s.frame.locals[i] := by simp [hi]
  refine ⟨fun v mem1 hrv hbor1 hprot1 => ⟨fun hlive => ?_, fun hdead => ?_⟩, fun hu => ?_⟩
  · have hlive' : s.frame.locals[i] ≠ .dead := fun h => hlive (by rw [hs, h])
    have hinv : invalidateConflictingBorrows mem1.borrows i .none = mem1.borrows :=
      invalidateConflictingBorrows_of_ne mem1.borrows i .none hbor1
    simp only [evalStmt, hrv, get?, hs, set?, hi, ↓reduceIte, hprot1, hinv]
    cases hm : mem1
    cases hsl : s.frame.locals[i] with
    | dead => exact absurd hsl hlive'
    | uninit => simp_all [MirStepNode.step]
    | init _ => simp_all [MirStepNode.step]
  · simp [evalStmt, hrv, get?, hdead]
  · simp [evalStmt, hu]

private theorem evalStmt_assign_derefWrite_mem (s : MachineState) (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (p : Nat) (rv : Rvalue) (span : String) :
    (∀ v (mem1 : MirSemantics.Memory) locals',
      evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals mem1 →
      mem1.activeProtectors = [] →
      mem1.callerLocals = [] →
      writePlaceValue s.frame.locals mem1.borrows ⟨p, [.deref]⟩ v decls layouts = .ok locals' →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts =
        .tau (.running (advanceStmt s locals'
          { mem1 with
            borrows := invalidateDerefWriteBorrows s.frame.locals mem1.borrows ⟨p, [.deref]⟩ [] }))) ∧
    (∀ v (mem1 : MirSemantics.Memory),
      evalRvalue s.frame.locals rv s.memory decls layouts = .ok v s.frame.locals mem1 →
      mem1.activeProtectors = [] →
      mem1.callerLocals = [] →
      writePlaceValue s.frame.locals mem1.borrows ⟨p, [.deref]⟩ v decls layouts = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) ∧
    (evalRvalue s.frame.locals rv s.memory decls layouts = .ub →
      evalStmt s ⟨.assign ⟨p, [.deref]⟩ rv, span⟩ decls layouts = MirStepNode.fail .ub) := by
  refine ⟨fun v mem1 locals' hv hprot hcl hw => ?_,
    fun v mem1 hv hprot hcl hw => ?_, fun hu => ?_⟩
  · simp only [evalStmt, hv, evalPlaceWrite, hprot, hw]
    cases hm : mem1
    simp_all [MirStepNode.step]
  · simp only [evalStmt, hv, evalPlaceWrite, hprot, hw, hcl]
  · simp [evalStmt, hu]

private theorem BorrowsOk.derefWriteRead {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {s : MachineState} {lm : Map Gen.LocalName Ptr} (hb : BorrowsOk body ctx view s lm)
    {bb : BasicBlockData} (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    {st : MirAst.Statement} (hst : bb.statements[s.frame.stmtIdx]? = some st)
    {w r : Nat} {rv : Rvalue} (hkind : st.kind = .assign ⟨w, [.deref]⟩ rv)
    (hsrc : ptrDerefReadSrc rv = some r)
    {dw dr : LocalDecl} (hdw : body.localDecls[w]? = some dw)
    {pointeeIt : Gen.IntType} (hw_pt : ptrPointeeOf dw.ty = some (.mut, pointeeIt))
    (hdr : body.localDecls[r]? = some dr) (hr_ptr : isPtrTy dr.ty = true)
    (ptrValW ptrValR : ProvenancePtr) (entryW entryR : BorrowEntry)
    (hvw : view[w]? = some (.init (.ptr ptrValW 8)))
    (hwA : s.frame.locals[w]? = some (.init (.ptr ptrValW 8)))
    (hlookupW : lookupBorrow s.memory.borrows ptrValW.tag = some entryW)
    (hvr : view[r]? = some (.init (.ptr ptrValR 8)))
    (hrA : s.frame.locals[r]? = some (.init (.ptr ptrValR 8)))
    (hlookupR : lookupBorrow s.memory.borrows ptrValR.tag = some entryR)
    (hndisW_env : (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD w .disabled ≠ .disabled)
    (hkeeps : foreignReadKeeps (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx) r w = true) :
    let borrowsR := MirSemantics.freezeDerefReadBorrowsAt s.frame.locals r [] s.memory.borrows
    ∃ (entryW' : BorrowEntry),
      lookupBorrow borrowsR ptrValW.tag = some entryW' ∧
      (entryW'.perm = .active ∨ entryW'.perm = .reserved) ∧
      entryW'.targetLocal = entryW.targetLocal ∧
      entryW'.targetProjection = entryW.targetProjection ∧
      entryW'.rangeOffset = 0 ∧
      entryW'.rangeLen = 0 ∧
      (∀ (locals' : List LocalSlot) (slot' : LocalSlot),
        (∃ v, slot' = .init v) →
        (∀ dp pv, body.localDecls[entryW.targetLocal]? = some dp → isPtrTy dp.ty = true →
          slot' ≠ .init (.ptr pv 8)) →
        BorrowsOk body ctx (view.set entryW.targetLocal slot')
          (advanceStmt s locals'
            { s.memory with
              borrows := invalidateDerefWriteBorrows s.frame.locals borrowsR ⟨w, [.deref]⟩ [] })
          lm) := by
  have hw_ptr : isPtrTy dw.ty = true := by simp [isPtrTy, hw_pt]
  have hw_mut : isMutPtrLocal body.localDecls w = true := by
    unfold isMutPtrLocal
    rw [hdw]
    simp [hw_pt]
  have hw_lt : w < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdw).1
  have hfrz_eq := freezeDerefReadBorrowsAt_eq_of_lookup hrA hlookupR
  have hAfter := hb.freezeRead entryR.targetLocal (some ptrValR.tag) entryR.targetProjection
    entryR.rangeOffset entryR.rangeLen
  have hranges : ∀ e ∈ s.memory.borrows, e.rangeLen = 0 :=
    fun e he => by obtain ⟨_, _, _, _, hrl⟩ := hb.perm_eq he; exact hrl
  let env := ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx
  let env1 := stepForeignRead body.localDecls body.localDecls.length env r
  let borrows1 := MirSemantics.freezeTreeBorrowsOnReadAtProj s.memory.borrows s.memory.borrows
    entryR.targetLocal (some ptrValR.tag) entryR.targetProjection
    entryR.rangeOffset entryR.rangeLen
  have hok1 : PtrEnvOk body view borrows1 env1 :=
    hb.alias_ok.foreignRead hranges hdr hr_ptr hvr hlookupR
  have hndis1 : env1.getD w .disabled ≠ .disabled := by
    change (stepForeignRead body.localDecls body.localDecls.length env r).getD w .disabled ≠
      .disabled
    rw [stepForeignRead_getD hw_lt]
    split
    · next h =>
      dsimp only [env] at h
      simp [hkeeps] at h
    · exact hndisW_env
  have hf := updateBorrowPermOnReadAtProj_freezeOrSelf s.memory.borrows entryR.targetLocal
    (some ptrValR.tag) entryR.targetProjection entryR.rangeOffset entryR.rangeLen
  let entryW' := MirSemantics.updateBorrowPermOnReadAtProj s.memory.borrows entryW
    entryR.targetLocal (some ptrValR.tag) entryR.targetProjection
    entryR.rangeOffset entryR.rangeLen
  have hlkW' : lookupBorrow borrows1 ptrValW.tag = some entryW' := by
    change lookupBorrow (MirSemantics.freezeTreeBorrowsOnReadAtProj _ _ _ _ _ _ _) _ = _
    rw [freezeTreeBorrowsOnReadAtProj_eq_map, hf.lookupBorrow_map, hlookupW]
    rfl
  obtain ⟨_, _, hprotW, hroffW, hrlenW⟩ := hb.perm_eq (lookupBorrow_mem_and_tag hlookupW).1
  have hroffW' : entryW'.rangeOffset = 0 := (hf.rangeOffset entryW).trans hroffW
  have hrlenW' : entryW'.rangeLen = 0 := (hf.rangeLen entryW).trans hrlenW
  have hlocW' : entryW'.targetLocal = entryW.targetLocal := hf.targetLocal entryW
  have hprojW' : entryW'.targetProjection = entryW.targetProjection := hf.targetProjection entryW
  have hpermW' : entryW'.perm = .active ∨ entryW'.perm = .reserved := by
    have hw_ok1 := hok1 w hw_lt
    cases hst_w1 : env1.getD w .disabled with
    | disabled => exact absurd hst_w1 hndis1
    | empty =>
      rw [hst_w1] at hw_ok1
      exact False.elim (hw_ok1 dw ptrValW hdw hw_ptr hvw)
    | live _ _ =>
      rw [hst_w1] at hw_ok1
      obtain ⟨⟨eW1, hlk1, hnd1, hnf1, _⟩, _⟩ := hw_ok1 dw ptrValW hdw hw_ptr hvw
      rw [hlkW'] at hlk1
      injection hlk1 with heq1
      subst heq1
      have hnf' := hnf1 hw_mut
      cases hp : entryW'.perm <;> simp_all
  refine ⟨entryW', ?_, hpermW', hlocW', hprojW', hroffW', hrlenW',
    fun locals' slot' hinit hnp => ?_⟩
  · change lookupBorrow
        (MirSemantics.freezeDerefReadBorrowsAt s.frame.locals r [] s.memory.borrows)
        ptrValW.tag = some entryW'
    rwa [hfrz_eq]
  · change BorrowsOk body ctx (view.set entryW.targetLocal slot')
      (advanceStmt s locals'
        { s.memory with
          borrows := invalidateDerefWriteBorrows s.frame.locals
            (MirSemantics.freezeDerefReadBorrowsAt s.frame.locals r [] s.memory.borrows)
            ⟨w, [.deref]⟩ [] })
      lm
    rw [hfrz_eq]
    change BorrowsOk body ctx (view.set entryW.targetLocal slot')
      (advanceStmt s locals'
        { s.memory with
          borrows := invalidateDerefWriteBorrows s.frame.locals borrows1 ⟨w, [.deref]⟩ [] })
      lm
    obtain ⟨entry_slot, relOff_w, hoff0_w, hlk_slot, htspec_w⟩ :=
      hAfter.2.2.2.2.2 w dw .mut pointeeIt ptrValW hdw hw_pt hvw
    rw [hlkW'] at hlk_slot
    injection hlk_slot with heq_slot
    subst heq_slot
    have hfull :
        MirSemantics.resolveDerefWriteFullProj s.frame.locals s.frame.locals
          (.ptr ptrValW 8) entryW' [] = entryW'.targetProjection :=
      resolveDerefWriteFullProj_of_ptrTargetSpec s.frame.locals s.frame.locals ptrValW 8 entryW' []
        htspec_w hoff0_w
    let upd : BorrowEntry → BorrowEntry := fun e =>
      MirSemantics.updateBorrowPermTreeAtProj borrows1 e entryW'.targetLocal
        (some ptrValW.tag) entryW'.targetProjection 0 0
    have hmap :
        invalidateDerefWriteBorrows s.frame.locals borrows1 ⟨w, [.deref]⟩ [] =
          borrows1.map upd :=
      invalidateDerefWriteBorrows_eq_map s.frame.locals borrows1 w ptrValW entryW'
        hwA hlkW' hrlenW' hroffW' hfull
    have hupd_fields : ∀ e,
        (upd e).tag = e.tag ∧ (upd e).targetLocal = e.targetLocal ∧
        (upd e).targetProjection = e.targetProjection ∧
        (upd e).rangeOffset = e.rangeOffset ∧ (upd e).rangeLen = e.rangeLen ∧
        (upd e).protector = e.protector ∧ (upd e).parentTag = e.parentTag := fun e =>
      updateBorrowPermTreeAtProj_fields borrows1 e entryW'.targetLocal
        (some ptrValW.tag) entryW'.targetProjection 0 0
    have hperm_eq1 : ∀ e ∈ borrows1,
        e.protector = none ∧ e.rangeOffset = 0 ∧ e.rangeLen = 0 := by
      intro e he
      change e ∈ MirSemantics.freezeTreeBorrowsOnReadAtProj _ _ _ _ _ _ _ at he
      rw [freezeTreeBorrowsOnReadAtProj_eq_map, List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      obtain ⟨_, _, hprot0, hroff0, hrlen0⟩ := hb.perm_eq he0
      exact ⟨(hf.protector e0).trans hprot0, (hf.rangeOffset e0).trans hroff0,
        (hf.rangeLen e0).trans hrlen0⟩
    refine {
      nextTag_pos := hb.nextTag_pos
      tags_pos := fun e' he' => by
        dsimp only [advanceStmt] at he' ⊢
        rw [hmap, List.mem_map] at he'
        obtain ⟨e, he, rfl⟩ := he'
        rw [(hupd_fields e).1]
        exact hAfter.1 e he
      tags_lt := fun e' he' => by
        dsimp only [advanceStmt] at he' ⊢
        rw [hmap, List.mem_map] at he'
        obtain ⟨e, he, rfl⟩ := he'
        rw [(hupd_fields e).1]
        exact hAfter.2.1 e he
      tags_nodup := by
        dsimp only [advanceStmt]
        rw [hmap]
        have htags_eq : (borrows1.map upd).map (·.tag) = borrows1.map (·.tag) := by
          rw [List.map_map]
          exact List.map_congr_left (fun e _ => (hupd_fields e).1)
        rw [htags_eq]
        exact hAfter.2.2.1
      entries_ok := fun e' he' => by
        dsimp only [advanceStmt] at he'
        rw [hmap, List.mem_map] at he'
        obtain ⟨e, he, rfl⟩ := he'
        obtain ⟨_, pointeeIt', relOff', _, hk_addr, htspec'⟩ := hAfter.2.2.2.1 e he
        obtain ⟨hprot_e, hroff_e, hrlen_e⟩ := hperm_eq1 e he
        obtain ⟨_, hloc, hproj, hroff_u, hrlen_u, hprot_u, _⟩ := hupd_fields e
        obtain ⟨mutbl', hform'⟩ := borrowEntry_form_of_unranged (upd e)
          (hprot_u.trans hprot_e) (hroff_u.trans hroff_e) (hrlen_u.trans hrlen_e)
        refine ⟨mutbl', pointeeIt', relOff', hform', hloc ▸ hk_addr, ?_⟩
        rwa [hloc, hproj]
      entries_place := fun e' he' => by
        dsimp only [advanceStmt] at he'
        rw [hmap, List.mem_map] at he'
        obtain ⟨e, he, rfl⟩ := he'
        rw [(hupd_fields e).2.1, (hupd_fields e).2.2.1]
        exact hAfter.2.2.2.2.1 e he
      target_init := fun hfrag k hk => by
        obtain ⟨v0, hv0⟩ := hb.target_init hfrag k hk
        by_cases htk : entryW.targetLocal = k
        · subst htk
          obtain ⟨v', rfl⟩ := hinit
          have hlt : entryW.targetLocal < view.length := (List.getElem?_eq_some_iff.mp hv0).1
          exact ⟨v', List.getElem?_set_self hlt⟩
        · rw [List.getElem?_set_ne htk]
          exact ⟨v0, hv0⟩
      target_ptrs := fun hfrag k hk => by
        obtain ⟨hnd, hlmk, hd⟩ := hb.target_ptrs hfrag k hk
        refine ⟨?_, hlmk, hd⟩
        by_cases htk : entryW.targetLocal = k
        · subst htk
          obtain ⟨v', rfl⟩ := hinit
          by_cases hlt : entryW.targetLocal < view.length
          · rw [List.getElem?_set_self hlt]; simp
          · rw [List.set_eq_of_length_le (Nat.not_lt.mp hlt)]
            exact hnd
        · rw [List.getElem?_set_ne htk]
          exact hnd
      alias_ok := ?_
      ptr_slots := fun p dp mutbl pointeeIt' pv hdp hpt hv => by
        have hp_ptr : isPtrTy dp.ty = true := by simp [isPtrTy, hpt]
        have hv_old : view[p]? = some (.init (.ptr pv 8)) := by
          by_cases htp : entryW.targetLocal = p
          · subst htp
            by_cases hlt : entryW.targetLocal < view.length
            · rw [List.getElem?_set_self hlt] at hv
              injection hv with hs
              exact False.elim (hnp dp pv hdp hp_ptr hs)
            · rwa [List.set_eq_of_length_le (Nat.not_lt.mp hlt)] at hv
          · rwa [List.getElem?_set_ne htp] at hv
        obtain ⟨e_p, relOff', hoff0', hlk_p, htspec_p⟩ :=
          hAfter.2.2.2.2.2 p dp mutbl pointeeIt' pv hdp hpt hv_old
        obtain ⟨_, hloc_p, hproj_p, _⟩ := hupd_fields e_p
        refine ⟨upd e_p, relOff', hoff0', ?_, ?_⟩
        · dsimp only [advanceStmt]
          rw [hmap, lookupBorrow_map_eq (fun e => (hupd_fields e).1) pv.tag, hlk_p]
          rfl
        · rwa [hloc_p, hproj_p] }
    dsimp only [advanceStmt]
    rw [hmap, Nat.add_eq, ptrEnvBefore_succ hbb hst]
    simp only [ptrStmtStep, hkind, hsrc]
    apply PtrEnvOk.set_nonptr _ entryW.targetLocal slot' hnp
    have hw_ok := hok1 w hw_lt
    unfold stepDerefWrite
    cases hst_w : env1.getD w .disabled with
    | empty =>
      rw [hst_w] at hw_ok
      exact False.elim (hw_ok dw ptrValW hdw hw_ptr hvw)
    | disabled =>
      intro q hq
      rw [getD_map_range _ _ _ hq]
      trivial
    | live wTarget wPeers _wHot =>
      rw [hst_w] at hw_ok
      obtain ⟨⟨entry_w, hlk_w, _, _, _, hw_tgt⟩, hw_peers⟩ := hw_ok dw ptrValW hdw hw_ptr hvw
      rw [hlkW'] at hlk_w
      injection hlk_w with heq_w
      subst heq_w
      intro q hq
      rw [getD_map_range _ _ _ hq]
      have hq_ok := hok1 q hq
      cases hst_q : env1.getD q .disabled with
      | empty =>
        rw [hst_q] at hq_ok
        exact hq_ok
      | disabled =>
        trivial
      | live qTarget qPeers _qHot =>
        rw [hst_q] at hq_ok
        by_cases hkeep : (wPeers.contains q || targetsDefinitelyDisjoint qTarget wTarget) = true
        · simp only [hkeep, ↓reduceIte]
          intro dq pv_q hdq hq_ptr hvq
          obtain ⟨⟨e_q, hlk_q, hndis_q, hnf_q, _, hq_tgt⟩, hq_peers⟩ := hq_ok dq pv_q hdq hq_ptr hvq
          obtain ⟨_, he_q_tag⟩ := lookupBorrow_mem_and_tag hlk_q
          have hkeep_q : upd e_q = e_q ∨ upd e_q = { e_q with perm := .active } := by
            apply updateBorrowPermTreeAtProj_self_or_disjoint_keep
            intro hloc
            have hkeep' : wPeers.contains q = true ∨
                targetsDefinitelyDisjoint qTarget wTarget = true := by
              simpa only [Bool.or_eq_true] using hkeep
            rcases hkeep' with hpeer | hdisj
            · have hdesc := hw_peers q (List.contains_iff_mem.mp hpeer) dq pv_q hdq hq_ptr hvq
              exact .inl (he_q_tag.symm ▸ hdesc)
            · by_cases htag_eq : e_q.tag = ptrValW.tag
              · exact .inl (htag_eq ▸ isBorrowDescendantOrSelf_self _ _)
              · right
                refine ⟨htag_eq, ?_⟩
                cases qTarget with
                | none => simp [targetsDefinitelyDisjoint] at hdisj
                | some qp =>
                  cases wTarget with
                  | none => simp [targetsDefinitelyDisjoint] at hdisj
                  | some wp =>
                    obtain ⟨k1, p1⟩ := qp
                    obtain ⟨k2, p2⟩ := wp
                    have h1 := hq_tgt (k1, p1) rfl
                    have h2 := hw_tgt (k2, p2) rfl
                    simp only [Prod.mk.injEq] at h1 h2
                    obtain ⟨rfl, rfl⟩ := h1
                    obtain ⟨rfl, rfl⟩ := h2
                    simp only [targetsDefinitelyDisjoint, hloc, ne_eq, not_true_eq_false,
                      decide_false, Bool.false_or, Bool.not_eq_true'] at hdisj
                    rwa [← borrowProjOverlap_borrowProjSteps]
          refine ⟨⟨upd e_q, ?_, ?_, ?_, ?_, ?_⟩,
            fun r' hr' dr' pv_r' hdr' hptr' hvr' => by
              rw [isBorrowDescendantOrSelf_map_eq (fun e => (hupd_fields e).1)
                (fun e => (hupd_fields e).2.2.2.2.2.2)]
              exact hq_peers r' hr' dr' pv_r' hdr' hptr' hvr'⟩
          · rw [lookupBorrow_map_eq (fun e => (hupd_fields e).1) pv_q.tag, hlk_q]
            rfl
          · rcases hkeep_q with hsame | hact_q
            · rwa [hsame]
            · simp [hact_q]
          · intro hmut_q
            rcases hkeep_q with hsame | hact_q
            · rw [hsame]; exact hnf_q hmut_q
            · simp [hact_q]
          · intro _ h; cases h
          · intro qp hqp
            rw [(hupd_fields e_q).2.1, (hupd_fields e_q).2.2.1]
            exact hq_tgt qp hqp
        · simp only [hkeep, Bool.false_eq_true, ↓reduceIte]
          trivial

private theorem GoodSize.lt_two_pow_63 {n : Nat} (h : GoodSize n) : n < 2 ^ 63 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem splitLastConstantIndex?_allFields {projs : List ProjectionElem}
    (h : allFields projs = true) :
    MirSemantics.splitLastConstantIndex? projs = none := by
  induction projs with
  | nil => rfl
  | cons e rest ih =>
    cases e <;> simp [allFields] at h
    cases rest with
    | nil => rfl
    | cons e2 r2 => simp [MirSemantics.splitLastConstantIndex?, ih h]

private theorem splitLastSubslice?_allFields {projs : List ProjectionElem}
    (h : allFields projs = true) :
    MirSemantics.splitLastSubslice? projs = none := by
  induction projs with
  | nil => rfl
  | cons e rest ih =>
    cases e <;> simp [allFields] at h
    cases rest with
    | nil => rfl
    | cons e2 r2 => simp [MirSemantics.splitLastSubslice?, ih h]

private theorem splitLastField?_allFields (idx : Nat) (fieldTy : MirAst.Ty)
    {rest : List ProjectionElem} (h : allFields rest = true) :
    ∃ init fIdx fTy,
      MirSemantics.splitLastField? (.field idx fieldTy :: rest) = some (init, fIdx, fTy) := by
  induction rest generalizing idx fieldTy with
  | nil => exact ⟨[], idx, fieldTy, rfl⟩
  | cons e r ih =>
    cases e with
    | field idx2 fieldTy2 =>
      simp only [allFields] at h
      obtain ⟨init, fIdx, fTy, hsub⟩ := ih idx2 fieldTy2 h
      exact ⟨.field idx fieldTy :: init, fIdx, fTy, by simp [MirSemantics.splitLastField?, hsub]⟩
    | _ => simp [allFields] at h

private theorem splitAfterLastSeqProj_allFields {projs : List ProjectionElem}
    (h : allFields projs = true) :
    MirSemantics.splitAfterLastSeqProj projs = ([], projs) := by
  induction projs with
  | nil => rfl
  | cons e rest ih =>
    cases e <;> simp [allFields] at h
    simp [MirSemantics.splitAfterLastSeqProj, ih h]

private theorem rigidTyByteSize_of_intTypeOf (layouts : Layout.LayoutTable) {t : MirAst.Ty}
    {it : Gen.IntType} (h : intTypeOf t = some it) :
    MirSemantics.rigidTyByteSize layouts t = some it.size.bytes ∧ it.size.bytes < 2 ^ 63 := by
  have hcast := intCastTargetBytes_of_intTypeOf h
  unfold intTypeOf at h
  obtain ⟨⟨sg, n⟩, hb, heq⟩ := Option.map_eq_some_iff.mp h
  subst heq
  refine ⟨?_, (intTyBytes_good hb).lt_two_pow_63⟩
  cases hk : t.kind <;> rw [hk] at hb hcast <;> try (simp [intTyBytes] at hb)
  all_goals
    rw [MirSemantics.rigidTyByteSize, hk]
    simp [MirSemantics.rigidTyKindByteSize, hcast]

private theorem normalizeAdjacentSubslicesAux_allFields :
    ∀ {projs : List ProjectionElem}, allFields projs = true →
      MirSemantics.normalizeAdjacentSubslicesAux none projs = projs
  | [], _ => rfl
  | e :: rest, h => by
    cases e <;> simp [allFields] at h
    exact congrArg (_ :: ·) (normalizeAdjacentSubslicesAux_allFields h)

private theorem normalizeAdjacentSubslices_allFields {projs : List ProjectionElem}
    (h : allFields projs = true) :
    MirSemantics.normalizeAdjacentSubslices projs = projs :=
  normalizeAdjacentSubslicesAux_allFields h

private theorem projHasSubslice_allFields {projs : List ProjectionElem}
    (h : allFields projs = true) :
    MirSemantics.projHasSubslice projs = false := by
  induction projs with
  | nil => rfl
  | cons e rest ih =>
    cases e <;> simp [allFields] at h
    exact ih h

mutual

private inductive ValueShapeEq : Value → Value → Prop where
  | scalar (sc1 sc2 : ScalarInt) : sc1.sizeBytes = sc2.sizeBytes →
      ValueShapeEq (.scalar sc1) (.scalar sc2)
  | aggregate (v : MirAst.VariantIdx) (fs1 fs2 : List Value) :
      ValueListShapeEq fs1 fs2 →
      ValueShapeEq (.aggregate v fs1) (.aggregate v fs2)
  | unit : ValueShapeEq .unit .unit

private inductive ValueListShapeEq : List Value → List Value → Prop where
  | nil : ValueListShapeEq [] []
  | cons {v1 v2 : Value} {fs1 fs2 : List Value} :
      ValueShapeEq v1 v2 → ValueListShapeEq fs1 fs2 →
      ValueListShapeEq (v1 :: fs1) (v2 :: fs2)

end

private theorem ValueListShapeEq.length_eq :
    ∀ {fs1 fs2 : List Value}, ValueListShapeEq fs1 fs2 → fs1.length = fs2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hr => congrArg (· + 1) hr.length_eq

private theorem forall2_get?_shape :
    ∀ {fs1 fs2 : List Value}, ValueListShapeEq fs1 fs2 → ∀ (idx : Nat),
      (fs1[idx]? = none ∧ fs2[idx]? = none) ∨
      ∃ v1 v2, fs1[idx]? = some v1 ∧ fs2[idx]? = some v2 ∧ ValueShapeEq v1 v2
  | [], [], .nil, _ => .inl ⟨rfl, rfl⟩
  | v1 :: _, v2 :: _, .cons hv _, 0 => .inr ⟨v1, v2, rfl, rfl, hv⟩
  | _ :: _, _ :: _, .cons _ hr, n + 1 => forall2_get?_shape hr n

mutual

private theorem tupleSpec_valOk_shape :
    ∀ (spec : TupleSpec) (v : Value), spec.valOk v = true → ValueShapeEq v spec.zeroVal
  | .scalar it, v, h => by
    cases v with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .scalar sc ⟨0, it.size.bytes⟩ h.1
    | _ => simp [TupleSpec.valOk] at h
  | .tuple fields _ _, v, h => by
    cases v with
    | aggregate aggVar vals =>
      cases aggVar with
      | zero =>
        simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at h
        exact .aggregate 0 vals (TupleSpec.zeroFieldVals fields)
          (tupleSpec_fieldsValOk_shape fields vals h.2)
      | succ _ => simp [TupleSpec.valOk] at h
    | _ => simp [TupleSpec.valOk] at h

private theorem tupleSpec_fieldsValOk_shape :
    ∀ (fields : List (Nat × TupleSpec)) (vals : List Value),
      TupleSpec.fieldsValOk fields vals = true →
      ValueListShapeEq vals (TupleSpec.zeroFieldVals fields)
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [TupleSpec.fieldsValOk] at h
  | _ :: _, [], h => by simp [TupleSpec.fieldsValOk] at h
  | (_, s) :: rf, v :: rv, h => by
    simp only [TupleSpec.fieldsValOk, Bool.and_eq_true] at h
    exact .cons (tupleSpec_valOk_shape s v h.1) (tupleSpec_fieldsValOk_shape rf rv h.2)

end

private theorem declSlotOk_valueShapeEq {layouts : Layout.LayoutTable} {d : LocalDecl} {v : Value}
    (hslot : DeclSlotOk d (.init v) layouts)
    (hkind : (∃ it, intTypeOf d.ty = some it) ∨
      (∃ elemIt count, arrayTypeOf d.ty = some (elemIt, count)) ∨
      (∃ fields size align, tupleTypeOf layouts d.ty = some (fields, size, align))) :
    ValueShapeEq v (canonicalDeclVal layouts d) := by
  rcases hkind with ⟨it, hit⟩ | ⟨elemIt, count, ha⟩ | ⟨fields, size, align, ht⟩
  · have hsc := scalarTypeOf_int hit
    have hs := (DeclSlotOk_of_scalarTypeOf (layouts := layouts) hsc (.init v)).mp hslot
    rw [tyOf_of_scalarTypeOf (layouts := layouts) hsc] at hs
    cases v with
    | scalar sc =>
      simp only [SlotOk, tyBytes] at hs
      simp only [canonicalDeclVal, hit]
      exact .scalar sc ⟨0, it.size.bytes⟩ hs.1
    | unit => exact False.elim hs
    | ptr _ _ => exact False.elim hs
    | aggregate v0 fs =>
      simp only [SlotOk] at hs
      cases v0 with
      | succ _ => exact False.elim hs
      | zero =>
        rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨_, _⟩⟩⟩
        · exact False.elim hs
        · cases f0 <;> exact False.elim hs
        · cases f0 <;> cases f1 <;> try exact False.elim hs
          simp only [Nat.zero_eq, tupleIntOfTy] at hs
          rcases hs with ⟨_, htu_bad, _⟩
          cases htu_bad
        · cases f0 <;> cases f1 <;> exact False.elim hs
  · have hni : intTypeOf d.ty = none := by
      cases htk : d.ty.kind <;> simp [arrayTypeOf, intTypeOf, intTyBytes, htk] at ha ⊢
    have hsloti := (DeclSlotOk_of_arrayTypeOf (layouts := layouts) ha (.init v)).mp hslot
    match v, hsloti with
    | .aggregate 0 elems, ⟨hlen, he⟩ =>
      simp only [canonicalDeclVal, hni, ha]
      rw [← hlen]
      have hrep : ∀ (es : List Value), (∀ x ∈ es, ElemOk elemIt x) →
          ValueListShapeEq es
            (List.replicate es.length (.scalar ⟨0, elemIt.size.bytes⟩)) := by
        intro es hes
        induction es with
        | nil => exact .nil
        | cons x xs ih =>
          have hx := hes x (List.mem_cons_self ..)
          cases x with
          | scalar sc =>
            exact .cons (.scalar sc ⟨0, elemIt.size.bytes⟩ hx.1)
              (ih (fun y hy => hes y (List.mem_cons_of_mem _ hy)))
          | _ => exact False.elim hx
      exact .aggregate 0 elems _ (hrep elems he)
  · have hni : intTypeOf d.ty = none := (not_scalar_of_tupleTypeOf ht).2.2.2.1
    have harr : arrayTypeOf d.ty = none := (not_scalar_of_tupleTypeOf ht).2.2.2.2
    have hsloti := (DeclSlotOk_of_tupleTypeOf ht (.init v)).mp hslot
    simp only [canonicalDeclVal, hni, harr, ht]
    exact tupleSpec_valOk_shape _ v hsloti.2

private theorem mirValue_length_eq : ∀ (xs : List Value), length xs = xs.length
  | [] => rfl
  | _ :: tl => congrArg (· + 1) (mirValue_length_eq tl)

private theorem ValueShapeEq.lookupAggregateLayout?_eq (layouts : Layout.LayoutTable)
    (curTy : MirAst.Ty) (aggVar : MirAst.VariantIdx) {fs1 fs2 : List Value}
    (h : ValueListShapeEq fs1 fs2) :
    MirSemantics.lookupAggregateLayout? layouts curTy aggVar fs1 =
      MirSemantics.lookupAggregateLayout? layouts curTy aggVar fs2 := by
  have hlen' : length fs1 = length fs2 := by
    rw [mirValue_length_eq, mirValue_length_eq, h.length_eq]
  unfold MirSemantics.lookupAggregateLayout?
  dsimp only
  rw [hlen']

private theorem ValueShapeEq.aggregateFieldByteOffset?_some_eq (layouts : Layout.LayoutTable)
    (encTy : MirAst.Ty) (aggVar : MirAst.VariantIdx) (fieldIdx : Nat) {fs1 fs2 : List Value}
    (h : ValueListShapeEq fs1 fs2) :
    MirSemantics.aggregateFieldByteOffset? layouts (some encTy) none
        (some (.aggregate aggVar fs1)) fieldIdx =
      MirSemantics.aggregateFieldByteOffset? layouts (some encTy) none
        (some (.aggregate aggVar fs2)) fieldIdx := by
  unfold MirSemantics.aggregateFieldByteOffset?
  dsimp only
  rw [ValueShapeEq.lookupAggregateLayout?_eq layouts encTy aggVar h]
  split
  · rfl
  · rcases encTy with ⟨ek, el⟩
    cases ek with
    | adt _ _ | closure _ _ =>
      cases aggVar with
      | succ _ => rfl
      | zero =>
        change (match (none : Option MirAst.VariantIdx), some (Value.aggregate 0 fs1) with
            | none, some (Value.aggregate 0 (_ :: [])) =>
              match Nat.beq fieldIdx 0 with | true => some 0 | false => none
            | _, _ => none) =
          (match (none : Option MirAst.VariantIdx), some (Value.aggregate 0 fs2) with
            | none, some (Value.aggregate 0 (_ :: [])) =>
              match Nat.beq fieldIdx 0 with | true => some 0 | false => none
            | _, _ => none)
        cases h with
        | nil => rfl
        | cons _ hr => cases hr <;> rfl
    | _ => rfl

private theorem ValueShapeEq.projectionChainByteOffset?_allFields_eq
    (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    {projs : List ProjectionElem} (hall : allFields projs = true) :
    ∀ (curTy : MirAst.Ty) (accOff : Nat) {v1 v2 : Value},
      ValueShapeEq v1 v2 →
      MirSemantics.projectionChainByteOffset? layouts (some curTy) (some v1) none accOff decls projs =
        MirSemantics.projectionChainByteOffset? layouts (some curTy) (some v2) none accOff decls projs := by
  induction projs with
  | nil => intro _ _ _ _ _; rfl
  | cons e rest ih =>
    intro curTy accOff v1 v2 hv
    cases e with
    | field fieldIdx fieldTy =>
      simp only [allFields] at hall
      cases hv with
      | scalar sc1 sc2 _ =>
        unfold MirSemantics.projectionChainByteOffset? MirSemantics.aggregateFieldByteOffset?
        rfl
      | unit => rfl
      | aggregate aggVar fs1 fs2 hfs =>
        unfold MirSemantics.projectionChainByteOffset?
        dsimp only
        rw [ValueShapeEq.aggregateFieldByteOffset?_some_eq layouts
          (MirSemantics.resolveTyWithLocalDecls decls layouts curTy) aggVar fieldIdx hfs]
        cases MirSemantics.aggregateFieldByteOffset? layouts
            (some (MirSemantics.resolveTyWithLocalDecls decls layouts curTy)) none
            (some (.aggregate aggVar fs2)) fieldIdx with
        | none => rfl
        | some stepOff =>
          cases aggVar with
          | succ _ => rfl
          | zero =>
            dsimp only
            rcases forall2_get?_shape hfs fieldIdx with ⟨hn1, hn2⟩ | ⟨u1, u2, hu1, hu2, huv⟩
            · simp [get?, hn1, hn2]
            · simp only [get?, hu1, hu2]
              exact ih hall _ _ huv
    | _ => simp [allFields] at hall

private theorem ValueShapeEq.projectionChainByteOffset?_constIdx_eq
    (layouts : Layout.LayoutTable) (decls : List LocalDecl) {curTy : MirAst.Ty}
    {elemIt : Gen.IntType} {count : Nat} (ha : arrayTypeOf curTy = some (elemIt, count))
    (accOff rawIdx minLen : Nat) (fromEnd : Bool) {v1 v2 : Value} (hv : ValueShapeEq v1 v2) :
    MirSemantics.projectionChainByteOffset? layouts (some curTy) (some v1) none accOff decls
        [.constantIndex rawIdx minLen fromEnd] =
      MirSemantics.projectionChainByteOffset? layouts (some curTy) (some v2) none accOff decls
        [.constantIndex rawIdx minLen fromEnd] := by
  unfold arrayTypeOf at ha
  cases htk : curTy.kind with
  | array ek c =>
    have hrk : (MirSemantics.resolveTyWithLocalDecls decls layouts curTy).kind = .array ek c := by
      rw [resolveTyWithLocalDecls_kind, htk]
    cases hv with
    | scalar _ _ _ =>
      unfold MirSemantics.projectionChainByteOffset?
      rfl
    | unit => rfl
    | aggregate aggVar fs1 fs2 hfs =>
      cases aggVar with
      | succ _ =>
        unfold MirSemantics.projectionChainByteOffset?
        rfl
      | zero =>
        have hlen : length fs1 = length fs2 := by
          rw [mirValue_length_eq, mirValue_length_eq, hfs.length_eq]
        unfold MirSemantics.projectionChainByteOffset?
        simp only [Nat.zero_eq]
        rw [hrk, hlen]
        generalize (Layout.LayoutTable.lookup layouts
          (MirSemantics.resolveTyWithLocalDecls decls layouts curTy).layoutIdx) = lkOpt
        cases lkOpt with
        | none => simp
        | some l =>
          rcases l with ⟨lsz, lal, lbr, lfields, lvars, lunin, lfls⟩
          cases lfields <;> cases lfls <;> simp
  | _ => rw [htk] at ha; cases ha

private theorem ValueShapeEq.checkTargetPlaceAlignWalk_allFields_eq
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (reqAlign : Nat)
    {projs : List ProjectionElem} (hall : allFields projs = true) :
    ∀ (curTy : MirAst.Ty) {v1 v2 : Value},
      ValueShapeEq v1 v2 →
      MirSemantics.checkTargetPlaceAlignWalk decls layouts reqAlign 0 (some curTy) (some v1) none projs =
        MirSemantics.checkTargetPlaceAlignWalk decls layouts reqAlign 0 (some curTy) (some v2) none projs := by
  induction projs with
  | nil => intro _ _ _ _; rfl
  | cons e rest ih =>
    intro curTy v1 v2 hv
    cases e with
    | field fieldIdx fieldTy =>
      have hall' : allFields rest = true := by simpa [allFields] using hall
      unfold MirSemantics.checkTargetPlaceAlignWalk
      dsimp only
      rw [ValueShapeEq.projectionChainByteOffset?_allFields_eq layouts decls hall curTy 0 hv]
      split
      · rfl
      · cases hv with
        | scalar _ _ _ => rfl
        | unit => rfl
        | aggregate aggVar fs1 fs2 hfs =>
          cases aggVar with
          | succ _ => rfl
          | zero =>
            dsimp only
            rcases forall2_get?_shape hfs fieldIdx with ⟨hn1, hn2⟩ | ⟨u1, u2, hu1, hu2, huv⟩
            · simp [get?, hn1, hn2]
            · simp only [get?, hu1, hu2]
              exact ih hall' _ huv
    | _ => simp [allFields] at hall

private theorem ValueShapeEq.checkTargetPlaceAlign_eq
    {decls : List LocalDecl} {layouts : Layout.LayoutTable}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    (tyOpt : Option MirAst.Ty) (entry : BorrowEntry) (ptrVal : ProvenancePtr)
    (hoff0 : ptrVal.offsetBytes = 0) {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec layouts decls ⟨entry.targetLocal, entry.targetProjection⟩ =
      some (pointeeIt, relOff))
    {dk : LocalDecl} (hdk : decls[entry.targetLocal]? = some dk)
    {v1 v2 : Value} (hv : ValueShapeEq v1 v2) :
    MirSemantics.checkTargetPlaceAlign decls layouts tyOpt entry ptrVal (some v1) =
      MirSemantics.checkTargetPlaceAlign decls layouts tyOpt
        { tag := 0, targetLocal := entry.targetLocal, targetProjection := entry.targetProjection,
          perm := .active }
        ⟨0, 0⟩ (some v2) := by
  unfold MirSemantics.checkTargetPlaceAlign
  rw [hoff0]
  dsimp only
  cases tyOpt with
  | none => rfl
  | some ty =>
    simp only [get?, hdk]
    split
    · rfl
    · obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
      rcases hcases with ⟨hproj, _, _, _⟩ |
        ⟨off, minL, fe, dk', count, hproj, hdk', ha, _, _⟩ |
        ⟨idx, fTy, rest, hproj, _, _, _, _, _, _, _, _, _, hres⟩
      · dsimp only at hproj; rw [hproj]; rfl
      · dsimp only at hproj hdk'
        rw [hdk] at hdk'; injection hdk' with hd_eq; subst hd_eq
        rw [hproj]
        unfold MirSemantics.checkTargetPlaceAlignWalk
        dsimp only
        rw [ValueShapeEq.projectionChainByteOffset?_constIdx_eq layouts decls ha 0 off minL fe hv]
        split
        · rfl
        · unfold MirSemantics.checkTargetPlaceAlignWalk; rfl
      · dsimp only at hproj; rw [hproj]
        exact ValueShapeEq.checkTargetPlaceAlignWalk_allFields_eq decls layouts _
          (resolveFieldPath_allFields hres) dk.ty hv

private theorem ptrDeclLayoutsOk_ptr_spec {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true) {p : Nat} {dp : LocalDecl}
    {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : body.localDecls[p]? = some dp)
    (hp_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt)) :
    ∃ pTy,
      MirSemantics.placeTyResolved body.localDecls body.layouts ⟨p, [.deref]⟩ = some pTy ∧
      let rAccTy := MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy
      MirSemantics.tyScalarBytes rAccTy = some pointeeIt.size.bytes ∧
      MirSemantics.tyByteSize body.localDecls body.layouts pTy = some pointeeIt.size.bytes ∧
      MirSemantics.tyByteSize body.localDecls body.layouts rAccTy = some pointeeIt.size.bytes ∧
      (match rAccTy.kind with | .bool | .char | .never => false | _ => true) = true ∧
      ∀ q ∈ bodyDirectBorrowPlaces body, ∀ dk, body.localDecls[q.local_]? = some dk →
        MirSemantics.checkTargetPlaceAlign body.localDecls body.layouts (some pTy)
          { tag := 0, targetLocal := q.local_, targetProjection := q.projection, perm := .active }
          ⟨0, 0⟩ (some (canonicalDeclVal body.layouts dk)) = true ∧
        MirSemantics.checkTargetPlaceAlign body.localDecls body.layouts (some rAccTy)
          { tag := 0, targetLocal := q.local_, targetProjection := q.projection, perm := .active }
          ⟨0, 0⟩ (some (canonicalDeclVal body.layouts dk)) = true := by
  unfold ptrDeclLayoutsOk at hdlo
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hdlo
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hp := hdlo.1 p hp_lt
  rw [hdp] at hp
  dsimp only at hp
  rw [hp_pt] at hp
  dsimp only at hp
  cases hpty : MirSemantics.placeTyResolved body.localDecls body.layouts ⟨p, [.deref]⟩ with
  | none => rw [hpty] at hp; cases hp
  | some pTy =>
    rw [hpty] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨pTy, rfl, h1, h2, h3, h4, fun q hq dk hdk => ?_⟩
    have hq' := h5 q hq
    rw [hdk] at hq'
    simpa [Bool.and_eq_true] using hq'

private theorem ptrDeclLayoutsOk_place_spec {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true) {q : Place}
    (hq : q ∈ bodyDirectBorrowPlaces body) {dk : LocalDecl}
    (hdk : body.localDecls[q.local_]? = some dk)
    {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff)) :
    let canonLocals : List LocalSlot :=
      body.localDecls.map (fun d => .init (canonicalDeclVal body.layouts d))
    let qEntry : BorrowEntry :=
      { tag := 0, targetLocal := q.local_, targetProjection := q.projection, perm := .active }
    MirSemantics.borrowPlaceByteOffset? canonLocals [] body.localDecls body.layouts qEntry =
      some relOff ∧
    (q.projection = [] →
      MirSemantics.tyByteSize body.localDecls body.layouts
        (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts dk.ty) =
        some pointeeIt.size.bytes) ∧
    (∀ off minL fe, q.projection = [.constantIndex off minL fe] →
      MirSemantics.resolveSeqContainerElemByteStride body.localDecls body.layouts q.local_ [] [] =
        pointeeIt.size.bytes ∧
      ∃ projTy, MirSemantics.placeTyResolved body.localDecls body.layouts q = some projTy ∧
        MirSemantics.tyByteSize body.localDecls body.layouts projTy = some pointeeIt.size.bytes) ∧
    (∀ idx fTy rest, q.projection = .field idx fTy :: rest →
      ∀ fields size align, tupleTypeOf body.layouts dk.ty = some (fields, size, align) →
        MirSemantics.tyByteSize body.localDecls body.layouts
          (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts dk.ty) = some size ∧
        MirSemantics.projectionChainByteOffset? body.layouts
          (some (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts dk.ty))
          (some (canonicalDeclVal body.layouts dk)) none 0 body.localDecls q.projection =
          some relOff ∧
        ∃ projTy, MirSemantics.placeTyResolved body.localDecls body.layouts q = some projTy ∧
          MirSemantics.tyByteSize body.localDecls body.layouts projTy = some pointeeIt.size.bytes) := by
  unfold ptrDeclLayoutsOk at hdlo
  simp only [Bool.and_eq_true, List.all_eq_true] at hdlo
  have h := hdlo.2 q hq
  rw [hdk, htspec] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun hp => ?_, fun off minL fe hp => ?_, fun idx fTy rest hp fields size align ht => ?_⟩
  · have h2 := h.2; rw [hp] at h2; simpa [decide_eq_true_eq] using h2
  · have h2 := h.2; rw [hp] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    refine ⟨h2.1, ?_⟩
    cases hpr : MirSemantics.placeTyResolved body.localDecls body.layouts q with
    | none => rw [hpr] at h2; simp at h2
    | some projTy =>
      have h2r := h2.2
      rw [hpr] at h2r
      exact ⟨projTy, rfl, by simpa [decide_eq_true_eq] using h2r⟩
  · have h2 := h.2; rw [hp] at h2
    simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at h2
    refine ⟨h2.1.1, by rw [hp]; exact h2.1.2, ?_⟩
    cases hpr : MirSemantics.placeTyResolved body.localDecls body.layouts q with
    | none => rw [hpr] at h2; simp at h2
    | some projTy =>
      have h2r := h2.2
      rw [hpr] at h2r
      exact ⟨projTy, rfl, by simpa [decide_eq_true_eq] using h2r⟩

private theorem resolveTyWithLocalDecls_idem (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (ty : MirAst.Ty) :
    MirSemantics.resolveTyWithLocalDecls decls layouts
      (MirSemantics.resolveTyWithLocalDecls decls layouts ty) =
    MirSemantics.resolveTyWithLocalDecls decls layouts ty := by
  rcases ty with ⟨k, l⟩
  unfold MirSemantics.resolveTyWithLocalDecls
  dsimp only
  cases hu : MirSemantics.isUnresolvedLayoutIdx layouts l
  · simp [hu]
  · dsimp only
    cases hf : MirSemantics.findDeclOrContainerElemTyWithKind? decls layouts k with
    | some declTy =>
      dsimp only
      cases MirSemantics.isUnresolvedLayoutIdx layouts declTy.layoutIdx <;> simp [hf]
    | none =>
      dsimp only
      cases hb : Nat.beq l 0 <;> cases decls <;> try simp [hu, hf, hb]
      cases hp : MirSemantics.isPrimitiveScalarKind k
      · dsimp only
        cases hu2 : MirSemantics.isUnresolvedLayoutIdx layouts (MirSemantics.unresolvedLayoutIdx layouts)
        · rfl
        · dsimp only; rw [hf]; dsimp only
          cases hb2 : Nat.beq (MirSemantics.unresolvedLayoutIdx layouts) 0
          · rfl
          · dsimp only; rw [hp]
      · simp [hu, hf, hb, hp]

private theorem tyByteSize_resolveTyWithLocalDecls (decls : List LocalDecl)
    (layouts : Layout.LayoutTable) (ty : MirAst.Ty) :
    MirSemantics.tyByteSize decls layouts
      (MirSemantics.resolveTyWithLocalDecls decls layouts ty) =
    MirSemantics.tyByteSize decls layouts ty := by
  unfold MirSemantics.tyByteSize MirSemantics.tyByteSizeAndAlignAux
  dsimp only
  rw [resolveTyWithLocalDecls_idem]

private theorem projectionChainByteOffset?_field_resolveTy
    (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (ty : MirAst.Ty) (valOpt : Option Value) (accOff : Nat)
    (idx : Nat) (fieldTy : MirAst.Ty) (rest : List ProjectionElem) :
    MirSemantics.projectionChainByteOffset? layouts
      (some (MirSemantics.resolveTyWithLocalDecls decls layouts ty))
      valOpt none accOff decls (.field idx fieldTy :: rest) =
    MirSemantics.projectionChainByteOffset? layouts
      (some ty) valOpt none accOff decls (.field idx fieldTy :: rest) := by
  unfold MirSemantics.projectionChainByteOffset?
  dsimp only
  rw [resolveTyWithLocalDecls_idem]

private theorem resolveSeqContainerElemByteStride_root_congr
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (k : Nat) {dk : LocalDecl}
    (hdk : decls[k]? = some dk) (elems1 elems2 : List Value) :
    MirSemantics.resolveSeqContainerElemByteStride decls layouts k [] elems1 =
      MirSemantics.resolveSeqContainerElemByteStride decls layouts k [] elems2 := by
  have hpl : MirSemantics.placeTyResolved decls layouts ⟨k, []⟩ = some dk.ty := by
    simp [MirSemantics.placeTyResolved, get?, hdk, MirSemantics.resolveProjectedTyResolved]
  unfold MirSemantics.resolveSeqContainerElemByteStride
  rw [hpl]

theorem borrowPlaceByteOffset?_of_ptrTargetSpec {body : CapturedMir}
    {locals callerLocals : List LocalSlot} {entry : BorrowEntry}
    {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
      some (pointeeIt, relOff))
    (hsub : entry.targetProjection ≠ [] →
      (∀ d ∈ body.localDecls, localDeclOk body.layouts d = true) ∧
      ptrDeclLayoutsOk body = true ∧
      ⟨entry.targetLocal, entry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body ∧
      ∃ dk v,
        body.localDecls[entry.targetLocal]? = some dk ∧
        locals[entry.targetLocal]? = some (.init v) ∧
        DeclSlotOk dk (.init v) body.layouts) :
    MirSemantics.borrowPlaceByteOffset? locals callerLocals body.localDecls body.layouts entry =
      some relOff := by
  by_cases hproj_nil : entry.targetProjection = []
  · have hrel0 : relOff = 0 := by
      have hts := htspec
      rw [hproj_nil] at hts
      simp only [ptrTargetSpec] at hts
      split at hts
      · obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp hts
        exact (Prod.mk.inj heq).2.symm
      · cases hts
    subst hrel0
    simp [MirSemantics.borrowPlaceByteOffset?, hproj_nil,
      MirSemantics.stripTransparentProjections, MirSemantics.normalizeSubsliceProjections]
  · obtain ⟨hdeclsOk, hdlo, hq, dk, v, hdk, hloc, hdslot⟩ := hsub hproj_nil
    let canonLocals : List LocalSlot :=
      body.localDecls.map (fun d => .init (canonicalDeclVal body.layouts d))
    let qEntry : BorrowEntry :=
      { tag := 0, targetLocal := entry.targetLocal, targetProjection := entry.targetProjection,
        perm := .active }
    have hcanon : MirSemantics.borrowPlaceByteOffset? canonLocals [] body.localDecls body.layouts
        qEntry = some relOff :=
      (ptrDeclLayoutsOk_place_spec hdlo hq hdk htspec).1
    have hstrip := stripTransparentProjections_of_ptrTargetSpec htspec
    have hnorm := normalizeSubsliceProjections_of_ptrTargetSpec htspec
    have hget_loc : get? locals entry.targetLocal = some (.init v) := by
      simpa [get?] using hloc
    have hget_canon : get? canonLocals entry.targetLocal =
        some (.init (canonicalDeclVal body.layouts dk)) := by
      simp [get?, canonLocals, hdk]
    have hget_decl : get? body.localDecls entry.targetLocal = some dk := by
      simpa [get?] using hdk
    obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
    rcases hcases with ⟨hproj, _, _, _⟩ |
      ⟨offset, minLen, fromEnd, dk', count, hproj, hdk', ha, _, _⟩ |
      ⟨idx, fieldTy, rest, hproj, _, _, dk', fields, size, align, _, hdk', htu, hres⟩
    · exact absurd hproj hproj_nil
    · dsimp only at hproj hdk'
      rw [hdk] at hdk'; injection hdk' with hdk_eq; subst hdk_eq
      have hvsh := declSlotOk_valueShapeEq hdslot (.inr (.inl ⟨pointeeIt, count, ha⟩))
      have ha_res : arrayTypeOf
          (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts dk.ty) =
          some (pointeeIt, count) := by
        unfold arrayTypeOf at ha ⊢
        rwa [resolveTyWithLocalDecls_kind]
      unfold MirSemantics.borrowPlaceByteOffset? at hcanon ⊢
      dsimp only [qEntry] at hcanon
      rw [hstrip, hnorm, hproj, hget_loc, hget_decl]
      rw [hstrip, hnorm, hproj, hget_canon, hget_decl] at hcanon
      dsimp only at hcanon ⊢
      rw [ValueShapeEq.projectionChainByteOffset?_constIdx_eq body.layouts body.localDecls
        ha_res 0 offset minLen fromEnd hvsh]
      exact hcanon
    · dsimp only at hproj hdk'
      rw [hdk] at hdk'; injection hdk' with hdk_eq; subst hdk_eq
      have hvsh := declSlotOk_valueShapeEq hdslot (.inr (.inr ⟨fields, size, align, htu⟩))
      have hall := resolveFieldPath_allFields hres
      unfold MirSemantics.borrowPlaceByteOffset? at hcanon ⊢
      dsimp only [qEntry] at hcanon
      rw [hstrip, hnorm, hproj, hget_loc, hget_decl]
      rw [hstrip, hnorm, hproj, hget_canon, hget_decl] at hcanon
      dsimp only at hcanon ⊢
      rw [ValueShapeEq.projectionChainByteOffset?_allFields_eq body.layouts body.localDecls hall
        (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts dk.ty) 0 hvsh]
      exact hcanon

theorem canonicalLocalAddr_lt_two_pow_64 {body : CapturedMir}
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hlen_lt : body.localDecls.length < 2 ^ 31)
    {k : Nat} {projs : List ProjectionElem} {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec body.layouts body.localDecls ⟨k, projs⟩ = some (pointeeIt, relOff)) :
    canonicalLocalAddr k relOff < 2 ^ 64 := by
  have hpage8 : MirSemantics.stackLocalAddrPageBase 8 = 1048576 := rfl
  obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
  obtain ⟨dk, hdk, hbound⟩ := ptrTargetSpec_bound hdeclsOk htspec
  have hk_lt : k < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdk).1
  have hdok := hdeclsOk dk (List.mem_of_getElem? hdk)
  have hrel_lt : relOff < 2 ^ 63 := by
    rcases hcases with ⟨hproj, _, _, _⟩ |
      ⟨_, _, _, dk', count, _, hdk', ha, _, _⟩ |
      ⟨_, _, _, _, _, _, dk', fields, size, align, _, hdk', htu, _⟩
    · dsimp only at hproj
      have hts := htspec
      subst hproj
      simp only [ptrTargetSpec] at hts
      split at hts
      · obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp hts
        have hr0 : relOff = 0 := (Prod.mk.inj heq).2.symm
        omega
      · cases hts
    · rw [hdk] at hdk'; injection hdk' with hdk_eq; subst hdk_eq
      obtain ⟨hTd, _⟩ := tyOf_array (layouts := body.layouts) ha
      rw [hTd] at hbound
      simp only [tyBytes] at hbound
      have hc_eq : (Int.ofNat count).toNat = count := rfl
      rw [hc_eq] at hbound
      have hsz_lt : count * pointeeIt.size.bytes < 2 ^ 63 := by
        simpa [localDeclOk, scalarTypeOf_none_of_arrayTypeOf ha,
          isPtrTy_false_of_arrayTypeOf ha, ha] using hdok
      omega
    · rw [hdk] at hdk'; injection hdk' with hdk_eq; subst hdk_eq
      obtain ⟨hTd, _⟩ := tyOf_tupleSpec htu
      rw [hTd] at hbound
      simp only [TupleSpec.toMiniRustTy, tyBytes] at hbound
      have hwf : (TupleSpec.tuple fields size align).wf = true := by
        simpa [localDeclOk, scalarTypeOf_none_of_tupleTypeOf htu,
          isPtrTy_false_of_tupleTypeOf htu, arrayTypeOf_none_of_tupleTypeOf htu, htu] using hdok
      simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
      have hsz_lt : size < 2 ^ 63 := hwf.1.2
      omega
  have hk_pow : k < 2 ^ 31 := Nat.lt_trans hk_lt hlen_lt
  simp only [canonicalLocalAddr, hpage8]
  omega

private theorem readProjectedValue_scalar_of_ptrTargetSpec {body : CapturedMir}
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {locals : List LocalSlot} (hslots : SlotsOk body.layouts body.localDecls locals)
    {q : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    {targetRootVal : Value} (ht : locals[q.local_]? = some (.init targetRootVal)) :
    ∃ (dk : LocalDecl) (sc : ScalarInt),
      body.localDecls[q.local_]? = some dk ∧
      ValueShapeEq targetRootVal (canonicalDeclVal body.layouts dk) ∧
      sc.sizeBytes = pointeeIt.size.bytes ∧
      1 ≤ pointeeIt.size.bytes ∧
      readProjectedValue locals targetRootVal q.projection = .ok (.scalar sc) := by
  have hgood : GoodSize pointeeIt.size.bytes :=
    operandOk_good (ptrTargetSpec_operandOk hdeclsOk htspec)
  have hpos : 1 ≤ pointeeIt.size.bytes := by
    rcases hgood with h | h | h | h | h <;> omega
  obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
  rcases hcases with ⟨hproj, dk, hdk, hit⟩ |
    ⟨offset, minLen, fromEnd, dk, count, hproj, hdk, ha, hpok, hbounds_fe⟩ |
    ⟨idx, fieldTy, rest, hproj, _, _, dk, fields, size, align, _, hdk, htu, hres⟩
  · have hvsh := declSlotOk_valueShapeEq (hslots q.local_ dk _ hdk ht) (.inl ⟨pointeeIt, hit⟩)
    have hslot := hslots.slotOk hdk ht hit
    cases targetRootVal with
    | scalar sc =>
      simp only [SlotOk, tyBytes] at hslot
      exact ⟨dk, sc, hdk, hvsh, hslot.1, hpos, by rw [hproj]; rfl⟩
    | unit => exact False.elim hslot
    | ptr _ _ => exact False.elim hslot
    | aggregate v0 fs =>
      simp only [SlotOk] at hslot
      cases v0 with
      | succ _ => exact False.elim hslot
      | zero =>
        rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨_, _⟩⟩⟩
        · exact False.elim hslot
        · cases f0 <;> exact False.elim hslot
        · cases f0 <;> cases f1 <;> try exact False.elim hslot
          simp only [Nat.zero_eq, tupleIntOfTy] at hslot
          rcases hslot with ⟨_, htu_bad, _⟩
          cases htu_bad
        · cases f0 <;> cases f1 <;> exact False.elim hslot
  · have hvsh := declSlotOk_valueShapeEq (hslots q.local_ dk _ hdk ht) (.inr (.inl ⟨pointeeIt, count, ha⟩))
    have hsloti := (DeclSlotOk_of_arrayTypeOf ha (.init targetRootVal)).mp (hslots q.local_ dk _ hdk ht)
    match targetRootVal, hsloti with
    | .aggregate 0 elems, ⟨hlen, he⟩ =>
      rcases q with ⟨k, projs⟩
      dsimp only at hproj hdk ⊢
      subst hproj
      have hmin : minLen ≤ count := by
        simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hpok
        exact hpok.1.1
      obtain ⟨hrok, _⟩ := readProjectedValue_proj body.localDecls locals count elems hlen
        (.constantIndex offset minLen fromEnd) hpok
      have hidx_some : ∃ idx, projIdx locals count (.constantIndex offset minLen fromEnd) = some idx := by
        cases fromEnd with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hbounds_fe
          exact ⟨offset, by simp [projIdx, show ¬ count < minLen by omega, hbounds_fe]⟩
        | true =>
          simp only [↓reduceIte] at hbounds_fe
          exact ⟨count - offset, by
            simp [projIdx, show ¬ count < minLen by omega, show count - offset < count by omega]⟩
      obtain ⟨eidx, heidx⟩ := hidx_some
      obtain ⟨v, hv, hrv⟩ := hrok eidx heidx
      have hvok := he v (List.mem_of_getElem? hv)
      cases v with
      | scalar sc =>
        exact ⟨dk, sc, hdk, hvsh, hvok.1, hpos, hrv⟩
      | _ => exact False.elim hvok
  · have hvsh := declSlotOk_valueShapeEq (hslots q.local_ dk _ hdk ht)
      (.inr (.inr ⟨fields, size, align, htu⟩))
    have hsloti := (DeclSlotOk_of_tupleTypeOf htu (.init targetRootVal)).mp
      (hslots q.local_ dk _ hdk ht)
    obtain ⟨leafVal, _, hleafOk, _, hprojRead⟩ := resolveFieldPath_read hsloti.1 hsloti.2 hres
    cases leafVal with
    | scalar sc =>
      simp only [TupleSpec.valOk, Bool.and_eq_true, decide_eq_true_eq] at hleafOk
      exact ⟨dk, sc, hdk, hvsh, hleafOk.1, hpos, hproj ▸ hprojRead locals⟩
    | _ => simp [TupleSpec.valOk] at hleafOk

private theorem ptrAllocByteBound?_spec {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {locals : List LocalSlot} (hslots : SlotsOk body.layouts body.localDecls locals)
    {mem : MirSemantics.Memory} {pv : ProvenancePtr} {entry : BorrowEntry}
    {pointeeIt : Gen.IntType} {relOff : Nat}
    (hlookup : lookupBorrow mem.borrows pv.tag = some entry)
    (hrlen : entry.rangeLen = 0)
    (hq : ⟨entry.targetLocal, entry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨entry.targetLocal, entry.targetProjection⟩ = some (pointeeIt, relOff))
    {targetRootVal : Value} (ht : locals[entry.targetLocal]? = some (.init targetRootVal)) :
    (∀ b, MirSemantics.ptrAllocByteBound? locals mem body.localDecls body.layouts pv =
      some b → b < 2 ^ 63) ∧
    (entry.perm ≠ .disabled →
      ∃ b, MirSemantics.ptrAllocByteBound? locals mem body.localDecls body.layouts pv =
        some b ∧ pointeeIt.size.bytes ≤ b) := by
  obtain ⟨dk, sc, hdk, hvsh, _, _, _⟩ :=
    readProjectedValue_scalar_of_ptrTargetSpec hdeclsOk hslots htspec ht
  obtain ⟨_, hroot_sz, hconst_sz, hfield_sz⟩ :=
    ptrDeclLayoutsOk_place_spec hdlo hq hdk htspec
  have hsA : get? locals entry.targetLocal = some (.init targetRootVal) := by simpa [get?] using ht
  have hpl_root : MirSemantics.placeTyResolved body.localDecls body.layouts ⟨entry.targetLocal, []⟩ =
      some dk.ty := by
    simp [MirSemantics.placeTyResolved, get?, hdk, MirSemantics.resolveProjectedTyResolved]
  have hlt_it : pointeeIt.size.bytes < 2 ^ 63 :=
    (operandOk_good (ptrTargetSpec_operandOk hdeclsOk htspec)).lt_two_pow_63
  constructor
  · intro b hb
    unfold MirSemantics.ptrAllocByteBound? at hb
    rw [hlookup] at hb
    dsimp only at hb
    cases hperm : entry.perm with
    | disabled => rw [hperm] at hb; simp only [Option.some.injEq] at hb; omega
    | active | reserved | frozen =>
      rw [hperm] at hb
      simp only [hsA, hrlen, Nat.beq_refl] at hb
      obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
      rcases hcases with ⟨hproj, d', hd', _⟩ |
        ⟨offset, minLen, fromEnd, d', count, hproj, hd', ha, _, _⟩ |
        ⟨idx, fieldTy, rest, hproj, _, _, d', fields, size, align, _, hd', htu, hres⟩
      · dsimp only at hproj hd'; rw [hdk] at hd'; injection hd' with hd_eq; subst hd_eq
        have hsz : MirSemantics.tyByteSize body.localDecls body.layouts dk.ty =
            some pointeeIt.size.bytes := by
          rw [← tyByteSize_resolveTyWithLocalDecls]; exact hroot_sz hproj
        rw [hproj] at hb
        simp only [MirSemantics.stripTransparentProjections,
          MirSemantics.normalizeSubsliceProjections, MirSemantics.normalizeAdjacentSubslices,
          MirSemantics.normalizeAdjacentSubslicesAux, MirSemantics.splitLastConstantIndex?,
          MirSemantics.splitLastSubslice?, MirSemantics.splitLastField?,
          hpl_root, hsz, Option.some.injEq] at hb
        omega
      · dsimp only at hproj hd'; rw [hdk] at hd'; injection hd' with hd_eq; subst hd_eq
        have hbound : count * pointeeIt.size.bytes < 2 ^ 63 := by
          simpa [localDeclOk, scalarTypeOf_none_of_arrayTypeOf ha, ha,
            isPtrTy_false_of_arrayTypeOf ha] using hdeclsOk dk (List.mem_of_getElem? hdk)
        obtain ⟨hstride, projTy, hpr, hpr_sz⟩ := hconst_sz offset minLen fromEnd hproj
        have hsloti := (DeclSlotOk_of_arrayTypeOf ha (.init targetRootVal)).mp
          (hslots entry.targetLocal dk _ hdk ht)
        match targetRootVal, hsloti with
        | .aggregate 0 elems, ⟨hlenE, _⟩ =>
          rw [hproj] at hb hpr
          cases fromEnd with
          | false =>
            have hstr_el := (resolveSeqContainerElemByteStride_root_congr
              body.localDecls body.layouts entry.targetLocal hdk elems []).trans hstride
            simp only [MirSemantics.stripTransparentProjections,
              MirSemantics.normalizeAdjacentSubslices, MirSemantics.normalizeAdjacentSubslicesAux,
              MirSemantics.splitLastConstantIndex?, readProjectedValue, hstr_el] at hb
            split at hb
            · simp only [Option.some.injEq] at hb; omega
            · simp only [Nat.sub_eq, Nat.mul_eq, Option.some.injEq] at hb
              subst hb
              have hle : (elems.length - offset) * pointeeIt.size.bytes ≤ count * pointeeIt.size.bytes := by
                rw [hlenE]; exact Nat.mul_le_mul_right _ (Nat.sub_le count offset)
              exact Nat.lt_of_le_of_lt hle hbound
          | true =>
            simp only [MirSemantics.stripTransparentProjections,
              MirSemantics.normalizeSubsliceProjections, MirSemantics.normalizeSubsliceProjectionsAux,
              MirSemantics.normalizeAdjacentSubslices, MirSemantics.normalizeAdjacentSubslicesAux,
              MirSemantics.splitLastConstantIndex?, MirSemantics.splitLastSubslice?,
              MirSemantics.splitLastField?, hpr, hpr_sz, Option.some.injEq] at hb
            omega
      · dsimp only at hproj hd'; rw [hdk] at hd'; injection hd' with hd_eq; subst hd_eq
        have hwf : (TupleSpec.tuple fields size align).wf = true := by
          simpa [localDeclOk, scalarTypeOf_none_of_tupleTypeOf htu, isPtrTy_false_of_tupleTypeOf htu,
            arrayTypeOf_none_of_tupleTypeOf htu, htu] using hdeclsOk dk (List.mem_of_getElem? hdk)
        have hlt_sz : size < 2 ^ 63 := by
          simp only [TupleSpec.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf; exact hwf.1.2
        obtain ⟨hsz0, _, projTy, hpr, _⟩ := hfield_sz idx fieldTy rest hproj fields size align htu
        have hsz : MirSemantics.tyByteSize body.localDecls body.layouts dk.ty = some size := by
          rw [← tyByteSize_resolveTyWithLocalDecls]; exact hsz0
        have hall : allFields (.field idx fieldTy :: rest) = true := resolveFieldPath_allFields hres
        have hall_rest : allFields rest = true := by simpa [allFields] using hall
        obtain ⟨initF, fIdx, fTy, hslf⟩ := splitLastField?_allFields idx fieldTy hall_rest
        rw [hproj] at hb hpr
        rw [stripTransparentProjections_allFields hall,
          normalizeSubsliceProjections_allFields hall,
          normalizeAdjacentSubslices_allFields hall,
          splitLastConstantIndex?_allFields hall,
          splitLastSubslice?_allFields hall,
          hslf, splitAfterLastSeqProj_allFields hall] at hb
        dsimp only at hb
        rw [normalizeSubsliceProjections_allFields hall] at hb
        simp only [hpl_root, hsz] at hb
        split at hb
        · simp only [Option.some.injEq] at hb; omega
        · split at hb <;> simp only [Nat.sub_eq, Option.some.injEq] at hb <;> omega
  · intro hndis
    unfold MirSemantics.ptrAllocByteBound?
    rw [hlookup]
    dsimp only
    cases hperm : entry.perm with
    | disabled => exact absurd hperm hndis
    | active | reserved | frozen =>
      simp only [hsA, hrlen, Nat.beq_refl]
      obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
      rcases hcases with ⟨hproj, d', hd', _⟩ |
        ⟨offset, minLen, fromEnd, d', count, hproj, hd', ha, hpok, hbounds_fe⟩ |
        ⟨idx, fieldTy, rest, hproj, _, _, d', fields, size, align, _, hd', htu, hres⟩
      · dsimp only at hproj hd'; rw [hdk] at hd'; injection hd' with hd_eq; subst hd_eq
        have hsz : MirSemantics.tyByteSize body.localDecls body.layouts dk.ty =
            some pointeeIt.size.bytes := by
          rw [← tyByteSize_resolveTyWithLocalDecls]; exact hroot_sz hproj
        rw [hproj]
        simp only [MirSemantics.stripTransparentProjections,
          MirSemantics.normalizeSubsliceProjections, MirSemantics.normalizeAdjacentSubslices,
          MirSemantics.normalizeAdjacentSubslicesAux, MirSemantics.splitLastConstantIndex?,
          MirSemantics.splitLastSubslice?, MirSemantics.splitLastField?, hpl_root, hsz]
        exact ⟨pointeeIt.size.bytes, rfl, Nat.le_refl _⟩
      · dsimp only at hproj hd'; rw [hdk] at hd'; injection hd' with hd_eq; subst hd_eq
        obtain ⟨hstride, projTy, hpr, hpr_sz⟩ := hconst_sz offset minLen fromEnd hproj
        have hsloti := (DeclSlotOk_of_arrayTypeOf ha (.init targetRootVal)).mp
          (hslots entry.targetLocal dk _ hdk ht)
        match targetRootVal, hsloti with
        | .aggregate 0 elems, ⟨hlenE, _⟩ =>
          rw [hproj] at hpr ⊢
          have hmin : minLen ≤ count := by
            simp only [projOk, Bool.and_eq_true, decide_eq_true_eq] at hpok
            exact hpok.1.1
          cases fromEnd with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at hbounds_fe
            have hlt_off : offset < count := hbounds_fe
            have hstr_el := (resolveSeqContainerElemByteStride_root_congr
              body.localDecls body.layouts entry.targetLocal hdk elems []).trans hstride
            have hble : (Nat.ble minLen count && Nat.ble offset count) = true := by
              simp [Nat.ble_eq, hmin, Nat.le_of_lt hlt_off]
            simp only [MirSemantics.stripTransparentProjections,
              MirSemantics.normalizeAdjacentSubslices, MirSemantics.normalizeAdjacentSubslicesAux,
              MirSemantics.splitLastConstantIndex?, readProjectedValue, hstr_el,
              mirValue_length_eq, hlenE, hble, Nat.sub_eq, Nat.mul_eq]
            exact ⟨(count - offset) * pointeeIt.size.bytes, rfl, by
              have : 1 ≤ count - offset := by omega
              exact Nat.le_trans (by simp) (Nat.mul_le_mul_right pointeeIt.size.bytes this)⟩
          | true =>
            simp only [MirSemantics.stripTransparentProjections,
              MirSemantics.normalizeSubsliceProjections, MirSemantics.normalizeSubsliceProjectionsAux,
              MirSemantics.normalizeAdjacentSubslices, MirSemantics.normalizeAdjacentSubslicesAux,
              MirSemantics.splitLastConstantIndex?, MirSemantics.splitLastSubslice?,
              MirSemantics.splitLastField?, hpr, hpr_sz]
            exact ⟨pointeeIt.size.bytes, rfl, Nat.le_refl _⟩
      · dsimp only at hproj hd'; rw [hdk] at hd'; injection hd' with hd_eq; subst hd_eq
        have hsloti := (DeclSlotOk_of_tupleTypeOf htu (.init targetRootVal)).mp
          (hslots entry.targetLocal dk _ hdk ht)
        obtain ⟨_, hrel_le⟩ := resolveFieldPath_wf hsloti.1 hres
        dsimp only [TupleSpec.size] at hrel_le
        have hts := htspec
        rw [hproj] at hts
        simp only [ptrTargetSpec] at hts
        split at hts <;> try cases hts
        simp only [Bind.bind, Option.bind, hdk] at hts
        rw [htu] at hts
        dsimp only at hts
        rw [hres] at hts
        dsimp only at hts
        injection hts with hpair
        obtain ⟨_, hrel_eq⟩ := Prod.mk.inj hpair
        obtain ⟨hsz0, hchain0, projTy, hpr, _⟩ := hfield_sz idx fieldTy rest hproj fields size align htu
        have hsz : MirSemantics.tyByteSize body.localDecls body.layouts dk.ty = some size := by
          rw [← tyByteSize_resolveTyWithLocalDecls]; exact hsz0
        have hall : allFields (.field idx fieldTy :: rest) = true := resolveFieldPath_allFields hres
        have hall_rest : allFields rest = true := by simpa [allFields] using hall
        obtain ⟨initF, fIdx, fTy, hslf⟩ := splitLastField?_allFields idx fieldTy hall_rest
        have hchain : MirSemantics.projectionChainByteOffset? body.layouts
            (some dk.ty) (some targetRootVal) none 0 body.localDecls
            (.field idx fieldTy :: rest) = some relOff := by
          rw [← projectionChainByteOffset?_field_resolveTy,
            ValueShapeEq.projectionChainByteOffset?_allFields_eq body.layouts body.localDecls
              hall _ 0 hvsh]
          simpa [hproj] using hchain0
        rw [hproj] at hpr ⊢
        rw [stripTransparentProjections_allFields hall,
          normalizeSubsliceProjections_allFields hall,
          normalizeAdjacentSubslices_allFields hall,
          splitLastConstantIndex?_allFields hall,
          splitLastSubslice?_allFields hall,
          hslf, splitAfterLastSeqProj_allFields hall]
        dsimp only
        rw [normalizeSubsliceProjections_allFields hall]
        have hble_rel : Nat.ble relOff size = true := Nat.ble_eq.mpr (by omega)
        simp only [readProjectedValue, hpl_root, hsz, hchain, hble_rel, Nat.sub_eq]
        exact ⟨size - relOff, rfl, by omega⟩

private theorem checkSafeRefDerefOk_of_ptrTargetSpec {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {s : MachineState} (hslots : SlotsOk body.layouts body.localDecls s.frame.locals)
    {p : Nat} {dp : LocalDecl} {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : body.localDecls[p]? = some dp)
    (hp_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    {parentPtr : ProvenancePtr} (hoff0 : parentPtr.offsetBytes = 0)
    {parentEntry : BorrowEntry}
    (hlookup : lookupBorrow s.memory.borrows parentPtr.tag = some parentEntry)
    (hndis : parentEntry.perm ≠ .disabled)
    (hrlen : parentEntry.rangeLen = 0)
    (hq : ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ = some (pointeeIt, relOff))
    {targetRootVal : Value}
    (ht : s.frame.locals[parentEntry.targetLocal]? = some (.init targetRootVal)) :
    (match dp.ty.kind with
     | .ref _ _ =>
       MirSemantics.checkSafeRefDerefOk s.frame.locals parentPtr s.memory.borrows
         s.memory.globals s.memory.callerLocals body.localDecls body.layouts
         (MirSemantics.placeTyResolved body.localDecls body.layouts ⟨p, [.deref]⟩)
     | _ => true) = true := by
  cases dp.ty.kind with
  | ref _ _ =>
    dsimp only
    obtain ⟨pTy, hpty, _, hp_sz, _, _, _⟩ := ptrDeclLayoutsOk_ptr_spec hdlo hdp hp_pt
    have htag_eq : parentEntry.tag = parentPtr.allocId := (lookupBorrow_mem_and_tag hlookup).2
    let boundMem : MirSemantics.Memory :=
      { MirSemantics.emptyMemory with
        globals := s.memory.globals
        borrows := [{ parentEntry with perm := .active }]
        callerLocals := s.memory.callerLocals }
    have hlk_bound : lookupBorrow boundMem.borrows parentPtr.allocId =
        some { parentEntry with perm := .active } := by
      simp [boundMem, lookupBorrow, htag_eq]
    obtain ⟨b, hb, hle_b⟩ := (ptrAllocByteBound?_spec hdlo hdeclsOk hslots
      (pv := ⟨parentPtr.allocId, 0⟩) hlk_bound hrlen hq htspec ht).2 (by simp)
    have hsA : get? s.frame.locals parentEntry.targetLocal = some (.init targetRootVal) := by
      simpa [get?] using ht
    unfold MirSemantics.checkSafeRefDerefOk
    rw [hpty, hoff0]
    dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl]
    rw [hp_sz, hlookup]
    dsimp only
    cases hp_perm : parentEntry.perm with
    | disabled => exact absurd hp_perm hndis
    | _ =>
      dsimp only
      rw [hsA]
      simp only [Bool.and_self]
      change (match MirSemantics.ptrAllocByteBound? s.frame.locals boundMem body.localDecls
          body.layouts { allocId := parentPtr.allocId, offsetBytes := 0 } with
        | some bound => Nat.ble (Nat.add 0 pointeeIt.size.bytes) bound
        | none => true) = true
      rw [hb]
      simpa [Nat.add_eq, Nat.ble_eq] using hle_b
  | _ => rfl

private theorem findDeclOrContainerElemTyWithKind?_intKind
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) {ek : MirAst.RigidTy}
    (hek : (intTyBytes ek).isSome = true) {resTy : MirAst.Ty}
    (h : MirSemantics.findDeclOrContainerElemTyWithKind? decls layouts ek = some resTy) :
    (intTyBytes resTy.kind).isSome = true := by
  have hd : ∀ (ds : List LocalDecl),
      MirSemantics.findDeclTyWithKind? ds ek = some resTy →
      (intTyBytes resTy.kind).isSome = true := by
    intro ds hds
    induction ds with
    | nil => simp [MirSemantics.findDeclTyWithKind?] at hds
    | cons d rest ih =>
      unfold MirSemantics.findDeclTyWithKind? at hds
      cases heq : MirSemantics.rigidTyEq d.ty.kind ek with
      | false => rw [heq] at hds; exact ih hds
      | true =>
        rw [heq] at hds
        simp only [Option.some.injEq] at hds
        subst hds
        unfold MirSemantics.rigidTyEq at heq
        cases hfuel : MirSemantics.defaultTyEqFuel with
        | zero => rw [hfuel] at heq; unfold MirSemantics.rigidTyEqAux at heq; cases heq
        | succ f =>
          rw [hfuel] at heq
          cases hdk_k : d.ty.kind with
          | int w => cases w <;> rfl
          | uint w => cases w <;> rfl
          | _ =>
            cases hek_k : ek <;>
              simp [MirSemantics.rigidTyEqAux, intTyBytes, hdk_k, hek_k] at heq hek
  have hc : ∀ (ds : List LocalDecl),
      MirSemantics.findContainerElemTyWithKind? layouts ds ek = some resTy →
      (intTyBytes resTy.kind).isSome = true := by
    intro ds hds
    induction ds with
    | nil => simp [MirSemantics.findContainerElemTyWithKind?] at hds
    | cons d rest ih =>
      unfold MirSemantics.findContainerElemTyWithKind? at hds
      dsimp only at hds
      cases hdk_kind : d.ty.kind with
      | array ek0 _ | slice ek0 =>
        rw [hdk_kind] at hds
        dsimp only at hds
        cases hr : MirSemantics.rigidTyEq ek0 ek with
        | false => rw [hr] at hds; exact ih hds
        | true =>
          rw [hr] at hds
          dsimp only at hds
          cases hl : Layout.LayoutTable.lookup layouts d.ty.layoutIdx with
          | none => rw [hl] at hds; exact ih hds
          | some l =>
            rw [hl] at hds
            rcases l with ⟨_, _, _, fieldsL, _, _, fls⟩
            cases fieldsL <;> try exact ih hds
            cases fls with
            | nil => exact ih hds
            | cons flIdx _ =>
              simp only [Option.some.injEq] at hds
              subst hds
              exact hek
      | _ =>
        rw [hdk_kind] at hds
        exact ih hds
  unfold MirSemantics.findDeclOrContainerElemTyWithKind? at h
  cases hf : MirSemantics.findDeclTyWithKind? decls ek with
  | some dt => rw [hf] at h; simp only [Option.some.injEq] at h; subst h; exact hd decls hf
  | none => rw [hf] at h; exact hc decls h

private theorem resolveProjectedTyResolved_allFields_kind
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) :
    ∀ {projs : List ProjectionElem}, allFields projs = true →
      ∀ (bTy1 bTy2 : MirAst.Ty), bTy1.kind = bTy2.kind →
        (MirSemantics.resolveProjectedTyResolved decls layouts bTy1 projs).map (·.kind) =
          (resolveProjTy bTy2 projs).map (·.kind) := by
  intro projs
  induction projs with
  | nil =>
    intro _ bTy1 bTy2 hkind
    simp [MirSemantics.resolveProjectedTyResolved, resolveProjTy, hkind]
  | cons pe tl ih =>
    intro hall bTy1 bTy2 _
    cases pe with
    | field fi ft =>
      simp only [allFields] at hall
      unfold MirSemantics.resolveProjectedTyResolved resolveProjTy
      dsimp only
      apply ih hall _ ft
      repeat (first | rfl | exact resolveTyWithLocalDecls_kind decls layouts ft | split)
    | _ => simp [allFields] at hall

private theorem isElemPtrAtZero_false_of_scalar_read
    (decls : List LocalDecl) (layouts : Layout.LayoutTable) (locals : List LocalSlot)
    (targetRootVal : Value) (entry : BorrowEntry) (_pointeeTyOpt : Option MirAst.Ty)
    {sc : ScalarInt} {pointeeIt : Gen.IntType} {relOff : Nat}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    (htspec : ptrTargetSpec layouts decls ⟨entry.targetLocal, entry.targetProjection⟩ =
      some (pointeeIt, relOff))
    (_hrd : readProjectedValue locals targetRootVal entry.targetProjection = .ok (.scalar sc)) :
    MirSemantics.endsWithSubslice
      (MirSemantics.normalizeSubsliceProjections
        (MirSemantics.stripTransparentProjections entry.targetProjection)) = false ∧
    MirSemantics.projHasSubslice entry.targetProjection = false ∧
    (match MirSemantics.placeTyResolved decls layouts
        { local_ := entry.targetLocal,
          projection := MirSemantics.normalizeSubsliceProjections
            (MirSemantics.stripTransparentProjections entry.targetProjection) } with
     | some { kind := .array _ _, .. } => false
     | some { kind := .slice _, .. } => false
     | _ => true) = true := by
  obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
  rcases hcases with ⟨hproj, dk, hdk, hit⟩ |
    ⟨offset, minLen, fromEnd, dk, count, hproj, hdk, ha, _, _⟩ |
    ⟨idx, fTy, rest, hproj, _, _, dk, fields, _, _, _, hdk, _, hres⟩
  · dsimp only at hproj hdk
    rw [hproj]
    have hpl : MirSemantics.placeTyResolved decls layouts ⟨entry.targetLocal, []⟩ = some dk.ty := by
      simp [MirSemantics.placeTyResolved, get?, hdk, MirSemantics.resolveProjectedTyResolved]
    refine ⟨rfl, rfl, ?_⟩
    simp only [MirSemantics.stripTransparentProjections, MirSemantics.normalizeSubsliceProjections, hpl]
    rcases dk with ⟨_, ⟨dk_k, _⟩, _⟩
    unfold intTypeOf at hit
    dsimp only at hit
    cases dk_k <;> simp [intTyBytes] at hit ⊢
  · dsimp only at hproj hdk
    rw [hproj]
    unfold arrayTypeOf at ha
    cases htk : dk.ty.kind with
    | array ek _ =>
      rw [htk] at ha
      obtain ⟨_, hb_ek, _⟩ := Option.map_eq_some_iff.mp ha
      have hek_int : (intTyBytes ek).isSome = true := by simp [hb_ek]
      refine ⟨rfl, rfl, ?_⟩
      simp only [MirSemantics.stripTransparentProjections, MirSemantics.normalizeSubsliceProjections,
        MirSemantics.normalizeSubsliceProjectionsAux, MirSemantics.placeTyResolved, get?, hdk,
        MirSemantics.resolveProjectedTyResolved, MirSemantics.elemTyOf, htk]
      have hres_int : ∀ (et : MirAst.Ty),
          (intTyBytes et.kind).isSome = true →
          (match some et with
           | some { kind := .array _ _, .. } => false
           | some { kind := .slice _, .. } => false
           | _ => true) = true := by
        intro et het
        rcases et with ⟨ek', _⟩
        cases ek' <;> simp [intTyBytes] at het ⊢
      apply hres_int
      cases hf : MirSemantics.findDeclOrContainerElemTyWithKind? decls layouts ek with
      | some dt =>
        have hdt := findDeclOrContainerElemTyWithKind?_intKind decls layouts hek_int hf
        repeat (first | exact hek_int | exact hdt | split)
      | none =>
        repeat (first | exact hek_int | split)
    | _ => rw [htk] at ha; cases ha
  · dsimp only at hproj hdk
    have hall := resolveFieldPath_allFields hres
    rw [hproj, stripTransparentProjections_allFields hall,
      normalizeSubsliceProjections_allFields hall]
    have hres_ty : ∃ leafTy, resolveProjTy dk.ty (.field idx fTy :: rest) = some leafTy ∧
        (intTyBytes leafTy.kind).isSome = true := by
      have haux : ∀ (projs : List ProjectionElem) (baseTy : MirAst.Ty) (spec : TupleSpec) (rOff : Nat),
          projs ≠ [] →
          resolveFieldPath layouts spec projs = some (rOff, .scalar pointeeIt) →
          ∃ lTy, resolveProjTy baseTy projs = some lTy ∧ (intTyBytes lTy.kind).isSome = true := by
        intro projs
        induction projs with
        | nil => intro _ _ _ hne; exact absurd rfl hne
        | cons pe tl ih =>
          intro baseTy spec rOff _ hrp
          cases pe with
          | field fIdx fT =>
            cases spec with
            | scalar _ => simp [resolveFieldPath] at hrp
            | tuple fs _ _ =>
              unfold resolveFieldPath at hrp
              simp only [Bind.bind, Option.bind] at hrp
              cases hfs : fs[fIdx]? with
              | none => simp [hfs] at hrp
              | some pair =>
                rcases pair with ⟨off, subSpec⟩
                cases hsp : specOfRigidTy layouts fT.kind fT.layoutIdx with
                | none => simp [hfs, hsp] at hrp
                | some expSpec =>
                  simp only [hfs, hsp] at hrp
                  by_cases heq : subSpec = expSpec
                  · simp only [heq, ↓reduceIte] at hrp
                    cases tl with
                    | nil =>
                      unfold resolveFieldPath at hrp
                      simp only [Pure.pure, Option.some.injEq, Prod.mk.injEq] at hrp
                      obtain ⟨_, rfl⟩ := hrp
                      refine ⟨fT, rfl, ?_⟩
                      cases hfk : fT.kind with
                      | uint w => cases w <;> rfl
                      | int w => cases w <;> rfl
                      | tuple _ | adt _ _ =>
                        rw [hfk] at hsp
                        unfold specOfRigidTy at hsp
                        simp only [Bind.bind, Option.bind, Pure.pure] at hsp
                        repeat (split at hsp <;> try simp at hsp)
                      | _ => rw [hfk] at hsp; simp [specOfRigidTy] at hsp
                    | cons p2 tl2 =>
                      cases hrec : resolveFieldPath layouts expSpec (p2 :: tl2) with
                      | none => simp [hrec] at hrp
                      | some rpair =>
                        rcases rpair with ⟨restOff, leafSpec⟩
                        simp only [hrec, Pure.pure, Option.some.injEq, Prod.mk.injEq] at hrp
                        obtain ⟨_, rfl⟩ := hrp
                        exact ih fT expSpec restOff (by simp) hrec
                  · simp [heq] at hrp
          | _ => cases spec <;> simp [resolveFieldPath] at hrp
      exact haux (.field idx fTy :: rest) dk.ty (.tuple fields _ _) _ (by simp) hres
    obtain ⟨leafTy, hleaf, hleafInt⟩ := hres_ty
    refine ⟨?_, projHasSubslice_allFields hall, ?_⟩
    · have hend : ∀ (ps : List ProjectionElem), allFields ps = true →
          MirSemantics.endsWithSubslice ps = false := by
        intro ps
        induction ps with
        | nil => intro _; rfl
        | cons e tl ih =>
          intro ha0
          cases e <;> simp [allFields] at ha0
          cases tl with
          | nil => rfl
          | cons e2 tl2 => exact ih ha0
      exact hend _ hall
    · have hkind_map : (MirSemantics.placeTyResolved decls layouts
          ⟨entry.targetLocal, .field idx fTy :: rest⟩).map (·.kind) = some leafTy.kind := by
        simp only [MirSemantics.placeTyResolved, get?, hdk]
        rw [resolveProjectedTyResolved_allFields_kind decls layouts hall dk.ty dk.ty rfl, hleaf]
        rfl
      cases hplr : MirSemantics.placeTyResolved decls layouts
          ⟨entry.targetLocal, .field idx fTy :: rest⟩ with
      | none => rfl
      | some resTy =>
        rw [hplr] at hkind_map
        simp only [Option.map, Option.some.injEq] at hkind_map
        rcases resTy with ⟨rk, rl⟩
        dsimp only at hkind_map
        cases rk <;> rw [← hkind_map] at hleafInt <;> simp [intTyBytes] at hleafInt ⊢

private theorem resolveRefDerefTarget?_of_ptrTargetSpec {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {s : MachineState} (hslots : SlotsOk body.layouts body.localDecls s.frame.locals)
    {p : Nat} {dp : LocalDecl} {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : body.localDecls[p]? = some dp)
    (hp_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    {parentPtr : ProvenancePtr} (hoff0 : parentPtr.offsetBytes = 0)
    {parentEntry : BorrowEntry}
    (hq : ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ = some (pointeeIt, relOff))
    {targetRootVal : Value}
    (ht : s.frame.locals[parentEntry.targetLocal]? = some (.init targetRootVal)) :
    MirSemantics.resolveRefDerefTarget? s.frame.locals targetRootVal parentEntry parentPtr []
      body.localDecls body.layouts
      (MirSemantics.placeTyResolved body.localDecls body.layouts ⟨p, [.deref]⟩)
      (MirSemantics.placeTyResolved body.localDecls body.layouts ⟨p, [.deref]⟩) false
      body.localDecls = some (some (parentEntry.targetProjection, 0)) := by
  obtain ⟨pTy, hpty, hsc_bytes, hp_sz, hr_sz, hnot_bad, halign_all⟩ :=
    ptrDeclLayoutsOk_ptr_spec hdlo hdp hp_pt
  obtain ⟨dk, sc, hdk, hvsh, hsc_sz, _, hrd⟩ :=
    readProjectedValue_scalar_of_ptrTargetSpec hdeclsOk hslots htspec ht
  have hdecls_ne : ∃ d0 ds, body.localDecls = d0 :: ds := by
    cases h : body.localDecls with
    | nil => rw [h] at hdp; simp at hdp
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  obtain ⟨d0, ds, hcons⟩ := hdecls_ne
  have halign : MirSemantics.checkTargetPlaceAlign body.localDecls body.layouts (some pTy)
      parentEntry parentPtr (some targetRootVal) = true := by
    rw [ValueShapeEq.checkTargetPlaceAlign_eq hdeclsOk (some pTy) parentEntry parentPtr
      hoff0 htspec hdk hvsh]
    exact (halign_all _ hq dk hdk).1
  have hnu : MirSemantics.placeTouchesUnion body.localDecls body.layouts
      ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ = false :=
    placeTouchesUnion_false_of_inFragment (.inr (.inr (.inr (by simp [htspec]))))
  obtain ⟨hend_sub, hhas_sub, hnot_seq_pl⟩ :=
    isElemPtrAtZero_false_of_scalar_read body.localDecls body.layouts s.frame.locals
      targetRootVal parentEntry (some pTy) hdeclsOk htspec hrd
  have hrAcc_not_never : (match (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy).kind with
      | .never => false | _ => true) = true := by
    cases hk : (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy).kind <;>
      rw [hk] at hnot_bad <;> simp_all
  have hrd_norm : readProjectedValue s.frame.locals targetRootVal
      (MirSemantics.normalizeSubsliceProjections
        (MirSemantics.stripTransparentProjections parentEntry.targetProjection)) = .ok (.scalar sc) := by
    obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
    rcases hcases with ⟨hproj, _, _, _⟩ | ⟨_, _, _, _, _, hproj, _, _, _, _⟩ |
      ⟨_, _, _, hproj, _, _, _, _, _, _, _, _, _, hres⟩
    · dsimp only at hproj; rw [hproj] at hrd ⊢; exact hrd
    · dsimp only at hproj; rw [hproj] at hrd ⊢; exact hrd
    · dsimp only at hproj
      have hall := resolveFieldPath_allFields hres
      rw [hproj, stripTransparentProjections_allFields hall,
        normalizeSubsliceProjections_allFields hall]
      rwa [← hproj]
  have hleaf :
      (match
        projHasSubslice
          (match parentEntry.targetProjection with
          | [] => []
          | ph :: pt => ph :: appendProjections pt []) with
      | false =>
        some
          (match parentEntry.targetProjection with
            | [] => []
            | ph :: pt => ph :: appendProjections pt [],
            0)
      | true =>
        match
          forwardSubslicesOrdered
              (stripTransparentProjections
                (match parentEntry.targetProjection with
                | [] => []
                | ph :: pt => ph :: appendProjections pt [])) &&
            subsliceChainValidOnVal s.frame.locals targetRootVal
              (normalizeSubsliceProjections
                (stripTransparentProjections
                  (match parentEntry.targetProjection with
                  | [] => []
                  | ph :: pt => ph :: appendProjections pt []))) with
        | true =>
          some
            (match parentEntry.targetProjection with
              | [] => []
              | ph :: pt => ph :: appendProjections pt [],
              0)
        | false => none) = some (parentEntry.targetProjection, 0) := by
    cases hproj : parentEntry.targetProjection with
    | nil => rfl
    | cons ph pt =>
      have hh : projHasSubslice (ph :: pt) = false := hproj ▸ hhas_sub
      simp only [appendProjections_nil_right, hh]
  have hres_stack : MirSemantics.resolveStackThinPtrTargetProjWithResidual?
      s.frame.locals targetRootVal parentEntry parentPtr [] body.localDecls body.layouts
      (some pTy) (some pointeeIt.size.bytes) = some (parentEntry.targetProjection, 0) := by
    unfold MirSemantics.resolveStackThinPtrTargetProjWithResidual?
    dsimp only [MirSemantics.startsWithArrayOrSliceProj, MirSemantics.stripTransparentProjections,
      MirSemantics.projHasSubslice]
    rw [hend_sub, hoff0]
    dsimp only [MirSemantics.startsWithArrayOrSliceProj, Nat.beq_refl]
    cases hpl_t : MirSemantics.placeTyResolved body.localDecls body.layouts
        { local_ := parentEntry.targetLocal,
          projection := MirSemantics.normalizeSubsliceProjections
            (MirSemantics.stripTransparentProjections parentEntry.targetProjection) } with
    | none =>
      cases MirSemantics.tyScalarBytes pTy with
      | none => cases pTy.kind <;> exact hleaf
      | some _ => rw [hrd_norm]; cases pTy.kind <;> exact hleaf
    | some plTy =>
      rcases plTy with ⟨plk, _⟩
      rw [hpl_t] at hnot_seq_pl
      cases MirSemantics.tyScalarBytes pTy with
      | none =>
        cases plk <;> try cases hnot_seq_pl
        all_goals (cases pTy.kind <;> exact hleaf)
      | some _ =>
        rw [hrd_norm]
        cases plk <;> try cases hnot_seq_pl
        all_goals (cases pTy.kind <;> exact hleaf)
  have hble : Nat.ble (Nat.add 0 pointeeIt.size.bytes) sc.sizeBytes = true := by
    simp [Nat.add_eq, Nat.ble_eq, hsc_sz]
  have hp_eta : { parentPtr with offsetBytes := 0 } = parentPtr := by
    cases parentPtr; dsimp only at hoff0 ⊢; subst hoff0; rfl
  unfold MirSemantics.resolveRefDerefTarget?
  rw [hpty, hcons]
  dsimp only [MirSemantics.stripTransparentProjections]
  rw [← hcons, halign]
  dsimp only [MirSemantics.stripTransparentProjections]
  unfold MirSemantics.resolveRefDerefTargetCore?
  rw [hcons]
  dsimp only [MirSemantics.stripTransparentProjections]
  rw [← hcons, hr_sz, hres_stack]
  dsimp only [MirSemantics.readProjectedForLocal]
  rw [hnu]
  dsimp only [MirSemantics.stripTransparentProjections]
  rw [hrd]
  dsimp only [MirSemantics.stripTransparentProjections]
  rw [hsc_bytes]
  cases MirSemantics.placeTyResolved body.localDecls body.layouts
      ⟨parentEntry.targetLocal, parentEntry.targetProjection⟩ <;>
    (cases hk : (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy).kind <;>
      rw [hk] at hrAcc_not_never <;> try cases hrAcc_not_never) <;>
    (dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl];
     rw [hble];
     dsimp only [MirSemantics.checkDerefAlign, Nat.beq_refl];
     rw [hp_eta, halign];
     rfl)

private theorem evalOperand_deref_eq_target_typed {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {locals : List LocalSlot} (hslots : SlotsOk body.layouts body.localDecls locals)
    (mem : MirSemantics.Memory)
    {p : Nat} {dp : LocalDecl} {srcMutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    (hdp : body.localDecls[p]? = some dp)
    (hp_pt : ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt))
    {ptrVal : ProvenancePtr} (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    {entry : BorrowEntry} (hlookup : lookupBorrow mem.borrows ptrVal.tag = some entry)
    (hndis : entry.perm ≠ .disabled)
    (hq : ⟨entry.targetLocal, entry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨entry.targetLocal, entry.targetProjection⟩ = some (pointeeIt, relOff))
    {targetRootVal : Value}
    (ht : locals[entry.targetLocal]? = some (.init targetRootVal)) :
    evalOperand locals (.copy ⟨p, [.deref]⟩) mem.borrows mem.globals body.layouts
      mem.callerLocals body.localDecls =
    evalOperand locals (.copy ⟨entry.targetLocal, entry.targetProjection⟩) mem.borrows
      mem.globals body.layouts mem.callerLocals body.localDecls := by
  obtain ⟨pTy, hpty, hsc_bytes, _, _, hnot_bad, halign_all⟩ :=
    ptrDeclLayoutsOk_ptr_spec hdlo hdp hp_pt
  obtain ⟨dk, sc, hdk, hvsh, hsc_sz, hpos, hrd⟩ :=
    readProjectedValue_scalar_of_ptrTargetSpec hdeclsOk hslots htspec ht
  have hdecls_ne : ∃ d0 ds, body.localDecls = d0 :: ds := by
    cases h : body.localDecls with
    | nil => rw [h] at hdp; simp at hdp
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  obtain ⟨d0, ds, hcons⟩ := hdecls_ne
  have halign : MirSemantics.checkTargetPlaceAlign body.localDecls body.layouts
      (some (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy))
      entry ptrVal (some targetRootVal) = true := by
    rw [ValueShapeEq.checkTargetPlaceAlign_eq hdeclsOk _ entry ptrVal hoff0 htspec hdk hvsh]
    exact (halign_all _ hq dk hdk).2
  have hnu : MirSemantics.placeTouchesUnion body.localDecls body.layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false :=
    placeTouchesUnion_false_of_inFragment (.inr (.inr (.inr (by simp [htspec]))))
  have hrhs : evalOperand locals (.copy ⟨entry.targetLocal, entry.targetProjection⟩)
      mem.borrows mem.globals body.layouts mem.callerLocals body.localDecls =
      .ok (.scalar sc) locals := by
    cases hproj : entry.targetProjection with
    | nil =>
      rw [hproj] at hrd
      simp only [readProjectedValue, ProjReadResult.ok.injEq] at hrd
      subst hrd
      simp [evalOperand, get?, ht, readProjectedValue]
    | cons ph pt =>
      have hnd : ∀ rest, (ph :: pt) ≠ .deref :: rest := by
        intro rest hr
        rw [hproj, hr] at htspec
        simp [ptrTargetSpec] at htspec
      rw [evalOperand_copy_nonDeref locals ⟨entry.targetLocal, ph :: pt⟩ hnd mem.borrows
        mem.globals body.layouts mem.callerLocals body.localDecls (hproj ▸ hnu)]
      rw [hproj] at hrd
      simp [get?, ht, hrd]
  rw [hrhs]
  have hextract : MirSemantics.extractScalarSlice? sc 0 pointeeIt.size.bytes = some sc := by
    unfold MirSemantics.extractScalarSlice?
    have hb1 : Bool.and (Nat.ble 1 pointeeIt.size.bytes)
        (Nat.ble (Nat.add 0 pointeeIt.size.bytes) sc.sizeBytes) = true := by
      simp [Nat.add_eq, Nat.ble_eq, hpos, hsc_sz]
    have hb2 : Bool.and (Nat.beq 0 0) (Nat.beq pointeeIt.size.bytes sc.sizeBytes) = true := by
      simp [hsc_sz]
    rw [hb1, hb2]
  have hval_ok : MirSemantics.validateValueForTy? body.layouts
      (some (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy))
      (.scalar sc) = true := by
    rcases hr : MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy with ⟨rk, rl⟩
    simp only [hr] at hnot_bad
    cases rk <;> simp_all [MirSemantics.validateValueForTy?]
  unfold evalOperand
  dsimp only [get?]
  rw [hp]
  dsimp only [get?]
  rw [hcons]
  dsimp only [get?]
  rw [← hcons, hlookup]
  dsimp only [get?]
  cases hpe : entry.perm with
  | disabled => exact absurd hpe hndis
  | _ =>
    dsimp only [get?]
    rw [ht]
    dsimp only [get?]
    unfold MirSemantics.evalStackThinPtrTypedDerefRead
    rw [hpty, hoff0]
    dsimp only [MirSemantics.stripTransparentProjections, MirSemantics.checkDerefAlign,
      Nat.beq_refl]
    rw [halign]
    simp only [Bool.and_self]
    rw [hcons]
    dsimp only [MirSemantics.stripTransparentProjections]
    rw [← hcons, hsc_bytes]
    dsimp only [MirSemantics.stripTransparentProjections]
    cases hproj : entry.targetProjection with
    | nil =>
      have hrd' : readProjectedValue locals targetRootVal [] = .ok (.scalar sc) := hproj ▸ hrd
      dsimp only [MirSemantics.readProjectedForLocal]
      rw [hrd']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hextract]
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hval_ok]
    | cons ph pt =>
      have hnu' : MirSemantics.placeTouchesUnion body.localDecls body.layouts
          ⟨entry.targetLocal, ph :: pt⟩ = false := hproj ▸ hnu
      have hrd' : readProjectedValue locals targetRootVal (ph :: pt) = .ok (.scalar sc) :=
        hproj ▸ hrd
      dsimp only [MirSemantics.readProjectedForLocal]
      rw [appendProjections_nil_right, hnu']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hrd']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hextract]
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hval_ok]

private theorem writePlaceValue_deref_of_ptrTargetSpec {body : CapturedMir}
    (hdlo : ptrDeclLayoutsOk body = true)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    {locals : List LocalSlot} (hslots : SlotsOk body.layouts body.localDecls locals)
    (borrows : List BorrowEntry)
    {p : Nat} {dp : LocalDecl} {pointeeIt : Gen.IntType}
    (hdp : body.localDecls[p]? = some dp)
    (hp_pt : ptrPointeeOf dp.ty = some (.mut, pointeeIt))
    {ptrVal : ProvenancePtr} (hp : locals[p]? = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    {entry : BorrowEntry} (hlookup : lookupBorrow borrows ptrVal.tag = some entry)
    (hact : entry.perm = .active ∨ entry.perm = .reserved)
    (hq : ⟨entry.targetLocal, entry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨entry.targetLocal, entry.targetProjection⟩ = some (pointeeIt, relOff))
    {targetRootVal : Value}
    (ht : locals[entry.targetLocal]? = some (.init targetRootVal))
    {wSc : ScalarInt} (hw_sz : wSc.sizeBytes = pointeeIt.size.bytes)
    {w : Value}
    (hwshape : (entry.targetProjection = [] ∧ w = .scalar wSc) ∨
      ∃ ph pt rootVal, entry.targetProjection = ph :: pt ∧
        locals[entry.targetLocal]? = some (.init rootVal) ∧
        writeProjectedValue locals rootVal (ph :: pt) (.scalar wSc) = .ok w) :
    writePlaceValue locals borrows ⟨p, [.deref]⟩ (.scalar wSc) body.localDecls body.layouts =
      .ok (locals.set entry.targetLocal (.init w)) := by
  obtain ⟨pTy, hpty, _, _, _, hnot_bad, halign_all⟩ :=
    ptrDeclLayoutsOk_ptr_spec hdlo hdp hp_pt
  obtain ⟨dk, oldSc, hdk, hvsh, hold_sz, hpos, hrd⟩ :=
    readProjectedValue_scalar_of_ptrTargetSpec hdeclsOk hslots htspec ht
  have hdecls_ne : ∃ d0 ds, body.localDecls = d0 :: ds := by
    cases h : body.localDecls with
    | nil => rw [h] at hdp; simp at hdp
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  obtain ⟨d0, ds, hcons⟩ := hdecls_ne
  have halign : MirSemantics.checkTargetPlaceAlign body.localDecls body.layouts
      (some (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy))
      entry ptrVal (some targetRootVal) = true := by
    rw [ValueShapeEq.checkTargetPlaceAlign_eq hdeclsOk _ entry ptrVal hoff0 htspec hdk hvsh]
    exact (halign_all _ hq dk hdk).2
  have hnu : MirSemantics.placeTouchesUnion body.localDecls body.layouts
      ⟨entry.targetLocal, entry.targetProjection⟩ = false :=
    placeTouchesUnion_false_of_inFragment (.inr (.inr (.inr (by simp [htspec]))))
  have hval_ok : MirSemantics.validateValueForTy? body.layouts
      (some (MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy))
      (.scalar wSc) = true := by
    rcases hr : MirSemantics.resolveTyWithLocalDecls body.localDecls body.layouts pTy with ⟨rk, rl⟩
    simp only [hr] at hnot_bad
    cases rk <;> simp_all [MirSemantics.validateValueForTy?]
  have hsplice : MirSemantics.spliceScalarSlice? oldSc 0 wSc = some wSc := by
    unfold MirSemantics.spliceScalarSlice?
    have hb1 : Bool.and (Nat.ble 1 wSc.sizeBytes)
        (Nat.ble (Nat.add 0 wSc.sizeBytes) oldSc.sizeBytes) = true := by
      simp [Nat.add_eq, Nat.ble_eq, hw_sz, hold_sz, hpos]
    have hb2 : Bool.and (Nat.beq 0 0) (Nat.beq wSc.sizeBytes oldSc.sizeBytes) = true := by
      simp [hw_sz, hold_sz]
    rw [hb1, hb2]
  have hk_lt : entry.targetLocal < locals.length := (List.getElem?_eq_some_iff.mp ht).1
  have hsA : get? locals entry.targetLocal = some (.init targetRootVal) := by
    simpa [get?] using ht
  unfold writePlaceValue
  dsimp only [get?]
  rw [hp]
  dsimp only [get?]
  rw [hlookup]
  dsimp only [get?]
  rcases hact with hpe | hpe <;> rw [hpe]
  all_goals
    dsimp only [get?]
    rw [hcons]
    dsimp only [get?]
    rw [← hcons]
    unfold MirSemantics.writeStackThinPtrTypedDeref
    rw [hpty, hoff0, hsA]
    dsimp only [MirSemantics.stripTransparentProjections, MirSemantics.checkDerefAlign,
      Nat.beq_refl]
    rw [halign, hval_ok]
    simp only [Bool.and_self]
    rw [hcons]
    dsimp only [MirSemantics.stripTransparentProjections]
    rw [← hcons]
    rcases hwshape with ⟨hproj, rfl⟩ | ⟨ph, pt, rootVal, hproj, hroot, hwp⟩
    · have hrd' : readProjectedValue locals targetRootVal [] = .ok (.scalar oldSc) := hproj ▸ hrd
      rw [hproj]
      dsimp only [MirSemantics.readProjectedForLocal]
      rw [hrd']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hsplice]
      simp [set?, hk_lt]
    · rw [ht] at hroot
      injection hroot with hinit
      injection hinit with hrv_eq
      subst hrv_eq
      have hnu' : MirSemantics.placeTouchesUnion body.localDecls body.layouts
          ⟨entry.targetLocal, ph :: pt⟩ = false := hproj ▸ hnu
      have hrd' : readProjectedValue locals targetRootVal (ph :: pt) = .ok (.scalar oldSc) :=
        hproj ▸ hrd
      rw [hproj]
      dsimp only [MirSemantics.readProjectedForLocal]
      rw [appendProjections_nil_right, hnu']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hrd']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hsplice]
      dsimp only [MirSemantics.writeProjectedForLocal]
      rw [hnu']
      dsimp only [MirSemantics.stripTransparentProjections]
      rw [hwp]
      simp [set?, hk_lt]

/-! ## The theorem -/

/-- **Correspondence theorem (one step, preserving `StateRelN`).** For a
fragment body `body`, its `minimize`-style translation `f`, and related states
(`StateRelN`), one Anneal MIR step and one MiniRust `Machine::step` correspond
in the sense of `StepRelN`. -/
theorem step_correspondence_N (body : CapturedMir) (f : Gen.Function) (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRelN body f ctx s m) :
    StepRelN body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨view, lm, hrel, hthr, hlo, hns, hbo⟩ := hrel
  obtain ⟨hphase, hargs, hn31, hret0, hdeclsOk, htemps, hbbs, hsdOk, hmvOk, hmtOk⟩ :=
    inFragment_spec body hfrag
  obtain ⟨hpa, _⟩ := inFragment_ptr body hfrag
  obtain ⟨_, hpresAll, _⟩ := ptrAliasingOk_spec hpa
  have hspec := translateFn_spec body f hf
  obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hrel.blk⟩
  have hbbmem : bb ∈ body.basicBlocks := List.mem_of_getElem? hbb
  obtain ⟨_, hstmts, hterm⟩ := hbbs bb hbbmem
  obtain ⟨tb, htb, hgetb⟩ := hspec.2.2 _ bb hbb
  obtain ⟨hlen, hstspec, htermspec⟩ := translateBlock_spec _ _ bb tb htb
  obtain ⟨hmvS, hmvT, hmvEdge⟩ := movesOk_spec hmvOk hbb
  have hshape : Shape m (ctxWithBorrows body ctx s.memory.borrows)
      [(ctxWithBorrows body ctx s.memory.borrows).caller,
        calleeFrameL f (ctxWithBorrows body ctx s.memory.borrows) lm s.frame.blockIdx
          s.frame.stmtIdx]
      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
  have hframe : FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) view lm (resetPick m)
      s.frame.blockIdx s.frame.stmtIdx :=
    ⟨FnLocalsSpec.of_translateFn hf, resetPick_shape hshape, hlo, hdeclsOk, hns⟩
  have hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals := hrel.stale.slots hlo.slots
  have hnA : s.frame.locals.length = body.localDecls.length := hrel.stale.1.trans hlo.nlocals
  have hdlo : ptrDeclLayoutsOk body = true := ptrDeclLayoutsOk_of_ptrAliasingOk hpa
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
    have hpresSt := stmtPreservesAddrTaken_not_target ((hpresAll bb hbbmem).1 st hstmem)
    rcases translateStatement_some hst' with
      ⟨dst, rv, pe, e, hkind, hpe, he, rfl⟩ |
      ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨i, hkind, rfl⟩ |
      ⟨i, hkind, rfl⟩ |
      ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨retagKind, p, pe, hkind, hpe, rfl⟩
    · ------------------------------------------------------------ assign
      have hdst_addr : dst.local_ ∉ bodyAddrTakenLocals body := hpresSt.1 dst rv hkind
      rcases dst with ⟨i, projs⟩
      simp only at hdst_addr
      have hbor_i := hbo.target_ne_of_not_addrTaken hdst_addr
      -- Storing a non-pointer slot into the local `_i` keeps `BorrowsOk`.
      have hBset : (projs = [] → ptrDerefReadSrc rv = none) →
          ∀ (d : LocalDecl), body.localDecls[i]? = some d → isPtrTy d.ty = false →
          ∀ (x : LocalSlot) (locals' : List LocalSlot),
            BorrowsOk body ctx (view.set i x) (advanceStmt s locals' s.memory) lm := by
        intro hndr d hd hnp x _
        refine hbo.advance_set_nonptr hbb hst ?_ i x (fun hk => absurd hk hdst_addr)
          (fun dp pv hdp hpty => by
            rw [hd] at hdp; cases hdp; rw [hnp] at hpty; cases hpty)
        have hnd_decl : isDeclPtrLocal body.localDecls i = false := by
          simp [isDeclPtrLocal, hd, hnp]
        have hpt_none : ptrPointeeOf d.ty = none := by
          cases hp : ptrPointeeOf d.ty <;> simp_all [isPtrTy]
        obtain ⟨stKind, stSpan⟩ := st
        simp only at hkind
        subst hkind
        cases projs with
        | nil => simp [ptrStmtStep, hnd_decl, hndr rfl]
        | cons ph pt =>
          cases ph with
          | deref =>
            cases pt with
            | nil => simp [statementOk, hd, hpt_none] at hok
            | cons _ _ => rfl
          | _ => rfl
      cases projs with
      | nil =>
        ---------------------------------------------------------- assign root local `_i = rv`
        simp only [translatePlace, Option.some.injEq] at hpe
        subst hpe
        obtain ⟨kind, span⟩ := st
        simp only at hkind
        subst hkind
        have hal : i ∉ alwaysStorageLiveLocals body :=
          mentionsOk_stmt hmtOk hbbmem hstmem (local_mem_stmtLocals_assign ⟨i, []⟩ rv span)
        cases hdi : body.localDecls[i]? with
        | none => simp [statementOk, hdi] at hok
        | some d =>
          have hi_decl : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
          have hi : i < s.frame.locals.length := by rw [hnA]; exact hi_decl
          by_cases hraw : ∃ mutbl q, rv = .rawPtr mutbl q
          · ------------------------------------------------------ `_i = &raw mutbl q`
            obtain ⟨mutbl, q, rfl⟩ := hraw
            by_cases hqder : ∃ p rest, q = ⟨p, .deref :: rest⟩
            · ---------------------------------------------------- `_i = &raw mutbl (*_p)`
              obtain ⟨p, rest, rfl⟩ := hqder
              obtain ⟨rfl, _, _, pointeeIt, dp, srcMutbl, hpt, hdp, hp_pt, hmut_compat⟩ :=
                statementOk_rawPtr_reborrow_spec hdi hok
              have hpRead : p ∉ movedBefore body s.frame.blockIdx s.frame.stmtIdx := by
                have h' := hreads
                rw [stmtReadsOk_rawPtr_reborrow] at h'
                simpa [List.contains_iff_mem] using h'
              have hpAgree : s.frame.locals[p]? = view[p]? := hrel.stale.agree hpRead
              rcases evalStatement_assign_rawPtr_reborrow_mr hframe hbo hns hfrag i d hdi mutbl
                  pointeeIt hpt p dp srcMutbl hdp hp_pt e he with
                ⟨parentPtr, parentEntry, relOff, hvp, hoff0, hlookup, htspec, hMok⟩ | ⟨hnot, hMub⟩
              · have hndis_env :
                    (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠
                      .disabled := by
                  have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
                  simpa [ptrStmtOk, ptrDerefReadSrc, copyRv, reborrowParentOf, bne_iff_ne] using hpst
                obtain ⟨hndis_p, hact_p⟩ :=
                  hbo.usable_of_not_disabled hndis_env hdp hp_pt hvp hlookup
                have hpA : s.frame.locals[p]? = some (.init (.ptr parentPtr 8)) := hpAgree.trans hvp
                have hmut_perm : mutbl = .mut → parentEntry.perm = .active ∨ parentEntry.perm = .reserved :=
                  fun hm => hact_p (hmut_compat hm)
                have he_mem := (lookupBorrow_mem_and_tag hlookup).1
                obtain ⟨_, _, _, _, hk_addr, _⟩ := hbo.entries_ok parentEntry he_mem
                obtain ⟨_, _, _, _, hrlen⟩ := hbo.perm_eq he_mem
                have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                obtain ⟨targetRootVal, ht_view⟩ := hbo.target_init hfrag parentEntry.targetLocal hk_addr
                have ht_init : s.frame.locals[parentEntry.targetLocal]? = some (.init targetRootVal) :=
                  hkAgree.trans ht_view
                have hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 :=
                  layoutPointerBytes_of_localDeclOk_isPtrTy
                    (hdeclsOk d (List.mem_of_getElem? hdi)) (by simp [isPtrTy, hpt])
                obtain ⟨hA1, hA2⟩ := evalStmt_assign_rawPtr_reborrow s body.localDecls body.layouts
                  i mutbl p dp srcMutbl pointeeIt hdp hp_pt span parentPtr hpA
                  (checkSafeRefDerefOk_of_ptrTargetSpec hdlo hdeclsOk hslotsA hdp hp_pt hoff0
                    hlookup hndis_p hrlen (hbo.entries_place parentEntry he_mem) htspec ht_init)
                  hi hbor_i hrel.protectors hptr8
                by_cases hdead : s.frame.locals[i]? = some .dead
                · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                  obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                  rw [hA2 hdead]
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                  rw [hA1 hdead]
                  obtain ⟨m3, hm3, h3⟩ := hMok hlive
                  obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                  refine StepRelN.tau' m4
                    (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                  have hstale := hrel.stale.assign hbb hst rfl (.init (.ptr parentPtr 8))
                  exact hrel.advanceN hfrag hbb hlt _
                    (view.set i (.init (.ptr parentPtr 8))) _ lm m4 h4.threads h4.active
                    (by rw [h4.allocs]; exact h3.locs)
                    h3.nonScalar hstale
                    (retLive_set hrel.retLive i (by simp))
                    (hbo.rawPtr_reborrow hlo.nlocals hbb hst hdi hdp (by simp [isPtrTy, hp_pt]) rfl
                      parentPtr hoff0 hvp parentEntry hlookup hndis_p hmut_perm pointeeIt relOff
                      htspec hpt hdst_addr _)
                    rfl rfl rfl rfl
              · have hAub := evalStmt_assign_ub s body.localDecls body.layouts ⟨i, []⟩
                  (.rawPtr mutbl ⟨p, [.deref]⟩) span
                  ((evalRvalue_reborrow_ub_of_not_init s.frame.locals p s.memory body.localDecls
                    body.layouts (by rw [hpAgree]; exact hnot)).1 mutbl)
                rw [hAub]
                by_cases hdead : s.frame.locals[i]? = some .dead
                · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                  obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                  obtain ⟨msg, hmsg⟩ := hMub hlive
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
            · ---------------------------------------------------- direct `_i = &raw mutbl q`
              have hnd_qproj : ∀ rest, q.projection ≠ .deref :: rest := by
                intro rest hr
                exact hqder ⟨q.local_, rest, by cases q; simp only at hr; subst hr; rfl⟩
              obtain ⟨_, pointeeIt, relOff, hpt, htspec⟩ := statementOk_rawPtr_spec hdi hnd_qproj hok
              have hq_addr : q.local_ ∈ bodyAddrTakenLocals body :=
                mem_bodyAddrTakenLocals hbbmem hstmem rfl hnd_qproj
              obtain ⟨hni, hnd, _⟩ :=
                evalTargetPlace hframe hbo hns hfrag q pointeeIt relOff htspec hq_addr
              obtain ⟨hnd_q, _, _⟩ := hbo.target_ptrs hfrag q.local_ hq_addr
              have hqAgree := hrel.stale.addrTaken_eq hpa hq_addr
              have hq_lt : q.local_ < s.frame.locals.length := by
                rw [hnA]; exact (ptrTargetSpec_cases hdeclsOk htspec).1
              have hsq : s.frame.locals[q.local_]? = some s.frame.locals[q.local_] :=
                List.getElem?_eq_getElem hq_lt
              have hliveq : s.frame.locals[q.local_] ≠ .dead := fun hc =>
                hnd_q (by rw [← hqAgree, hsq, hc])
              have hqi : q.local_ ≠ i := fun h => hdst_addr (h ▸ hq_addr)
              have hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 :=
                layoutPointerBytes_of_localDeclOk_isPtrTy
                  (hdeclsOk d (List.mem_of_getElem? hdi)) (by simp [isPtrTy, hpt])
              obtain ⟨hA1, hA2⟩ := evalStmt_assign_rawPtr s body.localDecls body.layouts i mutbl q
                pointeeIt relOff htspec span hnd hni _ hsq hliveq hi hbor_i hqi hrel.protectors hptr8
              by_cases hdead : s.frame.locals[i]? = some .dead
              · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                rw [hA2 hdead]
                exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
              · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                rw [hA1 hdead]
                obtain ⟨m3, hm3, h3⟩ := evalStatement_assign_rawPtr_mr hframe hbo hns hfrag i d hdi
                  mutbl q pointeeIt relOff hpt hlive htspec hq_addr e he
                obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                refine StepRelN.tau' m4
                  (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                have hstale := hrel.stale.assign hbb hst rfl (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))
                exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
                  _ lm m4 h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar hstale
                  (retLive_set hrel.retLive i (by simp))
                  (hbo.rawPtr hlo.nlocals hbb hst hdi rfl pointeeIt relOff htspec hpt hdst_addr _)
                  rfl rfl rfl rfl
          · by_cases href : ∃ bkind q, rv = .ref bkind q
            · ---------------------------------------------------- `_i = &q` / `_i = &mut q`
              obtain ⟨bkind, q, rfl⟩ := href
              by_cases hqder : ∃ p rest, q = ⟨p, .deref :: rest⟩
              · -------------------------------------------------- `_i = &(*_p)` / `_i = &mut (*_p)`
                obtain ⟨p, rest, rfl⟩ := hqder
                obtain ⟨rfl, _, _, pointeeIt, dp, srcMutbl, hpt, hdp, hp_pt, hmut_compat⟩ :=
                  statementOk_ref_reborrow_spec hdi hok
                have hpRead : p ∉ movedBefore body s.frame.blockIdx s.frame.stmtIdx := by
                  have h' := hreads
                  rw [stmtReadsOk_ref_reborrow] at h'
                  simpa [List.contains_iff_mem] using h'
                have hpAgree : s.frame.locals[p]? = view[p]? := hrel.stale.agree hpRead
                rcases evalStatement_assign_reborrow_mr hframe hbo hns hfrag i d hdi
                    (borrowKindMutbl bkind) pointeeIt hpt p dp srcMutbl hdp hp_pt
                    (.inr ⟨bkind, rfl, rfl⟩) e he with
                  ⟨parentPtr, parentEntry, relOff, hvp, hoff0, hlookup, htspec, hMok⟩ | ⟨hnot, hMub⟩
                · have hndis_env :
                      (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠
                        .disabled := by
                    have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
                    simpa [ptrStmtOk, ptrDerefReadSrc, copyRv, reborrowParentOf, bne_iff_ne] using hpst
                  obtain ⟨hndis_p, hact_p⟩ :=
                    hbo.usable_of_not_disabled hndis_env hdp hp_pt hvp hlookup
                  have hpA : s.frame.locals[p]? = some (.init (.ptr parentPtr 8)) := hpAgree.trans hvp
                  have hmut_perm :
                      borrowKindMutbl bkind = .mut →
                        parentEntry.perm = .active ∨ parentEntry.perm = .reserved :=
                    fun hm => hact_p (hmut_compat hm)
                  have he_mem := (lookupBorrow_mem_and_tag hlookup).1
                  obtain ⟨_, _, _, _, hk_addr, _⟩ := hbo.entries_ok parentEntry he_mem
                  have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                  obtain ⟨targetRootVal, ht_view⟩ :=
                    hbo.target_init hfrag parentEntry.targetLocal hk_addr
                  have ht_init : s.frame.locals[parentEntry.targetLocal]? =
                      some (.init targetRootVal) := hkAgree.trans ht_view
                  have hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 :=
                    layoutPointerBytes_of_localDeclOk_isPtrTy
                      (hdeclsOk d (List.mem_of_getElem? hdi)) (by simp [isPtrTy, hpt])
                  obtain ⟨hA1, hA2⟩ := evalStmt_assign_ref_reborrow s body.localDecls body.layouts
                    i bkind p dp srcMutbl pointeeIt hdp hp_pt span parentPtr hpA hoff0 parentEntry
                    hlookup hndis_p hmut_perm targetRootVal ht_init
                    (resolveRefDerefTarget?_of_ptrTargetSpec hdlo hdeclsOk hslotsA hdp hp_pt hoff0
                      (hbo.entries_place parentEntry he_mem) htspec ht_init)
                    hi hbor_i hrel.protectors hptr8
                  by_cases hdead : s.frame.locals[i]? = some .dead
                  · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                    obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                    rw [hA2 hdead]
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                    rw [hA1 hdead]
                    obtain ⟨m3, hm3, h3⟩ := hMok hlive
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    refine StepRelN.tau' m4
                      (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                    have hstale := hrel.stale.assign hbb hst rfl (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))
                    exact hrel.advanceN hfrag hbb hlt _
                      (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))) _ lm m4 h4.threads h4.active
                      (by rw [h4.allocs, ctxWithBorrows_refReborrowEntry_eq]; exact h3.locs)
                      h3.nonScalar hstale
                      (retLive_set hrel.retLive i (by simp))
                      (hbo.reborrow hlo.nlocals hbb hst hdi hdp (by simp [isPtrTy, hp_pt]) rfl rfl
                        parentPtr hvp parentEntry hlookup hndis_p pointeeIt relOff htspec hpt
                        hdst_addr _ (.inr ⟨rfl, rfl⟩) (.inr ⟨bkind, rfl, rfl⟩)
                        (by cases bkind <;> simp [refReborrowEntry, refReborrowPerm]))
                      rfl rfl rfl rfl
                · have hAub := evalStmt_assign_ub s body.localDecls body.layouts ⟨i, []⟩
                    (.ref bkind ⟨p, [.deref]⟩) span
                    ((evalRvalue_reborrow_ub_of_not_init s.frame.locals p s.memory body.localDecls
                      body.layouts (by rw [hpAgree]; exact hnot)).2 bkind)
                  rw [hAub]
                  by_cases hdead : s.frame.locals[i]? = some .dead
                  · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                    obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                    obtain ⟨msg, hmsg⟩ := hMub hlive
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
              · -------------------------------------------------- direct `_i = &q` / `_i = &mut q`
                have hnd_qproj : ∀ rest, q.projection ≠ .deref :: rest := by
                  intro rest hr
                  exact hqder ⟨q.local_, rest, by cases q; simp only at hr; subst hr; rfl⟩
                obtain ⟨_, pointeeIt, relOff, hpt, htspec⟩ :=
                  statementOk_ref_spec hdi hnd_qproj hok
                have hdb : directBorrowOf (.ref bkind q) = some (borrowKindMutbl bkind, q) :=
                  directBorrowOf_ref_of_nonDeref hnd_qproj
                have hq_addr : q.local_ ∈ bodyAddrTakenLocals body :=
                  mem_bodyAddrTakenLocals_of_directBorrow hbbmem hstmem rfl hdb
                obtain ⟨hni, hnd, _⟩ :=
                  evalTargetPlace hframe hbo hns hfrag q pointeeIt relOff htspec hq_addr
                obtain ⟨hnd_q, _, _⟩ := hbo.target_ptrs hfrag q.local_ hq_addr
                have hqAgree := hrel.stale.addrTaken_eq hpa hq_addr
                have hq_lt : q.local_ < s.frame.locals.length := by
                  rw [hnA]; exact (ptrTargetSpec_cases hdeclsOk htspec).1
                have hsq : s.frame.locals[q.local_]? = some s.frame.locals[q.local_] :=
                  List.getElem?_eq_getElem hq_lt
                have hliveq : s.frame.locals[q.local_] ≠ .dead := fun hc =>
                  hnd_q (by rw [← hqAgree, hsq, hc])
                have hqi : q.local_ ≠ i := fun h => hdst_addr (h ▸ hq_addr)
                obtain ⟨hA1, hA2⟩ := evalStmt_assign_ref s body.localDecls body.layouts i bkind
                  q pointeeIt relOff htspec span hnd hni _ hsq hliveq hi hbor_i hqi hrel.protectors
                by_cases hdead : s.frame.locals[i]? = some .dead
                · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                  obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                  rw [hA2 hdead]
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                  rw [hA1 hdead]
                  obtain ⟨m3, hm3, h3⟩ := evalStatement_assign_ref_mr hframe hbo hns hfrag i d hdi
                    bkind q pointeeIt relOff hpt hlive htspec hq_addr e he
                  obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                  refine StepRelN.tau' m4
                    (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                  have hstale := hrel.stale.assign hbb hst rfl (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))
                  exact hrel.advanceN hfrag hbb hlt _
                    (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))) _ lm m4 h4.threads h4.active
                    (by rw [h4.allocs]; exact h3.locs) h3.nonScalar hstale
                    (retLive_set hrel.retLive i (by simp))
                    (hbo.directBorrow hlo.nlocals hbb hst hdi rfl hdb pointeeIt relOff htspec
                      hpt hdst_addr _ (refBorrowEntry_cases _ _ _)
                      (by
                        cases bkind with
                        | shared => simp [refBorrowEntry, refBorrowPerm]
                        | «mut» tp =>
                          cases tp with
                          | true => simp [refBorrowEntry, refBorrowPerm]
                          | false =>
                            rcases q with ⟨_, projs⟩
                            cases projs with
                            | nil => simp [borrowStartsHot]
                            | cons ph pt =>
                              cases ph with
                              | deref => exact False.elim (hnd_qproj pt rfl)
                              | _ => simp [borrowStartsHot]))
                    rfl rfl rfl rfl
            · by_cases hder : ∃ p rest, copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)
              · ---------------------------------------------------- `_i = copy (*_p)` / `move (*_p)`
                obtain ⟨p, rest, hcrv⟩ := hder
                obtain ⟨rfl, it, dp, srcMutbl, hit, hdp, hpt⟩ := statementOk_derefRead hdi hcrv hok
                have hitd : itOf d body.layouts = it := (tyOf_int hit).2
                have hint : intTypeOf d.ty = some (itOf d body.layouts) := by rw [hitd]; exact hit
                have hnpd : isPtrTy d.ty = false := Bool.eq_false_iff.mpr fun hp => by
                  rw [(not_other_of_isPtrTy (layouts := body.layouts) hp).2.2.2.1] at hit; cases hit
                have hnd_i_decl : isDeclPtrLocal body.localDecls i = false := by
                  simp [isDeclPtrLocal, hdi, hnpd]
                have hsrc_p : ptrDerefReadSrc rv = some p := by
                  simp [ptrDerefReadSrc, hcrv]
                have hpRead : p ∉ movedBefore body s.frame.blockIdx s.frame.stmtIdx := by
                  have h' := hreads
                  rw [stmtReadsOk_derefRead hcrv] at h'
                  simpa [List.contains_iff_mem] using h'
                have hpAgree : s.frame.locals[p]? = view[p]? := hrel.stale.agree hpRead
                rw [hcrv] at he
                have he' := translateRvalue_derefRead hdp hpt he
                subst he'
                have hgood := hframe.decl_good i d hdi
                have hspecF := (translateFn_spec body f hf).2.1 i d hdi
                let memFrz : MirSemantics.Memory :=
                  { s.memory with
                    borrows := MirSemantics.freezeDerefReadBorrowsAt s.frame.locals p []
                      s.memory.borrows }
                obtain ⟨res, hMok, hMnone, hAok, hAnone, hBfrz⟩ : ∃ res : Option Value,
                    (∀ v, res = some v → view[i]? ≠ some .dead →
                      ∃ m3, evalStatement (resetPick m) (.Assign (.Local (localName i))
                          (.Load (.Deref (.Load (.Local (localName p))) (.Int it)))) = .ok m3 ∧
                        FrameOk body f (ctxWithBorrows body ctx s.memory.borrows)
                          (view.set i (.init v)) lm m3 s.frame.blockIdx s.frame.stmtIdx) ∧
                    (res = none → view[i]? ≠ some .dead →
                      ∃ msg, evalStatement (resetPick m) (.Assign (.Local (localName i))
                          (.Load (.Deref (.Load (.Local (localName p))) (.Int it)))) =
                        .error (.ub msg)) ∧
                    (∀ v, res = some v →
                      evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
                        .ok v s.frame.locals memFrz) ∧
                    (res = none →
                      evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts = .ub) ∧
                    (∀ v (locals' : List LocalSlot), res = some v →
                      ctxWithBorrows body ctx memFrz.borrows =
                        ctxWithBorrows body ctx s.memory.borrows ∧
                      BorrowsOk body ctx (view.set i (.init v))
                        (advanceStmt s locals' memFrz) lm) := by
                  rcases evalPlace_deref hframe hbo hns hfrag p dp srcMutbl it hdp hpt with
                    ⟨ptrVal, entry, relOff, m1, hvp, hoff0, hlookup, hk_addr, htspec, hderef, h1,
                      htgt⟩ |
                    ⟨hnot, msg, hmsg⟩
                  · obtain ⟨hni, _, _⟩ := evalTargetPlace hframe hbo hns hfrag
                      ⟨entry.targetLocal, entry.targetProjection⟩ it relOff htspec hk_addr
                    have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                    have hndis_env :
                        (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠
                          .disabled := by
                      have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
                      simpa [ptrStmtOk, ptrDerefReadSrc, hcrv, bne_iff_ne] using hpst
                    have hndis_p : entry.perm ≠ .disabled :=
                      (hbo.usable_of_not_disabled hndis_env hdp hpt hvp hlookup).1
                    have hpA : s.frame.locals[p]? = some (.init (.ptr ptrVal 8)) :=
                      hpAgree.trans hvp
                    have he_mem := (lookupBorrow_mem_and_tag hlookup).1
                    obtain ⟨targetRootVal, ht_view⟩ :=
                      hbo.target_init hfrag entry.targetLocal hk_addr
                    have ht_init : s.frame.locals[entry.targetLocal]? =
                        some (.init targetRootVal) := hkAgree.trans ht_view
                    obtain ⟨hEqOk, hEqUb⟩ := evalRvalue_derefRead_eq s.frame.locals hcrv s.memory
                      body.localDecls body.layouts hdp hpt entry
                      (evalOperand_deref_eq_target_typed hdlo hdeclsOk hslotsA s.memory hdp hpt hpA
                        hoff0 hlookup hndis_p (hbo.entries_place entry he_mem) htspec ht_init)
                    have hagq : ReadsAgree s.frame.locals view
                        [.copy ⟨entry.targetLocal, entry.targetProjection⟩] :=
                      readsAgree_copy_target hni hkAgree
                    have hopok := ptrTargetSpec_operandOk hdeclsOk htspec
                    have hokq : rvalueOk body.layouts body.localDecls (itOf d body.layouts)
                        (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) = true := by
                      rw [hitd]; exact hopok
                    obtain ⟨targetPe, htpe⟩ : ∃ pe, translatePlace body.localDecls
                        ⟨entry.targetLocal, entry.targetProjection⟩ = some pe := by
                      simp only [operandOk, Bool.and_eq_true, translateOperand,
                        Option.isSome_map] at hopok
                      exact Option.isSome_iff_exists.mp hopok.2
                    have heq : translateRvalue body.layouts body.localDecls (some d.ty)
                        (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) =
                          some (.Load targetPe) := by
                      simp [translateRvalue, translateOperand, htpe]
                    have hfr : opBits s.frame.locals
                        (.copy ⟨entry.targetLocal, entry.targetProjection⟩) =
                        rvBits body.localDecls view (itOf d body.layouts) body.layouts
                          (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) := by
                      simpa [rvBits] using rvBits_frame_raw (decls := body.localDecls)
                        (it := itOf d body.layouts)
                        (layouts := body.layouts)
                        (rv := .use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) hagq
                    obtain ⟨hop1, hop2⟩ := evalOperand_frag body.localDecls s.frame.locals hslotsA
                      hnA (itOf d body.layouts)
                      (.copy ⟨entry.targetLocal, entry.targetProjection⟩) hokq
                      s.memory.borrows s.memory.globals s.memory.callerLocals
                    have hMeq : view[i]? ≠ some .dead →
                        evalStatement (resetPick m) (.Assign (.Local (localName i))
                          (.Load (.Deref (.Load (.Local (localName p))) (.Int it)))) =
                        evalStatement m1 (.Assign (.Local (localName i)) (.Load targetPe)) := by
                      intro hlive
                      obtain ⟨_, slot, _, hs⟩ := hframe.slot_exists i hi_decl
                      obtain ⟨pi, hpi⟩ := hframe.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
                      exact evalStatement_assign_local_load_eq
                        (evalPlace_local_some hframe.shape i _ hspecF.2 pi hpi)
                        (evalPlace_local_some h1.shape i _ hspecF.2 pi hpi) hderef (htgt targetPe htpe)
                    refine ⟨(rvBits body.localDecls view (itOf d body.layouts) body.layouts
                        (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩))).map
                        (fun r => .scalar ⟨r, (itOf d body.layouts).size.bytes⟩), ?_, ?_, ?_, ?_, ?_⟩
                    · intro v hv hlive
                      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                      rw [hMeq hlive]
                      exact (evalStatement_assign h1 i d hdi hlive hint _ hokq _ heq).1 r hr
                    · intro hv hlive
                      rw [hMeq hlive]
                      exact (evalStatement_assign h1 i d hdi hlive hint _ hokq _ heq).2
                        (Option.map_eq_none_iff.mp hv)
                    · intro v hv
                      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                      exact hEqOk _ (hop1 r (hfr.trans hr))
                    · intro hv
                      exact hEqUb (hop2 (hfr.trans (Option.map_eq_none_iff.mp hv)))
                    · intro v locals' _
                      refine ⟨ctxWithBorrows_freezeDerefReadBorrowsAt_eq body ctx hpA hlookup, ?_⟩
                      exact hbo.derefRead hbb hst rfl hnd_i_decl hdst_addr hsrc_p hdp
                        (by simp [isPtrTy, hpt]) ptrVal entry hvp hpA hlookup (.init v)
                        (fun dp' pv hdp' hpty => by
                          rw [hdi] at hdp'; cases hdp'; rw [hnpd] at hpty; cases hpty)
                  · refine ⟨none, fun _ h => (by cases h), fun _ hlive => ?_, fun _ h => (by cases h),
                      fun _ => ?_, fun _ _ h => (by cases h)⟩
                    · obtain ⟨_, slot, _, hs⟩ := hframe.slot_exists i hi_decl
                      obtain ⟨pi, hpi⟩ := hframe.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
                      exact ⟨msg, evalStatement_assign_load_ub
                        (evalPlace_local_some hframe.shape i _ hspecF.2 pi hpi) hmsg⟩
                    · exact evalRvalue_derefRead_ub s.frame.locals hcrv s.memory body.localDecls
                        body.layouts (by rw [hpAgree]; exact hnot)
                have hbor_frz : ∀ e ∈ memFrz.borrows, e.targetLocal ≠ i := by
                  intro e he_mem
                  dsimp only [memFrz, MirSemantics.freezeDerefReadBorrowsAt] at he_mem
                  split at he_mem
                  · split at he_mem
                    · rw [freezeTreeBorrowsOnReadAtProj_eq_map, List.mem_map] at he_mem
                      obtain ⟨e0, he0, rfl⟩ := he_mem
                      rw [(updateBorrowPermOnReadAtProj_freezeOrSelf _ _ _ _ _ _).targetLocal]
                      exact hbor_i e0 he0
                    · exact hbor_i e he_mem
                  · exact hbor_i e he_mem
                obtain ⟨hA1, hA2⟩ := evalStmt_assign_val_mem s body.localDecls body.layouts i rv
                  span hi
                by_cases hdead : s.frame.locals[i]? = some .dead
                · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                  obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal
                    (.Load (.Deref (.Load (.Local (localName p))) (.Int it)))
                  have hA : evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ body.localDecls body.layouts =
                      MirStepNode.fail .ub := by
                    cases hres : res with
                    | none => exact hA2 (hAnone hres)
                    | some v =>
                      exact (hA1 v memFrz (hAok v hres) hbor_frz hrel.protectors).2 hdead
                  rw [hA]
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                  cases hres : res with
                  | none =>
                    rw [hA2 (hAnone hres)]
                    obtain ⟨msg, hmsg⟩ := hMnone hres hlive
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  | some v =>
                    rw [(hA1 v memFrz (hAok v hres) hbor_frz hrel.protectors).1 hdead]
                    obtain ⟨m3, hm3, h3⟩ := hMok v hres hlive
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    obtain ⟨hctx_frz, hB_frz⟩ := hBfrz v (s.frame.locals.set i (.init v)) hres
                    refine StepRelN.tau' m4
                      (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                    have hstale := hrel.stale.assign hbb hst rfl (.init v)
                    rw [rvPost_derefRead hcrv] at hstale
                    exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init v)) _ lm m4 h4.threads
                      h4.active (by rw [h4.allocs, hctx_frz]; exact h3.locs) h3.nonScalar hstale
                      (retLive_set hrel.retLive i (by simp)) hB_frz rfl rfl rfl rfl
              · ---------------------------------------------------- any other rvalue
                have hnder : ∀ p rest, copyRv rv ≠ .use (.copy ⟨p, .deref :: rest⟩) :=
                  fun p rest h => hder ⟨p, rest, h⟩
                have hndr : ptrDerefReadSrc rv = none := by
                  unfold ptrDerefReadSrc
                  split
                  · rename_i p rest hcrv
                    exact absurd hcrv (hnder p rest)
                  · rfl
                have hBset0 := hBset (fun _ => hndr)
                have hnraw : ∀ m q, rv ≠ .rawPtr m q := fun m q h => hraw ⟨m, q, h⟩
                have hnref : ∀ bk q, rv ≠ .ref bk q := fun bk q h => href ⟨bk, q, h⟩
                have hreadsMo : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx)
                    (rvOperands rv) = true := by
                  rw [← stmtReadsOk_root_of_not_deref (span := span) (i := i) hnraw hnref hnder]
                  exact hreads
                have hr0 : readsOk [] (rvOperands rv) = true :=
                  readsOk_mono (fun _ h => by simp at h) hreadsMo
                have hagree := hrel.stale.readsAgree hreadsMo
                simp only [statementOk] at hok
                obtain ⟨res, hk, hmf, hMok, hMnone, hAok, hAnone, hBok⟩ : ∃ res : Option Value,
                    moveKind rv = true ∧
                    MoveFrameOk s.frame.locals rv s.memory body.localDecls body.layouts ∧
                    (∀ v, res = some v → view[i]? ≠ some .dead →
                      ∃ m3, evalStatement (resetPick m) (.Assign (.Local (localName i)) e) = .ok m3 ∧
                        FrameOk body f (ctxWithBorrows body ctx s.memory.borrows) (view.set i (.init v))
                          lm m3 s.frame.blockIdx s.frame.stmtIdx) ∧
                    (res = none → view[i]? ≠ some .dead →
                      ∃ msg, evalStatement (resetPick m) (.Assign (.Local (localName i)) e) =
                        .error (.ub msg)) ∧
                    (∀ v, res = some v →
                      evalRvalue s.frame.locals (copyRv rv) s.memory body.localDecls body.layouts =
                        .ok v s.frame.locals s.memory) ∧
                    (res = none →
                      evalRvalue s.frame.locals (copyRv rv) s.memory body.localDecls body.layouts =
                        .ub) ∧
                    (∀ v (locals' : List LocalSlot), res = some v →
                      BorrowsOk body ctx (view.set i (.init v)) (advanceStmt s locals' s.memory) lm) := by
                  cases hb : isBoolTy d.ty with
                  | true =>
                    have hnp : isPtrTy d.ty = false := Bool.eq_false_iff.mpr fun hp => by
                      rw [(not_other_of_isPtrTy (layouts := body.layouts) hp).1] at hb; cases hb
                    have hit : itOf d body.layouts = u8Ty := (tyOf_bool hb).2
                    have hokB : rvalueOkB body.layouts body.localDecls (copyRv rv) = true := by
                      simpa [hdi, hb] using hok
                    have hfr : rvBitsB body.localDecls s.frame.locals (copyRv rv) body.layouts =
                        rvBitsB body.localDecls view (copyRv rv) body.layouts := rvBitsB_frame hagree
                    obtain ⟨hA1, hA2⟩ := evalRvalue_fragB body.localDecls s.frame.locals hslotsA hnA
                      (copyRv rv) hokB s.memory
                    refine ⟨(rvBitsB body.localDecls view (copyRv rv) body.layouts).map
                        (fun r => .scalar ⟨r, (itOf d body.layouts).size.bytes⟩),
                      moveKind_of_rvalueOkB hokB,
                      moveFrameOk_of_rvalueOkB hokB hslotsA hnA s.memory,
                      ?_, ?_, ?_, ?_, fun v l _ => hBset0 d hdi hnp _ l⟩
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
                      have hnp : isPtrTy d.ty = false := Bool.eq_false_iff.mpr fun hp => by
                        rw [(not_other_of_isPtrTy (layouts := body.layouts) hp).2.1] at ho; cases ho
                      have hit : itOf d body.layouts = u8Ty := (tyOf_ordering ho).2
                      have hokO : rvalueOkO body.layouts body.localDecls (copyRv rv) = true := by
                        simpa [hdi, hb, ho] using hok
                      have hfr : rvBitsO body.localDecls s.frame.locals (copyRv rv) body.layouts =
                          rvBitsO body.localDecls view (copyRv rv) body.layouts := rvBitsO_frame hagree
                      obtain ⟨hA1, hA2⟩ := evalRvalue_fragO body.localDecls s.frame.locals hslotsA hnA
                        (copyRv rv) hokO s.memory
                      refine ⟨(rvBitsO body.localDecls view (copyRv rv) body.layouts).map
                          (fun r => .scalar ⟨r, (itOf d body.layouts).size.bytes⟩),
                        moveKind_of_rvalueOkO hokO,
                        moveFrameOk_of_rvalueOkO hokO s.frame.locals s.memory,
                        ?_, ?_, ?_, ?_, fun v l _ => hBset0 d hdi hnp _ l⟩
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
                      cases htup : intBoolTupleOf d.ty with
                      | some it =>
                        have hnp : isPtrTy d.ty = false := Bool.eq_false_iff.mpr fun hp => by
                          rw [(not_other_of_isPtrTy (layouts := body.layouts) hp).2.2.1] at htup
                          cases htup
                        have hitd : itOf d body.layouts = it := (tyOf_tuple htup).2
                        have htup' : intBoolTupleOf d.ty = some (itOf d body.layouts) := by
                          rw [hitd]; exact htup
                        have hokT : rvalueOkTuple body.layouts body.localDecls (itOf d body.layouts)
                            (copyRv rv) = true := by
                          rw [hitd]; simpa [hdi, hb, ho, htup] using hok
                        have hgood := hframe.decl_good i d hdi
                        have hpmir : placeMirTy body.localDecls ⟨i, []⟩ = some d.ty := by
                          simp [placeMirTy, hdi, resolveProjTy]
                        rw [hpmir] at he
                        have hfr : rvTupleBits s.frame.locals (itOf d body.layouts) (copyRv rv) =
                            rvTupleBits view (itOf d body.layouts) (copyRv rv) :=
                          rvTupleBits_frame hagree
                        obtain ⟨hA1, hA2⟩ := evalRvalue_fragTuple body.localDecls s.frame.locals hslotsA
                          hnA (itOf d body.layouts) hgood (copyRv rv) hokT s.memory
                        refine ⟨(rvTupleBits view (itOf d body.layouts) (copyRv rv)).map
                            (fun pr => .aggregate 0
                              [.scalar ⟨pr.1, (itOf d body.layouts).size.bytes⟩, .scalar ⟨pr.2, 1⟩]),
                          moveKind_of_rvalueOkTuple hokT,
                          moveFrameOk_of_rvalueOkTuple hokT s.frame.locals s.memory,
                          ?_, ?_, ?_, ?_,
                          fun v l _ => hBset0 d hdi hnp _ l⟩
                        · intro v hv hlive
                          obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
                          exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv)
                            hokT e he).1 bits b hpb
                        · intro hv hlive
                          exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv)
                            hokT e he).2 (Option.map_eq_none_iff.mp hv)
                        · intro v hv
                          obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
                          exact hA1 bits b (hfr.trans hpb)
                        · intro hv
                          exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
                      | none =>
                        cases hit : intTypeOf d.ty with
                        | some it =>
                          have hnp : isPtrTy d.ty = false := Bool.eq_false_iff.mpr fun hp => by
                            rw [(not_other_of_isPtrTy (layouts := body.layouts) hp).2.2.2.1] at hit
                            cases hit
                          have hitd : itOf d body.layouts = it := (tyOf_int hit).2
                          have hok' : rvalueOk body.layouts body.localDecls (itOf d body.layouts)
                              (copyRv rv) = true := by
                            have hpd := ptrDerefReadOk_of_not_deref (decls := body.localDecls)
                              (it := it) hnder
                            rw [hitd]; simpa [hdi, hb, ho, htup, hit, hpd] using hok
                          have hint : intTypeOf d.ty = some (itOf d body.layouts) := by
                            rw [hitd]; exact hit
                          have hgood := hframe.decl_good i d hdi
                          have hfr : rvBits body.localDecls s.frame.locals (itOf d body.layouts)
                              body.layouts (copyRv rv) =
                              rvBits body.localDecls view (itOf d body.layouts) body.layouts
                                (copyRv rv) := rvBits_frame hagree
                          have hnsOps : OpsNonScalarInit body.localDecls s.frame.locals
                              (rvOperands (copyRv rv)) := (hns.opsInit_of_readsAgree hagree).copy
                          obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA
                            hnA (itOf d body.layouts) hgood (copyRv rv) hok' hnsOps s.memory
                          refine ⟨(rvBits body.localDecls view (itOf d body.layouts) body.layouts
                              (copyRv rv)).map (fun r => .scalar ⟨r, (itOf d body.layouts).size.bytes⟩),
                            moveKind_of_rvalueOk hok',
                            moveFrameOk_of_rvalueOk hok' s.frame.locals s.memory,
                            ?_, ?_, ?_, ?_, fun v l _ => hBset0 d hdi hnp _ l⟩
                          · intro v hv hlive
                            obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                            exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv)
                              hok' e he).1 r hr
                          · intro hv hlive
                            exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv)
                              hok' e he).2 (Option.map_eq_none_iff.mp hv)
                          · intro v hv
                            obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                            exact hA1 r (hfr.trans hr)
                          · intro hv
                            exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
                        | none =>
                          cases ha : arrayTypeOf d.ty with
                          | some p =>
                            obtain ⟨elemIt, count⟩ := p
                            have hnp : isPtrTy d.ty = false := isPtrTy_false_of_arrayTypeOf ha
                            simp only [hdi, hb, ho, htup, hit, ha] at hok
                            obtain ⟨hcrv, _⟩ := arrayRvalueOk_noMove hok
                            rw [hcrv] at he
                            have hfr : arrayRvElems s.frame.locals elemIt rv =
                                arrayRvElems view elemIt rv := arrayRvElems_frame elemIt rv hagree
                            obtain ⟨hA1, hA2⟩ := evalRvalue_array_frag body.localDecls s.frame.locals
                              hslotsA hnA elemIt count rv hok s.memory
                            refine ⟨(arrayRvElems view elemIt rv).map (fun elems => .aggregate 0 elems),
                              moveKind_of_arrayRvalueOk hok,
                              moveFrameOk_of_arrayRvalueOk hok s.frame.locals s.memory,
                              ?_, ?_, ?_, ?_,
                              fun v l _ => hBset0 d hdi hnp _ l⟩
                            · intro v hv _
                              obtain ⟨elems, hel, rfl⟩ := Option.map_eq_some_iff.mp hv
                              exact (evalStatement_assign_array hframe i d hdi elemIt count ha rv
                                hok e he).1 elems hel
                            · intro hv _
                              exact (evalStatement_assign_array hframe i d hdi elemIt count ha rv
                                hok e he).2 (Option.map_eq_none_iff.mp hv)
                            · intro v hv
                              rw [hcrv]
                              obtain ⟨elems, hel, rfl⟩ := Option.map_eq_some_iff.mp hv
                              exact hA1 elems (hfr.trans hel)
                            · intro hv
                              rw [hcrv]
                              exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
                          | none =>
                            cases ht : tupleTypeOf body.layouts d.ty with
                            | none =>
                              ------------------------------------------ pointer-copying rvalue
                              cases hpt : ptrPointeeOf d.ty with
                              | none => simp [hdi, hb, ho, htup, hit, ha, ht, hpt] at hok
                              | some pr =>
                                obtain ⟨mutbl, pointeeIt⟩ := pr
                                have hokP : ptrRvalueOk body.layouts body.localDecls mutbl pointeeIt
                                    (isRefTy d.ty) (copyRv rv) = true := by
                                  simpa [hdi, hb, ho, htup, hit, ha, ht, hpt] using hok
                                have hnrawC : ∀ m q, copyRv rv ≠ .rawPtr m q := by
                                  intro m q h
                                  cases rv with
                                  | rawPtr m' q' => exact hnraw m' q' rfl
                                  | _ => simp [copyRv] at h
                                have hnrefC : ∀ bk q, copyRv rv ≠ .ref bk q := by
                                  intro bk q h
                                  cases rv with
                                  | ref bk' q' => exact hnref bk' q' rfl
                                  | _ => simp [copyRv] at h
                                obtain ⟨pE, hpmemE, hmut_ip, hMptr, hMub⟩ :=
                                  evalStatement_assign_ptrRvalue_mr hframe hbo hns hfrag i d hdi hpt
                                    hokP hnrawC hnrefC e he
                                have hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 :=
                                  layoutPointerBytes_of_localDeclOk_isPtrTy
                                    (hdeclsOk d (List.mem_of_getElem? hdi)) (by simp [isPtrTy, hpt])
                                obtain ⟨pA, _, hpmemA, ⟨srcMutbl, hsrc, _⟩, hAev⟩ :=
                                  evalRvalue_ptrRvalue hokP hnrawC hnrefC hptr8
                                obtain rfl : pE = pA := ptrRvalueOk_copy_unique hokP hpmemE hpmemA
                                have hpAgree : s.frame.locals[pE]? = view[pE]? :=
                                  hagree.of_copyRv _ hpmemE pE (by simp [opLocals, placeLocals])
                                obtain ⟨dp, hdp, hptp⟩ : ∃ dp, body.localDecls[pE]? = some dp ∧
                                    ptrPointeeOf dp.ty = some (srcMutbl, pointeeIt) := by
                                  cases hdp : body.localDecls[pE]? with
                                  | none => simp [hdp] at hsrc
                                  | some dp => exact ⟨dp, rfl, by simpa [hdp] using hsrc⟩
                                have hisPtrP : isPtrTy dp.ty = true := by simp [isPtrTy, hptp]
                                obtain ⟨slotp, hsp⟩ : ∃ slot, view[pE]? = some slot :=
                                  ⟨_, List.getElem?_eq_getElem (by
                                    rw [hlo.nlocals]; exact (List.getElem?_eq_some_iff.mp hdp).1)⟩
                                have hslotOk := hlo.slots pE dp slotp hdp hsp
                                have hk := moveKind_of_ptrRvalueOk hokP hnraw hnref
                                have hmfP : MoveFrameOk s.frame.locals rv s.memory body.localDecls
                                    body.layouts :=
                                  moveFrameOk_of_ptrRvalueOk hokP hslotsA
                                    (fun be hbe p' d' hp' hpty hc => by
                                      obtain ⟨_, _, _, _, hk_addr, _⟩ := hbo.entries_ok be hbe
                                      subst hc
                                      obtain ⟨_, _, hd_k⟩ :=
                                        hbo.target_ptrs hfrag be.targetLocal hk_addr
                                      rw [(hd_k d' hp').1] at hpty
                                      cases hpty)
                                cases slotp with
                                | init v =>
                                  obtain ⟨pv, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtrP (.init v)).mp hslotOk
                                  obtain ⟨hMok', entry, relOff, hoff0, hlookup, htspec⟩ :=
                                    hMptr pv hsp
                                  obtain ⟨hdb_none, hrb_none, hsrc_p⟩ :=
                                    ptrCopySrcOf_of_ptrRvalueOk hokP hnraw hnref hpmemE hdp hisPtrP
                                  refine ⟨some (.ptr pv 8), hk, hmfP,
                                    fun v hv hlive => ?_, fun hv => (by cases hv),
                                    fun v hv => ?_, fun hv => (by cases hv), fun v locals' hv => ?_⟩
                                  · cases hv; exact hMok' hlive
                                  · cases hv
                                    refine (hAev s.frame.locals s.memory).1 pv hoff0
                                      (hpAgree.trans hsp) (fun hoff_src => ?_)
                                    have hoff_rv : ptrOffsetSrcOf rv = some pE := by
                                      cases rv <;> try (simp [ptrOffsetSrcOf, copyRv] at hoff_src)
                                      rename_i bop l r
                                      cases l <;> cases r <;>
                                        simp [ptrOffsetSrcOf, copyRv, copyOp] at hoff_src ⊢
                                      all_goals exact hoff_src
                                    have hsrc_none : ptrDerefReadSrc rv = none := by
                                      unfold ptrDerefReadSrc
                                      split
                                      · rename_i p' rest' hcrv'
                                        exact False.elim (hnder p' rest' hcrv')
                                      · rfl
                                    have hndis_env :
                                        (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD pE
                                          .disabled ≠ .disabled := by
                                      have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
                                      simpa [ptrStmtOk, hsrc_none, hrb_none, hoff_rv, bne_iff_ne]
                                        using hpst
                                    have hndis_e : entry.perm ≠ .disabled :=
                                      (hbo.usable_of_not_disabled hndis_env hdp hptp hsp hlookup).1
                                    have he_mem := (lookupBorrow_mem_and_tag hlookup).1
                                    obtain ⟨_, _, _, _, hk_addr, _⟩ := hbo.entries_ok entry he_mem
                                    obtain ⟨_, _, _, _, hrlen⟩ := hbo.perm_eq he_mem
                                    have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                                    obtain ⟨targetRootVal, ht_view⟩ :=
                                      hbo.target_init hfrag entry.targetLocal hk_addr
                                    have ht_init : s.frame.locals[entry.targetLocal]? =
                                        some (.init targetRootVal) := hkAgree.trans ht_view
                                    exact ⟨entry, relOff, hlookup, hndis_e, htspec,
                                      ⟨.init targetRootVal, ht_init, by simp⟩,
                                      (ptrAllocByteBound?_spec hdlo hdeclsOk hslotsA hlookup hrlen
                                        (hbo.entries_place entry he_mem) htspec ht_init).1⟩
                                  · cases hv
                                    have hisPtrD : isPtrTy d.ty = true := by simp [isPtrTy, hpt]
                                    exact hbo.ptrCopy hlo.nlocals hbb hst hdi hisPtrD hdp hisPtrP
                                      hmut_ip rfl hdb_none hrb_none hsrc_p pv hsp hdst_addr
                                      (fun dp' mutbl' pointeeIt' hdp' hpt' => by
                                        rw [hdi] at hdp'; cases hdp'; rw [hpt] at hpt'; cases hpt'
                                        exact ⟨entry, relOff, hoff0, hlookup, htspec⟩)
                                | uninit =>
                                  refine ⟨none, hk, hmfP, fun v hv => (by cases hv),
                                    fun _ hlive => hMub (.inl hsp) hlive, fun v hv => (by cases hv),
                                    fun _ => (hAev s.frame.locals s.memory).2 (.inl (hpAgree.trans hsp)),
                                    fun v _ hv => (by cases hv)⟩
                                | dead =>
                                  refine ⟨none, hk, hmfP, fun v hv => (by cases hv),
                                    fun _ hlive => hMub (.inr hsp) hlive, fun v hv => (by cases hv),
                                    fun _ => (hAev s.frame.locals s.memory).2 (.inr (hpAgree.trans hsp)),
                                    fun v _ hv => (by cases hv)⟩
                            | some p =>
                              obtain ⟨fields, size, align⟩ := p
                              have hnp : isPtrTy d.ty = false := isPtrTy_false_of_tupleTypeOf ht
                              simp only [hdi, hb, ho, htup, hit, ha, ht] at hok
                              obtain ⟨hcrv, _⟩ := tupleRvalueOk_noMove hok
                              have htp : tuplePlaceSpec body.layouts body.localDecls ⟨i, []⟩ =
                                  some (fields, size, align) := by
                                simp only [tuplePlaceSpec, hi_decl, ↓reduceIte, hdi, Option.bind_eq_bind,
                                  Option.bind_some, ht]
                              have hpmir : placeMirTy body.localDecls ⟨i, []⟩ = some d.ty := by
                                simp [placeMirTy, hdi, resolveProjTy]
                              rw [hpmir, hcrv] at he
                              obtain ⟨sloti, hsi⟩ : ∃ slot, view[i]? = some slot :=
                                ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hi_decl)⟩
                              obtain ⟨⟨rootVal, rfl⟩, _⟩ :=
                                hns i d sloti hdi hsi (scalarTypeOf_none_of_tupleTypeOf ht) hnp
                              have hpe' : translatePlace body.localDecls ⟨i, []⟩ =
                                  some (.Local (localName i)) := rfl
                              obtain ⟨hM1, hM2⟩ := evalStatement_assign_tuple hframe ⟨i, []⟩ d.ty fields
                                size align htp (.Local (localName i)) hpe' rv hok e he rootVal hsi
                              have hfr : tupleRvVal s.frame.locals fields rv =
                                  tupleRvVal view fields rv := tupleRvVal_frame fields rv hagree
                              obtain ⟨hA1, hA2⟩ := evalRvalue_tuple_frag body.localDecls s.frame.locals
                                hslotsA hnA d.ty fields size align rv hok s.memory
                              refine ⟨tupleRvVal view fields rv,
                                moveKind_of_tupleRvalueOk hok,
                                moveFrameOk_of_tupleRvalueOk hok s.frame.locals s.memory,
                                ?_, ?_, ?_, ?_,
                                fun v l _ => hBset0 d hdi hnp _ l⟩
                              · intro newVal hnv _
                                obtain ⟨newRootVal, m3, hwpath, _, hm3, h3⟩ := hM1 newVal hnv
                                simp only [writeFieldPath, Option.some.injEq] at hwpath
                                subst hwpath
                                exact ⟨m3, hm3, h3⟩
                              · intro hnv _
                                exact hM2 hnv
                              · intro newVal hnv
                                rw [hcrv]
                                exact hA1 newVal (hfr.trans hnv)
                              · intro hnv
                                rw [hcrv]
                                exact hA2 (hfr.trans hnv)
                obtain ⟨hA1, hA2⟩ := evalStmt_assign_move s body.localDecls body.layouts i rv span hk hr0
                  hi hbor_i hrel.protectors hmf
                by_cases hdead : s.frame.locals[i]? = some .dead
                · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                  obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
                  have hA : evalStmt s ⟨.assign ⟨i, []⟩ rv, span⟩ body.localDecls body.layouts =
                      MirStepNode.fail .ub := by
                    cases hres : res with
                    | none => exact hA2 (hAnone hres)
                    | some v => exact (hA1 v (hAok v hres)).2 hdead
                  rw [hA]
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
                  cases hres : res with
                  | none =>
                    rw [hA2 (hAnone hres)]
                    obtain ⟨msg, hmsg⟩ := hMnone hres hlive
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  | some v =>
                    rw [(hA1 v (hAok v hres)).1 hdead]
                    obtain ⟨m3, hm3, h3⟩ := hMok v hres hlive
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    refine StepRelN.tau' m4
                      (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                    exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init v)) _ lm m4 h4.threads
                      h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar
                      (hrel.stale.assign hbb hst rfl (.init v))
                      (retLive_set hrel.retLive i (by simp)) (hBok v _ hres) rfl rfl rfl rfl
      | cons proj rest =>
        obtain ⟨kind, span⟩ := st
        simp only at hkind
        subst hkind
        suffices hmain : ¬(proj = .deref ∧ rest = [] ∧ (ptrDerefReadSrc rv).isSome = true) → _ by
          by_cases hderefRead : proj = .deref ∧ rest = [] ∧ (ptrDerefReadSrc rv).isSome = true
          · ---------------------------------------------------- `(*_i) = copy (*_r)` / `move (*_r)`
            obtain ⟨rfl, rfl, hsrcSome⟩ := hderefRead
            obtain ⟨r, hsrc⟩ := Option.isSome_iff_exists.mp hsrcSome
            obtain ⟨_, _, hcrv, di, dr, pointeeIt, srcMutbl, hdi, hptI, hdr, hptR⟩ :=
              statementOk_derefWrite_derefRead hsrc hok
            have hreadsD : r ∉ movedBefore body s.frame.blockIdx s.frame.stmtIdx ∧
                i ∉ movedBefore body s.frame.blockIdx s.frame.stmtIdx := by
              have h' := hreads
              rw [stmtReadsOk_derefWrite_derefRead hsrc] at h'
              simpa [Bool.and_eq_true, List.contains_iff_mem] using h'
            have hrAgree : s.frame.locals[r]? = view[r]? := hrel.stale.agree hreadsD.1
            have hiAgree : s.frame.locals[i]? = view[i]? := hrel.stale.agree hreadsD.2
            rw [translatePlace_deref hdi hptI, Option.some.injEq] at hpe
            subst hpe
            rw [hcrv] at he
            have he' := translateRvalue_derefRead hdr hptR he
            subst he'
            have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
            simp only [ptrStmtOk, hsrc, Bool.and_eq_true, bne_iff_ne] at hpst
            obtain ⟨hndisI_env, hndisR_env, hkeeps_env⟩ := hpst
            have hgoodP : GoodSize pointeeIt.size.bytes := ptrPointeeOf_good hptI
            let memFrz : MirSemantics.Memory :=
              { s.memory with
                borrows := MirSemantics.freezeDerefReadBorrowsAt s.frame.locals r []
                  s.memory.borrows }
            obtain ⟨hAok, hAwub, hAub⟩ := evalStmt_assign_derefWrite_mem s body.localDecls
              body.layouts i rv span
            rcases evalPlace_deref hframe hbo hns hfrag i di .mut pointeeIt hdi hptI with
              ⟨ptrValI, entryI, relOffI, m1, hvpI, hoff0I, hlookupI, hk_addrI, htspecI, hderefI,
                h1, _⟩ |
              ⟨hnotI, msgI, hmsgI⟩
            · rcases evalPlace_deref h1 hbo hns hfrag r dr srcMutbl pointeeIt hdr hptR with
                ⟨ptrValR, entryR, relOffR, m2, hvpR, hoff0R, hlookupR, hk_addrR, htspecR, hderefR,
                  h2, htgtR⟩ |
                ⟨hnotR, msgR, hmsgR⟩
              · have hndisR : entryR.perm ≠ .disabled :=
                  (hbo.usable_of_not_disabled hndisR_env hdr hptR hvpR hlookupR).1
                have hpIA : s.frame.locals[i]? = some (.init (.ptr ptrValI 8)) :=
                  hiAgree.trans hvpI
                have hpRA : s.frame.locals[r]? = some (.init (.ptr ptrValR 8)) :=
                  hrAgree.trans hvpR
                obtain ⟨entryI', hlookupI_frz, hactI_frz, hlocI_frz, hprojI_frz, hroffI_frz,
                    hrlenI_frz, hBdw⟩ :=
                  hbo.derefWriteRead hbb hst rfl hsrc hdi hptI hdr
                    (by simp [isPtrTy, hptR]) ptrValI ptrValR entryI entryR
                    hvpI hpIA hlookupI hvpR hpRA hlookupR hndisI_env hkeeps_env
                have hkAgreeI := hrel.stale.addrTaken_eq hpa hk_addrI
                have hkAgreeR := hrel.stale.addrTaken_eq hpa hk_addrR
                obtain ⟨_, _, hd_kI⟩ := hbo.target_ptrs hfrag entryI.targetLocal hk_addrI
                obtain ⟨_, _, _, _, _, _, htgtI_m2⟩ := evalTargetPlace h2 hbo hns hfrag
                  ⟨entryI.targetLocal, entryI.targetProjection⟩ pointeeIt relOffI htspecI hk_addrI
                obtain ⟨hniR, _, _⟩ := evalTargetPlace h2 hbo hns hfrag
                  ⟨entryR.targetLocal, entryR.targetProjection⟩ pointeeIt relOffR htspecR hk_addrR
                have he_memR := (lookupBorrow_mem_and_tag hlookupR).1
                obtain ⟨targetRootValR, ht_viewR⟩ :=
                  hbo.target_init hfrag entryR.targetLocal hk_addrR
                have ht_initR : s.frame.locals[entryR.targetLocal]? =
                    some (.init targetRootValR) := hkAgreeR.trans ht_viewR
                obtain ⟨hEqOkR, hEqUbR⟩ := evalRvalue_derefRead_eq s.frame.locals hcrv s.memory
                  body.localDecls body.layouts hdr hptR entryR
                  (evalOperand_deref_eq_target_typed hdlo hdeclsOk hslotsA s.memory hdr hptR hpRA
                    hoff0R hlookupR hndisR (hbo.entries_place entryR he_memR) htspecR ht_initR)
                have hagqR : ReadsAgree s.frame.locals view
                    [.copy ⟨entryR.targetLocal, entryR.targetProjection⟩] :=
                  readsAgree_copy_target hniR hkAgreeR
                have hopokI := ptrTargetSpec_operandOk hdeclsOk htspecI
                obtain ⟨dstTargetPe, htpeI⟩ : ∃ pe, translatePlace body.localDecls
                    ⟨entryI.targetLocal, entryI.targetProjection⟩ = some pe := by
                  simp only [operandOk, Bool.and_eq_true, translateOperand,
                    Option.isSome_map] at hopokI
                  exact Option.isSome_iff_exists.mp hopokI.2
                have hopokR := ptrTargetSpec_operandOk hdeclsOk htspecR
                obtain ⟨srcTargetPe, htpeR⟩ : ∃ pe, translatePlace body.localDecls
                    ⟨entryR.targetLocal, entryR.targetProjection⟩ = some pe := by
                  simp only [operandOk, Bool.and_eq_true, translateOperand,
                    Option.isSome_map] at hopokR
                  exact Option.isSome_iff_exists.mp hopokR.2
                have heqR : translateRvalue body.layouts body.localDecls none
                    (.use (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩)) =
                      some (.Load srcTargetPe) := by
                  simp [translateRvalue, translateOperand, htpeR]
                obtain ⟨hopR1, hopR2⟩ := evalOperand_frag body.localDecls s.frame.locals hslotsA
                  hnA pointeeIt (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩) hopokR
                  s.memory.borrows s.memory.globals s.memory.callerLocals
                obtain ⟨hAR1, hAR2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA
                  pointeeIt hgoodP (.use (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩))
                  hopokR (hns.opsInit_of_readsAgree hagqR) s.memory
                obtain ⟨res, hRok, hRnone⟩ := derefWrite_target h2 hbo hfrag hslotsA hnA
                  ⟨entryI.targetLocal, entryI.targetProjection⟩ pointeeIt relOffI htspecI hk_addrI
                  hkAgreeI (.use (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩)) hopokR hagqR
                  (.Load srcTargetPe) heqR dstTargetPe htpeI
                have hMeq := evalStatement_assign_deref_load_eq hderefI hderefR
                  (htgtI_m2 dstTargetPe htpeI) (htgtR srcTargetPe htpeR)
                cases hres : res with
                | none =>
                  obtain ⟨⟨msg, hmsg⟩, hAu⟩ := hRnone hres
                  have hAu' : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
                      .ub := by
                    cases hbR : opBits s.frame.locals
                        (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩) with
                    | none => exact hEqUbR (hopR2 hbR)
                    | some bits =>
                      rw [hAR1 bits (by simpa [rvBits] using hbR)] at hAu
                      cases hAu
                  rw [hAub hAu']
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hMeq, hmsg])
                | some w =>
                  obtain ⟨⟨m3, hm3, h3⟩, v, hv, hwshape⟩ := hRok w hres
                  obtain ⟨wSc, rfl, hw_sz, hv'⟩ :
                      ∃ wSc : ScalarInt, v = .scalar wSc ∧ wSc.sizeBytes = pointeeIt.size.bytes ∧
                        evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
                          .ok (.scalar wSc) s.frame.locals memFrz := by
                    cases hbR : opBits s.frame.locals
                        (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩) with
                    | none =>
                      rw [hAR2 (by simpa [rvBits] using hbR)] at hv
                      cases hv
                    | some bits =>
                      rw [hAR1 bits (by simpa [rvBits] using hbR)] at hv
                      injection hv with hv_eq
                      exact ⟨⟨bits, pointeeIt.size.bytes⟩, hv_eq.symm, rfl,
                        hEqOkR _ (hopR1 bits hbR)⟩
                  have htspecI' : ptrTargetSpec body.layouts body.localDecls
                      ⟨entryI'.targetLocal, entryI'.targetProjection⟩ =
                      some (pointeeIt, relOffI) := by
                    rwa [hlocI_frz, hprojI_frz]
                  have hqI' : ⟨entryI'.targetLocal, entryI'.targetProjection⟩ ∈
                      bodyDirectBorrowPlaces body := by
                    rw [hlocI_frz, hprojI_frz]
                    exact hbo.entries_place entryI (lookupBorrow_mem_and_tag hlookupI).1
                  obtain ⟨targetRootValI, ht_viewI⟩ :=
                    hbo.target_init hfrag entryI.targetLocal hk_addrI
                  have ht_initI' : s.frame.locals[entryI'.targetLocal]? =
                      some (.init targetRootValI) := by
                    rw [hlocI_frz]; exact hkAgreeI.trans ht_viewI
                  have hw : writePlaceValue s.frame.locals memFrz.borrows ⟨i, [.deref]⟩ (.scalar wSc)
                      body.localDecls body.layouts =
                      .ok (s.frame.locals.set entryI.targetLocal (.init w)) := by
                    rw [← hlocI_frz]
                    refine writePlaceValue_deref_of_ptrTargetSpec hdlo hdeclsOk hslotsA
                      memFrz.borrows hdi hptI hpIA hoff0I hlookupI_frz hactI_frz hqI' htspecI'
                      ht_initI' hw_sz ?_
                    rcases hwshape with ⟨hproj, rfl⟩ | ⟨ph, pt, rootVal, hproj, hroot, hwp⟩
                    · exact .inl ⟨hprojI_frz.trans hproj, rfl⟩
                    · exact .inr ⟨ph, pt, rootVal, hprojI_frz.trans hproj,
                        by rwa [hlocI_frz], hwp s.frame.locals⟩
                  rw [hAok (.scalar wSc) memFrz _ hv' hrel.protectors hrel.callerLocals hw]
                  obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                  refine StepRelN.tau' m4
                    (by simp [hne, listIndex_nat _ _ _ htst, hMeq, hm3, hm4, check_after h4]) ?_
                  exact hrel.advanceN hfrag hbb hlt _ (view.set entryI.targetLocal (.init w)) _ lm
                    m4 h4.threads h4.active
                    (by
                      rw [h4.allocs,
                        ctxWithBorrows_invalidateDerefWriteBorrows body ctx s.frame.locals
                          memFrz.borrows i ptrValI entryI' hpIA hlookupI_frz hrlenI_frz hroffI_frz
                          (resolveDerefWriteFullProj_of_ptrTargetSpec s.frame.locals
                            s.frame.locals ptrValI 8 entryI' [] htspecI' hoff0I),
                        ctxWithBorrows_freezeDerefReadBorrowsAt_eq body ctx hpRA hlookupR]
                      exact h3.locs)
                    h3.nonScalar
                    (hrel.stale.setBothKeep hbb hst
                      (by rcases copyRv_derefRead hcrv with h | h | h <;>
                        simp [h, stmtMoved, rvOperands, moveOut, opMoved]) (.init w))
                    (retLive_set hrel.retLive _ (by simp))
                    (hBdw _ (.init w) ⟨w, rfl⟩
                      (fun dp' pv hdp' hpty => absurd hpty (by rw [(hd_kI dp' hdp').1]; simp)))
                    rfl rfl rfl rfl
              · rw [hAub (evalRvalue_derefRead_ub s.frame.locals hcrv s.memory body.localDecls
                  body.layouts (by rw [hrAgree]; exact hnotR))]
                exact StepRelN.ub' msgR (by
                  simp [hne, listIndex_nat _ _ _ htst,
                    evalStatement_assign_deref_load_ub hderefI hmsgR])
            · have hnotIA :
                  s.frame.locals[i]? = some .uninit ∨ s.frame.locals[i]? = some .dead := by
                rw [hiAgree]; exact hnotI
              have hA : evalStmt s ⟨.assign ⟨i, [.deref]⟩ rv, span⟩ body.localDecls body.layouts =
                  MirStepNode.fail .ub := by
                rcases evalPlace_deref hframe hbo hns hfrag r dr srcMutbl pointeeIt hdr hptR with
                  ⟨ptrValR, entryR, relOffR, _, hvpR, hoff0R, hlookupR, hk_addrR, htspecR, _, _,
                    _⟩ |
                  ⟨hnotR, _, _⟩
                · have hndisR : entryR.perm ≠ .disabled :=
                    (hbo.usable_of_not_disabled hndisR_env hdr hptR hvpR hlookupR).1
                  have he_memR := (lookupBorrow_mem_and_tag hlookupR).1
                  have hkAgreeR := hrel.stale.addrTaken_eq hpa hk_addrR
                  obtain ⟨targetRootValR, ht_viewR⟩ :=
                    hbo.target_init hfrag entryR.targetLocal hk_addrR
                  have ht_initR : s.frame.locals[entryR.targetLocal]? =
                      some (.init targetRootValR) := hkAgreeR.trans ht_viewR
                  obtain ⟨hEqOkR, hEqUbR⟩ := evalRvalue_derefRead_eq s.frame.locals hcrv s.memory
                    body.localDecls body.layouts hdr hptR entryR
                    (evalOperand_deref_eq_target_typed hdlo hdeclsOk hslotsA s.memory hdr hptR
                      (hrAgree.trans hvpR) hoff0R hlookupR hndisR
                      (hbo.entries_place entryR he_memR) htspecR ht_initR)
                  have hopokR := ptrTargetSpec_operandOk hdeclsOk htspecR
                  obtain ⟨hopR1, hopR2⟩ := evalOperand_frag body.localDecls s.frame.locals hslotsA
                    hnA pointeeIt (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩) hopokR
                    s.memory.borrows s.memory.globals s.memory.callerLocals
                  cases hbR : opBits s.frame.locals
                      (.copy ⟨entryR.targetLocal, entryR.targetProjection⟩) with
                  | none => exact hAub (hEqUbR (hopR2 hbR))
                  | some bits =>
                    exact hAwub _ memFrz (hEqOkR _ (hopR1 bits hbR)) hrel.protectors
                      hrel.callerLocals
                      (writePlaceValue_deref_not_init s.frame.locals memFrz.borrows i _ hnotIA
                        body.localDecls body.layouts)
                · exact hAub (evalRvalue_derefRead_ub s.frame.locals hcrv s.memory body.localDecls
                    body.layouts (by rw [hrAgree]; exact hnotR))
              rw [hA]
              exact StepRelN.ub' msgI (by
                simp [hne, listIndex_nat _ _ _ htst, evalStatement_assign_place_ub hmsgI])
          · exact hmain hderefRead
        intro hderefRead
        have hreads' : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) (rvOperands rv) =
            true ∧
            ∀ j ∈ placeLocals ⟨i, proj :: rest⟩,
              j ∉ (rvOperands rv).foldl moveOut
                (movedBefore body s.frame.blockIdx s.frame.stmtIdx) := by
          have h' := hreads
          rw [stmtReadsOk_derefWrite_of_not_derefRead hderefRead] at h'
          simpa [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] using h'
        have hreadsMo := hreads'.1
        have hagree := hrel.stale.readsAgree hreadsMo
        have hplAgree : ∀ j ∈ placeLocals ⟨i, proj :: rest⟩, s.frame.locals[j]? = view[j]? :=
          fun j hj => hrel.stale.agree fun hmo =>
            hreads'.2 j hj ((foldl_moveOut_mem _ _ j).mpr (.inl hmo))
        have hiAgree : s.frame.locals[i]? = view[i]? :=
          hplAgree i (local_mem_placeLocals ⟨i, proj :: rest⟩)
        by_cases hfield : ∃ idx fieldTy, proj = .field idx fieldTy
        · -------------------------------------------------------- assign field `_i.f1...fk = rv`
          obtain ⟨idx, fieldTy, rfl⟩ := hfield
          simp only [statementOk, Bool.and_eq_true] at hok
          obtain ⟨htupSome, hok⟩ := hok
          cases hpit : placeIntType body.layouts body.localDecls ⟨i, .field idx fieldTy :: rest⟩ with
          | some it =>
            simp only [hpit, Bool.and_eq_true] at hok
            obtain ⟨hpok, hrvok⟩ := hok
            obtain ⟨hcrv, hnoMv⟩ := rvalueOk_noMove hrvok
            rw [hcrv] at he
            have hpok' := hpok
            simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at hpok'
            obtain ⟨hi, hpok'⟩ := hpok'
            cases hdi : body.localDecls[i]? with
            | none => simp [hdi] at hpok'
            | some d =>
              cases ht : tupleTypeOf body.layouts d.ty with
              | none => simp [hdi, ht] at htupSome
              | some rpair =>
                obtain ⟨rootFields, rootSize, rootAlign⟩ := rpair
                have hnp : isPtrTy d.ty = false := isPtrTy_false_of_tupleTypeOf ht
                have hnoibt : intBoolTupleOf d.ty = none := (not_scalar_of_tupleTypeOf ht).2.2.1
                simp only [hdi, hnoibt, ht] at hpok'
                cases hres : resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign)
                    (.field idx fieldTy :: rest) with
                | none => simp [hres] at hpok'
                | some lpair =>
                  obtain ⟨relOff, leafSpec⟩ := lpair
                  cases leafSpec with
                  | tuple _ _ _ => simp [hres] at hpok'
                  | scalar leafIt =>
                    simp only [hres, decide_eq_true_eq] at hpok'
                    subst hpok'
                    obtain ⟨sloti, hsi⟩ : ∃ slot, view[i]? = some slot :=
                      ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hi)⟩
                    obtain ⟨⟨rootVal, rfl⟩, _⟩ :=
                      hns i d sloti hdi hsi (scalarTypeOf_none_of_tupleTypeOf ht) hnp
                    have hsiA : s.frame.locals[i]? = some (.init rootVal) := hiAgree.trans hsi
                    have hsloti := (DeclSlotOk_of_tupleTypeOf ht (.init rootVal)).mp
                      (hlo.slots i d (.init rootVal) hdi hsi)
                    obtain ⟨hleafWf, _⟩ := resolveFieldPath_wf hsloti.1 hres
                    have hgood : GoodSize leafIt.size.bytes :=
                      (goodAlignBytes_iff leafIt.size.bytes).mp hleafWf
                    have hnsOps : OpsNonScalarInit body.localDecls s.frame.locals (rvOperands rv) :=
                      hns.opsInit_of_readsAgree hagree
                    obtain ⟨hMok, hMnone⟩ :=
                      evalStatement_assign_field_scalar hframe i idx fieldTy rest htupSome leafIt
                        hpok pe hpe rv hrvok e he rootVal hsi
                    obtain ⟨hAok, hAnone⟩ :=
                      evalStmt_assign_field_scalar s body.localDecls body.layouts i idx fieldTy rest
                        leafIt hgood rv span hslotsA hnA hi hrvok hnsOps rootVal hsiA
                        hbor_i hrel.protectors
                    have hfr : rvBits body.localDecls s.frame.locals leafIt body.layouts rv =
                        rvBits body.localDecls view leafIt body.layouts rv :=
                      rvBits_frame_raw hagree
                    cases hr : rvBits body.localDecls view leafIt body.layouts rv with
                    | none =>
                      rw [hAnone (hfr.trans hr)]
                      obtain ⟨msg, hmsg⟩ := hMnone hr
                      exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                    | some r =>
                      obtain ⟨newRootVal, m3, hwpath, hwsem, hm3, h3⟩ := hMok r hr
                      rw [hAok r newRootVal (hfr.trans hr) hwpath hwsem]
                      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                      refine StepRelN.tau' m4
                        (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                      exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init newRootVal)) _ lm m4
                        h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar
                        (hrel.stale.setBothKeep hbb hst
                          (by simp [stmtMoved, foldl_moveOut_of_noMove hnoMv]) (.init newRootVal))
                        (retLive_set hrel.retLive i (by simp)) (hBset (fun h => nomatch h) d hdi hnp _ _)
                        rfl rfl rfl rfl
          | none =>
            simp only [hpit] at hok
            cases htp : tuplePlaceSpec body.layouts body.localDecls ⟨i, .field idx fieldTy :: rest⟩ with
            | none => simp [htp] at hok
            | some tpair =>
              obtain ⟨fields, size, align⟩ := tpair
              cases hpmir : placeMirTy body.localDecls ⟨i, .field idx fieldTy :: rest⟩ with
              | none => simp [htp, hpmir] at hok
              | some dstTy =>
                simp only [htp, hpmir] at hok
                obtain ⟨hcrv, hnoMv⟩ := tupleRvalueOk_noMove hok
                rw [hpmir, hcrv] at he
                obtain ⟨d, rootFields, rootSize, rootAlign, _, hi, hdi, ht, _, _⟩ :=
                  tuplePlaceSpec_resolve htp
                have hnp : isPtrTy d.ty = false := isPtrTy_false_of_tupleTypeOf ht
                obtain ⟨sloti, hsi⟩ : ∃ slot, view[i]? = some slot :=
                  ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hi)⟩
                obtain ⟨⟨rootVal, rfl⟩, _⟩ :=
                  hns i d sloti hdi hsi (scalarTypeOf_none_of_tupleTypeOf ht) hnp
                have hsiA : s.frame.locals[i]? = some (.init rootVal) := hiAgree.trans hsi
                obtain ⟨hMok, hMnone⟩ :=
                  evalStatement_assign_tuple hframe ⟨i, .field idx fieldTy :: rest⟩ dstTy
                    fields size align htp pe hpe rv hok e he rootVal hsi
                obtain ⟨hAok, hAnone⟩ :=
                  evalStmt_assign_tuple s body.localDecls body.layouts
                    ⟨i, .field idx fieldTy :: rest⟩ dstTy fields size align htp rv span
                    hslotsA hnA hok rootVal hsiA hbor_i hrel.protectors
                have hfr : tupleRvVal s.frame.locals fields rv = tupleRvVal view fields rv :=
                  tupleRvVal_frame fields rv hagree
                cases hnv : tupleRvVal view fields rv with
                | none =>
                  rw [hAnone (hfr.trans hnv)]
                  obtain ⟨msg, hmsg⟩ := hMnone hnv
                  exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                | some newVal =>
                  obtain ⟨newRootVal, m3, hwpath, hwsem, hm3, h3⟩ := hMok newVal hnv
                  rw [hAok newVal newRootVal (hfr.trans hnv) hwpath hwsem]
                  obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                  refine StepRelN.tau' m4
                    (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                  exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init newRootVal)) _ lm m4
                    h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar
                    (hrel.stale.setBothKeep hbb hst
                      (by simp [stmtMoved, foldl_moveOut_of_noMove hnoMv]) (.init newRootVal))
                    (retLive_set hrel.retLive i (by simp)) (hBset (fun h => nomatch h) d hdi hnp _ _) rfl rfl rfl rfl
        · have hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy :=
            fun idx fieldTy h => hfield ⟨idx, fieldTy, h⟩
          cases rest with
          | cons p2 rest2 =>
            cases proj with
            | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
            | deref => simp [statementOk] at hok
            | _ => simp [translatePlace] at hpe
          | nil =>
            by_cases hderef : proj = .deref
            · ---------------------------------------------------- write through `(*_i) = rv`
              subst hderef
              have hsrcNone : ptrDerefReadSrc rv = none := by
                cases hs : ptrDerefReadSrc rv with
                | none => rfl
                | some r => exact False.elim (hderefRead ⟨rfl, rfl, by simp [hs]⟩)
              simp only [statementOk] at hok
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
              obtain ⟨hi_lt, hok⟩ := hok
              obtain ⟨dp, hdi⟩ : ∃ dp, body.localDecls[i]? = some dp :=
                ⟨_, List.getElem?_eq_getElem hi_lt⟩
              simp only [hdi] at hok
              cases hpt : ptrPointeeOf dp.ty with
              | none => simp [hpt] at hok
              | some pr =>
                obtain ⟨mutbl, pointeeIt⟩ := pr
                have hmut : mutbl = .mut := by
                  cases mutbl <;> first | rfl | simp [hpt] at hok
                subst hmut
                have hrvok : rvalueOk body.layouts body.localDecls pointeeIt (copyRv rv) = true := by
                  simpa [hpt, ptrDerefReadOk_false_of_src_none (decls := body.localDecls)
                    (it := pointeeIt) hsrcNone] using hok
                have hk : moveKind rv = true := moveKind_of_rvalueOk hrvok
                have hr0 : readsOk [] (rvOperands rv) = true :=
                  readsOk_mono (fun _ h => by simp at h) hreadsMo
                have hiL1 : (rvPost s.frame.locals rv)[i]? = s.frame.locals[i]? := by
                  rcases opsPost_get s.frame.locals (rvOperands rv) i with h' | ⟨hm, _, _⟩
                  · exact h'
                  · exact False.elim (hreads'.2 i (by simp [placeLocals])
                      ((foldl_moveOut_mem _ _ i).mpr (.inr hm)))
                rw [translatePlace_deref hdi hpt, Option.some.injEq] at hpe
                subst hpe
                have hgoodP : GoodSize pointeeIt.size.bytes := ptrPointeeOf_good hpt
                have hnsOps : OpsNonScalarInit body.localDecls s.frame.locals
                    (rvOperands (copyRv rv)) :=
                  (hns.opsInit_of_readsAgree hagree).copy
                obtain ⟨hAok, hAwub, hAub⟩ := evalStmt_assign_derefWrite_move s body.localDecls
                  body.layouts i rv span hk hr0
                  (moveFrameOk_of_rvalueOk hrvok s.frame.locals s.memory)
                  hrel.protectors hrel.callerLocals
                rcases evalPlace_deref hframe hbo hns hfrag i dp .mut pointeeIt hdi hpt with
                  ⟨ptrVal, entry, relOff, m1, hvp, hoff0, hlookup, hk_addr, htspec, hderef, h1,
                    htgt⟩ |
                  ⟨hnot, msg, hmsg⟩
                · have hndis_env :
                      (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD i .disabled ≠
                        .disabled := by
                    have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
                    simpa [ptrStmtOk, hsrcNone, bne_iff_ne] using hpst
                  have hact' : entry.perm = .active ∨ entry.perm = .reserved :=
                    (hbo.usable_of_not_disabled hndis_env hdi hpt hvp hlookup).2 rfl
                  obtain ⟨_, _, _, hroff, hrlen⟩ := hbo.perm_eq (lookupBorrow_mem_and_tag hlookup).1
                  have hpA : s.frame.locals[i]? = some (.init (.ptr ptrVal 8)) := hiAgree.trans hvp
                  have hpL1 : (rvPost s.frame.locals rv)[i]? = some (.init (.ptr ptrVal 8)) :=
                    hiL1.trans hpA
                  have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                  have hkL1 : (rvPost s.frame.locals rv)[entry.targetLocal]? =
                      s.frame.locals[entry.targetLocal]? := by
                    rcases opsPost_get s.frame.locals (rvOperands rv) entry.targetLocal with
                      h' | ⟨hm, _, _⟩
                    · exact h'
                    · exfalso
                      have hnat := movedBefore_not_addrTaken hpa s.frame.blockIdx
                        (s.frame.stmtIdx + 1) hk_addr
                      rw [movedBefore_succ hbb hst] at hnat
                      exact hnat (by
                        simpa [stmtMoved] using (foldl_moveOut_mem _ _ _).mpr (.inr hm))
                  obtain ⟨_, _, hd_k⟩ := hbo.target_ptrs hfrag entry.targetLocal hk_addr
                  have hopok := ptrTargetSpec_operandOk hdeclsOk htspec
                  obtain ⟨targetPe, htpe⟩ : ∃ pe, translatePlace body.localDecls
                      ⟨entry.targetLocal, entry.targetProjection⟩ = some pe := by
                    simp only [operandOk, Bool.and_eq_true, translateOperand,
                      Option.isSome_map] at hopok
                    exact Option.isSome_iff_exists.mp hopok.2
                  obtain ⟨res, hRok, hRnone⟩ := derefWrite_target h1 hbo hfrag hslotsA hnA _
                    pointeeIt relOff htspec hk_addr hkAgree (copyRv rv) hrvok hagree.of_copyRv e he
                    targetPe htpe
                  have hMeq := evalStatement_assign_place_eq e hderef (htgt targetPe htpe)
                  cases hres : res with
                  | none =>
                    obtain ⟨⟨msg, hmsg⟩, hAu⟩ := hRnone hres
                    rw [hAub hAu]
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hMeq, hmsg])
                  | some w =>
                    obtain ⟨⟨m3, hm3, h3⟩, v, hv, hwshape⟩ := hRok w hres
                    obtain ⟨hAR1, hAR2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA
                      pointeeIt hgoodP (copyRv rv) hrvok hnsOps s.memory
                    obtain ⟨wSc, rfl, hw_sz⟩ :
                        ∃ wSc : ScalarInt, v = .scalar wSc ∧ wSc.sizeBytes = pointeeIt.size.bytes := by
                      cases hr : rvBits body.localDecls s.frame.locals pointeeIt body.layouts
                          (copyRv rv) with
                      | none => rw [hAR2 hr] at hv; cases hv
                      | some bits =>
                        rw [hAR1 bits hr] at hv
                        injection hv with hv_eq
                        exact ⟨⟨bits, pointeeIt.size.bytes⟩, hv_eq.symm, rfl⟩
                    obtain ⟨targetRootVal, ht_view⟩ :=
                      hbo.target_init hfrag entry.targetLocal hk_addr
                    have ht_initL1 : (rvPost s.frame.locals rv)[entry.targetLocal]? =
                        some (.init targetRootVal) := hkL1.trans (hkAgree.trans ht_view)
                    have hw : writePlaceValue (rvPost s.frame.locals rv) s.memory.borrows
                        ⟨i, [.deref]⟩ (.scalar wSc) body.localDecls body.layouts =
                        .ok ((rvPost s.frame.locals rv).set entry.targetLocal (.init w)) := by
                      refine writePlaceValue_deref_of_ptrTargetSpec hdlo hdeclsOk
                        (rvPost_slots hslotsA rv) s.memory.borrows hdi hpt hpL1 hoff0 hlookup hact'
                        (hbo.entries_place entry (lookupBorrow_mem_and_tag hlookup).1)
                        htspec ht_initL1 hw_sz ?_
                      rcases hwshape with ⟨hproj, rfl⟩ | ⟨ph, pt, rootVal, hproj, hroot, hwp⟩
                      · exact .inl ⟨hproj, rfl⟩
                      · exact .inr ⟨ph, pt, rootVal, hproj, hkL1.trans hroot,
                          hwp (rvPost s.frame.locals rv)⟩
                    have hinvL1 := invalidateDerefWriteBorrows_congr_local
                      (rvPost s.frame.locals rv) s.frame.locals s.memory.borrows i ptrVal entry
                      htspec hoff0 hpL1 hpA hlookup hrlen hroff
                    rw [hAok (.scalar wSc) _ hv hw, hinvL1]
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    refine StepRelN.tau' m4
                      (by simp [hne, listIndex_nat _ _ _ htst, hMeq, hm3, hm4, check_after h4]) ?_
                    exact hrel.advanceN hfrag hbb hlt _ (view.set entry.targetLocal (.init w)) _ lm m4
                      h4.threads h4.active
                      (by
                        rw [h4.allocs,
                          ctxWithBorrows_invalidateDerefWriteBorrows body ctx s.frame.locals
                            s.memory.borrows i ptrVal entry hpA hlookup hrlen hroff
                            (resolveDerefWriteFullProj_of_ptrTargetSpec s.frame.locals
                              s.frame.locals ptrVal 8 entry [] htspec hoff0)]
                        exact h3.locs)
                      h3.nonScalar
                      (hrel.stale.assignDeref hbb hst rfl entry.targetLocal (.init w))
                      (retLive_set hrel.retLive _ (by simp))
                      (hbo.derefWrite hbb hst rfl hsrcNone hdi (by simp [isPtrTy, hpt]) ptrVal
                        entry hvp hpA hlookup (.init w) ⟨w, rfl⟩
                        (fun dp' pv hdp' hpty => absurd hpty (by rw [(hd_k dp' hdp').1]; simp)))
                      rfl rfl rfl rfl
                · ---------------------------------------- through an uninitialized pointer: UB
                  have hnotL1 : (rvPost s.frame.locals rv)[i]? = some .uninit ∨
                      (rvPost s.frame.locals rv)[i]? = some .dead := by
                    rw [hiL1, hiAgree]; exact hnot
                  obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA
                    pointeeIt hgoodP (copyRv rv) hrvok hnsOps s.memory
                  have hA : evalStmt s ⟨.assign ⟨i, [.deref]⟩ rv, span⟩ body.localDecls body.layouts =
                      MirStepNode.fail .ub := by
                    cases hr : rvBits body.localDecls s.frame.locals pointeeIt body.layouts
                        (copyRv rv) with
                    | none => exact hAub (hA2 hr)
                    | some r =>
                      exact hAwub _ (hA1 r hr)
                        (writePlaceValue_deref_not_init (rvPost s.frame.locals rv) s.memory.borrows
                          i _ hnotL1 body.localDecls body.layouts)
                  rw [hA]
                  exact StepRelN.ub' msg (by
                    simp [hne, listIndex_nat _ _ _ htst, evalStatement_assign_place_ub (e := e) hmsg])
            · ---------------------------------------------------- assign indexed element `_i[proj] = rv`
              rw [statementOk_assign_single_nonfield hnf hderef] at hok
              cases hdi : body.localDecls[i]? with
              | none => simp [hdi] at hok
              | some d =>
                simp only [hdi, Option.bind_eq_bind, Option.bind_some] at hok
                cases ha : arrayTypeOf d.ty with
                | none => simp [ha] at hok
                | some p =>
                  obtain ⟨elemIt, count⟩ := p
                  have hnp : isPtrTy d.ty = false := isPtrTy_false_of_arrayTypeOf ha
                  simp only [ha, Bool.and_eq_true] at hok
                  obtain ⟨hproj, hok'⟩ := hok
                  obtain ⟨hcrv, hnoMv⟩ := rvalueOk_noMove hok'
                  rw [hcrv] at he
                  have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
                  obtain ⟨sloti, hsi⟩ : ∃ slot, view[i]? = some slot :=
                    ⟨_, List.getElem?_eq_getElem (by rw [hlo.nlocals]; exact hi)⟩
                  obtain ⟨⟨v0, rfl⟩, _⟩ :=
                    hns i d sloti hdi hsi (scalarTypeOf_none_of_arrayTypeOf ha) hnp
                  have hsloti := (DeclSlotOk_of_arrayTypeOf ha (.init v0)).mp
                    (hlo.slots i d (.init v0) hdi hsi)
                  match v0, hsloti, hsi with
                  | .aggregate 0 elems, ⟨hlenE, _⟩, hsi =>
                    have hsiA : s.frame.locals[i]? = some (.init (.aggregate 0 elems)) :=
                      hiAgree.trans hsi
                    have hgood := arrayTypeOf_good ha
                    have hnsOps : OpsNonScalarInit body.localDecls s.frame.locals (rvOperands rv) :=
                      hns.opsInit_of_readsAgree hagree
                    obtain ⟨hMok, hMnone⟩ :=
                      evalStatement_assign_index hframe i d hdi elemIt count ha proj hproj pe hpe rv
                        hok' e he elems hsi
                    obtain ⟨hAok, hAnone⟩ :=
                      evalStmt_assign_index s body.localDecls body.layouts i proj rv span hslotsA
                        hnA d hdi elemIt count ha hgood hproj hok' hnsOps elems hsiA hlenE
                        hbor_i hrel.protectors
                    have hidxFr : projIdx s.frame.locals count proj = projIdx view count proj :=
                      projIdx_frame i count proj hplAgree
                    have hrvFr : rvBits body.localDecls s.frame.locals elemIt body.layouts rv =
                        rvBits body.localDecls view elemIt body.layouts rv :=
                      rvBits_frame_raw hagree
                    cases hidx : projIdx view count proj with
                    | none =>
                      rw [hAnone (.inl (hidxFr.trans hidx))]
                      obtain ⟨msg, hmsg⟩ := hMnone (.inl hidx)
                      exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                    | some idx =>
                      cases hr : rvBits body.localDecls view elemIt body.layouts rv with
                      | none =>
                        rw [hAnone (.inr (hrvFr.trans hr))]
                        obtain ⟨msg, hmsg⟩ := hMnone (.inr hr)
                        exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                      | some r =>
                        rw [hAok idx r (hidxFr.trans hidx) (hrvFr.trans hr)]
                        obtain ⟨m3, hm3, h3⟩ := hMok idx r hidx hr
                        obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                        refine StepRelN.tau' m4
                          (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                        exact hrel.advanceN hfrag hbb hlt _
                          (view.set i (.init (.aggregate 0
                            (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩))))) _ lm m4
                          h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar
                          (hrel.stale.setBothKeep hbb hst
                            (by simp [stmtMoved, foldl_moveOut_of_noMove hnoMv])
                            (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩)))))
                          (retLive_set hrel.retLive i (by simp)) (hBset (fun h => nomatch h) d hdi hnp _ _)
                          rfl rfl rfl rfl
    · ------------------------------------------------------------ placeMention
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      have hpOk : mentionPlaceOk body.layouts body.localDecls p = true := by
        simpa [statementOk] using hok
      have hal : p.local_ ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simpa [stmtLocals] using local_mem_placeLocals p)
      obtain ⟨hpl, hMlive, hMdead⟩ := evalStatement_placeMention_place hframe p hpOk pe hpe
      by_cases hdead : s.frame.locals[p.local_]? = some .dead
      · rw [evalStmt_placeMention_dead s body.localDecls body.layouts p span hdead]
        obtain ⟨msg, hmsg⟩ := hMdead ((hrel.stale.dead_iff _).mp hdead) hal
        exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
      · have hlive : view[p.local_]? ≠ some .dead :=
          fun h => hdead ((hrel.stale.dead_iff _).mpr h)
        rw [evalStmt_placeMention_place s body.localDecls body.layouts p span hslotsA hnA hpl hdead]
        have hM := hMlive hlive
        obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee hframe.shape
        refine StepRelN.tau' m4
          (by simp [hne, listIndex_nat _ _ _ htst, hM, hm4, check_after h4]) ?_
        exact hrel.advanceN hfrag hbb hlt _ view _ lm m4 h4.threads h4.active
          (by rw [h4.allocs]; exact hlo) hns (hrel.stale.keep hbb hst rfl) hrel.retLive
          (hbo.advance_keep hbb hst (by simp [ptrStmtStep])) rfl rfl rfl rfl
    · ------------------------------------------------------------ storageLive
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hin, hscSome⟩ := hok
      have hal : i ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      have hi_addr : i ∉ bodyAddrTakenLocals body := hpresSt.2.2.1 i rfl
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true := by
        simpa [hd, Bool.or_eq_true] using hscSome
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageLive s body.localDecls body.layouts i span hi
        (hbo.target_ne_of_not_addrTaken hi_addr)]
      obtain ⟨m3, lm3, hm3, h3, hlm3⟩ := evalStatement_storageLive hframe i d hd hal hscalar
        hrel.baseLow hn31
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
      refine StepRelN.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
      exact hrel.advanceN hfrag hbb hlt _ (view.set i .uninit) _ lm3 m4 h4.threads h4.active
        (by rw [h4.allocs]; exact h3.locs) h3.nonScalar (hrel.stale.setBoth hbb hst rfl .uninit)
        (retLive_set hrel.retLive i (by simp))
        (hbo.advance_storage hbb hst i .uninit (.inl rfl) hi_addr (fun _ _ _ _ => by simp)
          (fun k hk => hlm3 k (fun h => hi_addr (h ▸ hk))))
        rfl rfl rfl rfl
    · ------------------------------------------------------------ storageDead
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hin, hscSome⟩ := hok
      have hal : i ∉ alwaysStorageLiveLocals body :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      have hi_addr : i ∉ bodyAddrTakenLocals body := hpresSt.2.2.2 i rfl
      have hi0 : body.argCount < i := storageDeadOk_spec hsdOk hbbmem hstmem rfl
      obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true := by
        simpa [hd, Bool.or_eq_true] using hscSome
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageDead s body.localDecls body.layouts i span hi
        (hbo.target_ne_of_not_addrTaken hi_addr)]
      obtain ⟨m3, hm3, h3⟩ := evalStatement_storageDead hframe i d hd hal hscalar
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
      refine StepRelN.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
      exact hrel.advanceN hfrag hbb hlt _ (view.set i .dead) _ _ m4 h4.threads h4.active
        (by rw [h4.allocs]; exact h3.locs) h3.nonScalar (hrel.stale.setBoth hbb hst rfl .dead)
        (by rw [List.getElem?_set_ne (by omega)]; exact hrel.retLive)
        (hbo.advance_storage hbb hst i .dead (.inr (.inl rfl)) hi_addr (fun _ _ _ _ => by simp)
          (fun k hk => by
            have hki : localName k ≠ localName i := fun h =>
              hi_addr ((localName_inj k i).mp h ▸ hk)
            rw [mapGet_filter_key lm.entries (localName i) (localName k)]
            simp [hki]))
        rfl rfl rfl rfl
    · ------------------------------------------------------------ deinit
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      obtain ⟨i, proj⟩ := p
      cases proj with
      | cons _ _ => simp [statementOk] at hok
      | nil =>
        simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hin, hscSome⟩ := hok
        simp only [translatePlace, Option.some.injEq] at hpe
        subst hpe
        have hal : i ∉ alwaysStorageLiveLocals body :=
          mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals, placeLocals])
        have hi_addr : i ∉ bodyAddrTakenLocals body := hpresSt.2.1 ⟨i, []⟩ rfl
        obtain ⟨d, hd⟩ : ∃ d, body.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
        have hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true := by
          simpa [hd, Bool.or_eq_true] using hscSome
        have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
        obtain ⟨hMlive, hMdead⟩ := evalStatement_deinit hframe i d hd hscalar
        obtain ⟨hAlive, hAdead⟩ := evalStmt_deinit s body.localDecls body.layouts i span hi
        by_cases hdead : s.frame.locals[i]? = some .dead
        · rw [hAdead hdead]
          obtain ⟨msg, hmsg⟩ := hMdead ((hrel.stale.dead_iff i).mp hdead) hal
          exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
        · rw [hAlive hdead]
          obtain ⟨m3, hm3, h3⟩ := hMlive (fun h => hdead ((hrel.stale.dead_iff i).mpr h))
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
          refine StepRelN.tau' m4
            (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
          exact hrel.advanceN hfrag hbb hlt _ (view.set i .uninit) _ lm m4 h4.threads h4.active
            (by rw [h4.allocs]; exact h3.locs) h3.nonScalar (hrel.stale.setBoth hbb hst rfl .uninit)
            (retLive_set hrel.retLive i (by simp))
            (hbo.advance_storage hbb hst i .uninit (.inr (.inr rfl)) hi_addr
              (fun _ _ _ _ => by simp) (fun _ _ => rfl))
            rfl rfl rfl rfl
    · ------------------------------------------------------------ retag
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      obtain ⟨i, di, srcMutbl, srcIt, rfl, hnotFnEntry, hdi, hpt⟩ :=
        statementOk_retag_spec hok
      simp only [translatePlace, Option.some.injEq] at hpe
      subst hpe
      rw [hnotFnEntry] at htst
      have hiRead : i ∉ movedBefore body s.frame.blockIdx s.frame.stmtIdx := by
        simpa [stmtReadsOk, List.contains_iff_mem] using hreads
      have hiAgree : s.frame.locals[i]? = view[i]? := hrel.stale.agree hiRead
      obtain ⟨hAok, hAub⟩ := evalStmt_retag_local s body.localDecls body.layouts
        retagKind i span hnotFnEntry
      rcases evalStatement_validate_local_mr hframe hbo hns hfrag i di srcMutbl srcIt
          false hdi hpt with
        ⟨ptrVal, entry, m3, hvi, hlk, hm3, h3⟩ | ⟨hnot, msg, hmsg⟩
      · have hndis_env :
            (ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD i .disabled ≠
              .disabled := by
          have hpst := ptrStmtOk_of_ptrAliasingOk hpa hbb hst
          simpa [ptrStmtOk, bne_iff_ne] using hpst
        obtain ⟨hndis, hmut_act⟩ :=
          hbo.usable_of_not_disabled hndis_env hdi hpt hvi hlk
        rw [hAok ptrVal 8 entry (hiAgree.trans hvi) hlk hndis
          (retag_not_frozen_of_usable hdi hpt hmut_act)]
        obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
        refine StepRelN.tau' m4
          (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
        exact hrel.advanceN hfrag hbb hlt _ view _ lm m4 h4.threads h4.active
          (by rw [h4.allocs]; exact h3.locs) h3.nonScalar (hrel.stale.keep hbb hst rfl)
          hrel.retLive (hbo.advance_keep hbb hst (by simp [ptrStmtStep])) rfl rfl rfl rfl
      · have hnotA : s.frame.locals[i]? = some .uninit ∨ s.frame.locals[i]? = some .dead := by
          rw [hiAgree]; exact hnot
        rw [hAub hnotA]
        exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
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
      exact StepRelN.tau' m3 (by simp [htt, Interp.evalTerminator, hm3, check_after h3])
        (hrel.jumpN hfrag lm t ht _ h3.threads h3.active (by rw [h3.allocs]; exact hlo) hns
          (hstale_end.toBlock hsub) (hbo.jump hpa hbb hge t (by simp [termTargets, hk]) _))
    · -------------------------------------------------------------- switchInt
      obtain ⟨it, hit, hdok, hbr, hother⟩ := terminatorOk_switch hterm hk
      obtain ⟨⟨T, hT, hokT⟩, v, htt, hMok, hMnone⟩ := switch_spec hframe hk htermspec hit hdok
      have hreadsD : readsOk (movedBefore body s.frame.blockIdx bb.statements.length) [discr] =
          true := by
        simpa [termReadsOk, hk] using hmvT
      have hsimple : simpleOp discr = true := (readsOk_spec hreadsD discr (by simp)).1
      have hbitsEq : opBits s.frame.locals (copyOp discr) = opBits view (copyOp discr) :=
        opBits_frame _ (by
          rw [opLocals_copyOp]
          exact fun j hj => hstale_end.agree ((readsOk_spec hreadsD discr (by simp)).2 j hj))
      obtain ⟨hAok, hAnone⟩ := evalRelOperand_frag body.localDecls s.frame.locals hslotsA hnA
        (copyOp discr) hokT s.memory.borrows s.memory.globals s.memory.callerLocals
      have hdeq := evalOperand_decls_eq_nil_of_RelOperandOk body.localDecls s.frame.locals
        (copyOp discr) hokT s.memory.borrows s.memory.globals s.memory.callerLocals
      have hmove := evalOperand_move s.frame.locals discr hsimple s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals []
      cases hb : opBits view (copyOp discr) with
      | none =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk, hmove, hdeq, hAnone (hbitsEq.trans hb),
            opWithLocals]
        rw [hA]
        obtain ⟨msg, hmsg⟩ := hMnone hb
        exact StepRelN.ub' msg (by simp [htt, Interp.evalTerminator, hmsg])
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
          simp [MirSemantics.evalTerminator, hk, hmove, hdeq, hAok bits (hbitsEq.trans hb),
            opWithLocals, jumpState]
        rw [hA]
        have hM : evalTerminator (resetPick m) tb.terminator = .ok m4 := by
          rw [htt]
          simp only [Interp.evalTerminator, hm3, ok_bind]
          rw [hlookup]
          exact hm4
        exact StepRelN.emit' _ m4 rfl (by simp [hM, check_after h4])
          (hrel.jumpN hfrag lm _ htgt _ h4.threads h4.active (by rw [h4.allocs]; exact h3.locs)
            h3.nonScalar (hstale_end.toBlockMove discr hsub) (hbo.jump hpa hbb hge _ htgtMem _))
    · -------------------------------------------------------------- unreachable
      have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
        simp [MirSemantics.evalTerminator, hk]
      rw [hA]
      exact StepRelN.ub' "reached unreachable code" (by simp [htt, Interp.evalTerminator, ub])
    · -------------------------------------------------------------- return
      have hn0 : 0 < body.localDecls.length := by omega
      obtain ⟨d0, hd0⟩ : ∃ d, body.localDecls[0]? = some d := ⟨_, List.getElem?_eq_getElem hn0⟩
      have h0scalar : (scalarTypeOf d0.ty).isSome = true := by simpa [hd0] using hret0
      have hdScalar : scalarTypeOf d0.ty = some (tyOf d0 body.layouts) := by
        obtain ⟨T0, hT0⟩ := Option.isSome_iff_exists.mp h0scalar
        exact (tyOf_of_scalarTypeOf hT0) ▸ hT0
      obtain ⟨r0, a0, hp, hr0, hlive, haddrr, hlenr, halr⟩ := hrel.ret d0 hd0
      have hRet := evalReturn_frame hframe d0 hd0 h0scalar r0 a0 hp hr0 hlive haddrr hlenr halr
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
        exact StepRelN.ub' msg (by simp [htt, Interp.evalTerminator, hmsg])
      | .init v, hv0, hs0, hsA =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.retNormal v s.memory := by
          simp [MirSemantics.evalTerminator, hk, get?, hsA, hrel.callStack]
        rw [hA]
        obtain ⟨m', R, hm', hs', hR⟩ := hRet.1 v hs0
        have hv0' : SlotOk (tyOf d0 body.layouts) (.init v) :=
          (DeclSlotOk_of_scalarTypeOf hdScalar (.init v)).mp hv0
        exact StepRelN.ret' m' (by simp [htt, Interp.evalTerminator, hm', check_after hs'])
          ⟨r0, a0, d0, R, hd0, hv0', hp, hr0, hs'.threads, hs'.allocs, hR⟩

/-- **Correspondence theorem (one step).** For a fragment body `body`, its
`minimize`-style translation `f`, and related states (`StateRel`, when all
local declarations of `body` are scalar-family; see `step_correspondence_N` for
general `StateRelN` states with array, `TupleSpec`, or raw pointer locals), one
Anneal MIR step and one MiniRust `Machine::step` correspond in the sense of
`StepRel`. -/
theorem step_correspondence (body : CapturedMir) (f : Gen.Function) (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by decide) :
    StepRel body f ctx s (stepMirFn body s) (Interp.step m) :=
  (step_correspondence_N body f hfrag hf ctx s m (hrel.toStateRelN hall)).toStepRel

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

private theorem temp_isScalar {body : CapturedMir}
    (htemps : ∀ d ∈ body.localDecls.drop (body.argCount + 1),
      (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true)
    {i : Nat} {d : LocalDecl} (hi : body.argCount + 1 ≤ i) (hd : body.localDecls[i]? = some d) :
    (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true := by
  have hdrop : (body.localDecls.drop (body.argCount + 1))[i - (body.argCount + 1)]? = some d := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hi, hd]
  exact htemps d (List.mem_of_getElem? hdrop)

/-- Whether a `LocalSlot` holds an initialized value (`.init _`). -/
def slotIsInit : LocalSlot → Bool
  | .init _ => true
  | _ => false

/-- Decidable check that every non-scalar parameter slot (`i ≤ body.argCount`
with `scalarTypeOf d.ty = none`) in `locals` is initialized. Always `true` when
all parameter types are scalar or on `initMachineState body args`
(`initMachineState_nonScalar`). -/
def nonScalarSlotsInit (body : CapturedMir) (locals : List LocalSlot) : Bool :=
  (List.range (body.argCount + 1)).all fun i =>
    match body.localDecls[i]?, locals[i]? with
    | some d, some slot =>
      ((scalarTypeOf d.ty).isSome && !(bodyAddrTakenLocals body).contains i) || slotIsInit slot
    | _, _ => true

/-- At `f.start`, the locals map holds the return place and the arguments in
their initial allocations, and no temporary of the init block is allocated
yet. -/
theorem StartRel.localsOk {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {mInit : Mach} (hstart : StartRel body f ctx s mInit)
    (hargs : body.argCount + 1 ≤ body.localDecls.length)
    (hnp : ∀ (i : Nat) d, i < body.argCount + 1 → body.localDecls[i]? = some d →
      isPtrTy d.ty = false) :
    LocalsOkA body ctx [] s.frame.locals (localsMap ctx (body.argCount + 1))
      mInit.mem.memory.allocations := by
  have hmap : ∀ j, mapGet (localsMap ctx (body.argCount + 1)) (localName j) =
      if j < body.argCount + 1 then some (localPtr ctx j) else none := by
    intro j
    simp only [localsMap]
    exact mapGet_range_map _ _ _
  have hR := hstart.allocs
  have hn := hstart.nlocals
  have hLlen : (localAllocs ctx (body.localDecls.take (body.argCount + 1)) s.frame.locals
      body.layouts).length = body.argCount + 1 := by
    simp [localAllocs, localAllocsFrom_length, hn]; omega
  have hget : ∀ (i : Nat) d slot, i < body.argCount + 1 → body.localDecls[i]? = some d →
      s.frame.locals[i]? = some slot →
      mInit.mem.memory.allocations[ctx.base.length + i]? =
        some (stackAlloc (ctx.addrs.getD i 0) (itOf d body.layouts)
          (declSlotData d slot body.layouts)) := by
    intro i d slot hi hd hs
    rw [hR, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, localAllocs]
    rw [localAllocsFrom_getElem? ctx 0 _ _ i d slot
      (by rw [List.getElem?_take_of_lt hi]; exact hd) hs body.layouts]
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
      have haddr := hstart.addrs i d (by omega) hd
      refine ⟨ctx.base.length + i, rfl, by omega,
        haddr.1, Int.lt_trans haddr.2 (by decide), .inl haddr.2, ?_⟩
      simp only [hnp i d hi hd, Bool.false_eq_true, ↓reduceIte]
      exact hget i d slot hi hd hs
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

/-- Any MiniRust machine whose active thread stack has at least two frames
(`callerFrames ++ [fr]` with `callerFrames ≠ []`) cannot satisfy `ReturnRel`
(which requires a 1-frame stack `[{ c'.caller with ... }]`). -/
theorem Shape.not_returnRel_of_ne_nil {m : Mach} {rootCtx : Ctx}
    {callerFrames : List Frame} {fr : Frame} {allocs : List Gen.Allocation}
    (hsh : Shape m rootCtx (callerFrames ++ [fr]) allocs)
    (hne : callerFrames ≠ [])
    {b' : CapturedMir} {c' : Ctx} {s' : MachineState} {v : Value} :
    ¬ ReturnRel b' c' s' v m := by
  intro ⟨_, _, _, _, _, _, _, _, hthr, _, _⟩
  have h1 := hsh.threads
  rw [hthr] at h1
  have hlen := congrArg (fun ts => ts.map (·.stack.length)) h1
  simp [thread1] at hlen
  exact hne hlen

/-- No single-body `StateRel`-related MiniRust machine can satisfy `ReturnRel`:
a running `StateRel` machine has a 2-frame stack `[ctx.caller, calleeFrameL ...]`,
whereas `ReturnRel` requires a 1-frame stack after popping the callee. -/
theorem StateRel.not_returnRel {body b' : CapturedMir} {f : Gen.Function}
    {ctx c' : Ctx} {s s' : MachineState} {v : Value} {m : Mach}
    (hrel : StateRel body f ctx s m) :
    ¬ ReturnRel b' c' s' v m := by
  obtain ⟨view, hrel⟩ := hrel
  obtain ⟨lm, hthr, _⟩ := hrel.frame
  have hsh : Shape m ctx ([ctx.caller] ++ [calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx])
      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
  exact hsh.not_returnRel_of_ne_nil (by simp)

theorem StartRel.nonScalarLive {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {mInit : Mach}
    (hfrag : inFragment body = true)
    (hstart : StartRel body f ctx s mInit)
    (hnsInit : nonScalarSlotsInit body s.frame.locals = true) :
    NonScalarLive body s.frame.locals (localsMap ctx (body.argCount + 1)) := by
  obtain ⟨_, _, _, _, _, htemps, _, _, _, _⟩ := inFragment_spec body hfrag
  intro i d slot hd hs hnone hnp
  by_cases hi : i < body.argCount + 1
  · have hmem : i ∈ List.range (body.argCount + 1) := List.mem_range.mpr hi
    have hchk := (List.all_eq_true.mp hnsInit) i hmem
    simp only [hd, hs, hnone, Option.isSome_none, Bool.false_and, Bool.false_or] at hchk
    have hv : ∃ v, slot = .init v := by
      cases slot with
      | dead => simp [slotIsInit] at hchk
      | uninit => simp [slotIsInit] at hchk
      | init v => exact ⟨v, rfl⟩
    refine ⟨hv, fun p hp => ?_⟩
    have hmap : mapGet (localsMap ctx (body.argCount + 1)) (localName i) = some (localPtr ctx i) := by
      simp only [localsMap]
      rw [mapGet_range_map]
      simp [hi]
    rw [hmap] at hp
    cases hp
    exact (hstart.addrs i d (by omega) hd).2
  · rcases temp_isScalar htemps (by omega) hd with hsc | hp
    · simp [hnone] at hsc
    · simp [hnp] at hp

/-- Stepping the `minimize` entry block (`f.start = bbName body.basicBlocks.length`)
when `alwaysStorageLiveLocals body = []` jumps to `bb0` in one step while
preserving all allocations and locals. -/
theorem step_initBlock {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    {ctx : Ctx} {mInit : Mach} {allocs : List Gen.Allocation}
    {n : Nat}
    (hshape : Shape mInit ctx
      [ctx.caller, calleeFrame f ctx n body.basicBlocks.length 0] allocs)
    (hal : alwaysStorageLiveLocals body = [] := by decide) :
    ∃ m0, Interp.step mInit = .ok m0 ∧
      Shape m0 ctx [ctx.caller, calleeFrame f ctx n 0 0] allocs := by
  obtain ⟨_, hinit⟩ := translateFn_start body f hf
  obtain ⟨m0, hm0, h0⟩ := jumpToBlock_callee (resetPick_shape hshape) 0
  refine ⟨m0, ?_, h0⟩
  have hshL : Shape mInit ctx
      [ctx.caller, calleeFrameL f ctx (localsMap ctx n) body.basicBlocks.length 0] allocs := hshape
  rw [step_callee hshL (initBlock body) hinit]
  simp [initBlock, hal, Interp.evalTerminator, hm0, check_after h0]

/-- The init-block invariant of `step_start_N` after `k ≤
(alwaysStorageLiveLocals body).length` steps: the callee frame is at statement
`k` of `minimize`'s init block, the first `k` temporaries are allocated, and
`NonScalarLive` and the argument locals map are preserved. -/
private theorem step_start_key {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true) :
    ∀ k, k ≤ (alwaysStorageLiveLocals body).length → ∃ m lm,
    Interp.steps k mInit = .ok m ∧
    Shape m ctx [ctx.caller, calleeFrameL f ctx lm body.basicBlocks.length k]
      m.mem.memory.allocations ∧
    LocalsOkA body ctx ((alwaysStorageLiveLocals body).take k) s.frame.locals lm
      m.mem.memory.allocations ∧
    NonScalarLive body s.frame.locals lm ∧
    (∀ j, j < body.argCount + 1 → mapGet lm (localName j) = some (localPtr ctx j)) := by
  obtain ⟨_, hargs, hn31, _, hdeclsOk, htemps, _, _, _, _⟩ := inFragment_spec body hfrag
  obtain ⟨hfstart, hinit⟩ := translateFn_start body f hf
  have hAnd := alwaysStorageLiveLocals_nodup body
  have hlenS : (initBlock body).statements.length = (alwaysStorageLiveLocals body).length := by
    simp [initBlock]
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨mInit, localsMap ctx (body.argCount + 1), rfl, ⟨?_, hstart.active, rfl⟩,
      by simpa using hstart.localsOk hargs (inFragment_params_not_ptr body hfrag),
      hstart.nonScalarLive hfrag hns, fun j hj => mapGet_localsMap ctx _ j hj⟩
    rw [hstart.threads]
    simp [calleeFrame, calleeFrameL, hfstart]
  | succ k ih =>
    intro hk
    obtain ⟨m, lm, hm, hsh, hlo, hnsL, hlmP⟩ := ih (by omega)
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
    have hscalar : (scalarTypeOf d.ty).isSome = true ∨ isPtrTy d.ty = true :=
      temp_isScalar htemps hlo1 hd
    have hsa : s.frame.locals[a]? = some .dead := hstart.tempsDead a (by omega) hlo2
    have hpa : mapGet lm (localName a) = none := by
      cases hp : mapGet lm (localName a) with
      | none => rfl
      | some p =>
        have := (hlo.live a .dead hsa).mp (by simp [hp])
        simp [hnot] at this
    obtain ⟨m3, lm3, hm3, hsh3, hlo3, hns3, hlm3⟩ :=
      evalStatement_storageLive_init (FnLocalsSpec.of_translateFn hf)
      (resetPick_shape hsh) hlo hdeclsOk hnsL a d hd hscalar hsa hpa hstart.baseLow hn31
    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee hsh3
    have hne : ((k : Nat) : Int) ≠ ((initBlock body).statements.length : Int) := by
      rw [hlenS]; omega
    have hstep : Interp.step m = .ok m4 := by
      rw [step_callee hsh (initBlock body) hinit]
      simp [hne, listIndex_nat _ _ _ hst, hm3, hm4, check_after h4]
    refine ⟨m4, lm3, ?_, ⟨h4.threads, h4.active, rfl⟩, ?_, hns3,
      fun j hj => (hlm3 j (by omega)).trans (hlmP j hj)⟩
    · rw [steps_add, hm, ok_bind, steps_one hstep]
    · rw [htake, h4.allocs]
      exact hlo3

/-- **Init block (`StateRelN`).** From `StartRel` (Anneal at `(0, 0)` and
MiniRust at `f.start`), `initLen body` MiniRust steps execute `minimize`'s init
block (`StorageLive` of each temporary of `alwaysStorageLiveLocals`, then
`Goto(bb0)`) and land in `StateRelN`. -/
theorem step_start_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRelN body f ctx s m0 := by
  obtain ⟨_, hargs, _, _, _, _, _, _, _, _⟩ := inFragment_spec body hfrag
  obtain ⟨_, hinit⟩ := translateFn_start body f hf
  have hlenS : (initBlock body).statements.length = (alwaysStorageLiveLocals body).length := by
    simp [initBlock]
  obtain ⟨m, lm, hm, hsh, hlo, hnsL, hlmP⟩ := step_start_key hfrag hf hstart hns _ (Nat.le_refl _)
  rw [List.take_length] at hlo
  obtain ⟨m0, hm0, h0⟩ := jumpToBlock_callee (resetPick_shape hsh) 0
  have hif : (((alwaysStorageLiveLocals body).length : Nat) : Int) =
      ((initBlock body).statements.length : Int) := by rw [hlenS]
  have hstep : Interp.step m = .ok m0 := by
    rw [step_callee hsh (initBlock body) hinit]
    simp [hif, initBlock, Interp.evalTerminator, hm0, check_after h0]
  have hn0 : 0 < body.localDecls.length := by omega
  have hthr0 : m0.threads =
      [thread1 ctx [ctx.caller, calleeFrameL f ctx lm s.frame.blockIdx s.frame.stmtIdx]] := by
    rw [hstart.blk0, hstart.stmt0]; exact h0.threads
  have hlo0 : LocalsOk body ctx s.frame.locals lm m0.mem.memory.allocations := by
    rw [h0.allocs]; exact hlo
  have hnpP := inFragment_params_not_ptr body hfrag
  have hnoPtr : ∀ (p : Nat) dp pv, body.localDecls[p]? = some dp → isPtrTy dp.ty = true →
      s.frame.locals[p]? ≠ some (.init (.ptr pv 8)) := by
    intro p dp pv hdp hpty hv
    by_cases hp : p < body.argCount + 1
    · rw [hnpP p dp hp hdp] at hpty; cases hpty
    · have := hstart.tempsDead p (by omega) (List.getElem?_eq_some_iff.mp hdp).1
      rw [hv] at this; cases this
  have hloB : LocalsOk body (ctxWithBorrows body ctx s.memory.borrows) s.frame.locals lm
      m0.mem.memory.allocations :=
    LocalsOkA.extend_ptrTargets (ctx1 := ctx) (ctx2 := ctxWithBorrows body ctx s.memory.borrows)
      rfl hlo0 (fun i d pv _ _ hd hpty hv _ => absurd hv (hnoPtr i d pv hd hpty))
  have hbo : BorrowsOk body ctx s.frame.locals s lm := by
    obtain ⟨hpa, _⟩ := inFragment_ptr body hfrag
    obtain ⟨haddrP, _, _⟩ := ptrAliasingOk_spec hpa
    refine BorrowsOk.start hstart.borrows (fun _ => hstart.nextTag_pos)
      (fun _ k hk => ?_) (fun _ k hk => ?_) hnoPtr
    · obtain ⟨hk1, hk2⟩ := haddrP k hk
      have hk_mem : k ∈ List.range (body.argCount + 1) := List.mem_range.mpr (by omega)
      have hchk := (List.all_eq_true.mp hns) k hk_mem
      have hk_lt : k < body.localDecls.length := by omega
      obtain ⟨dk, hdk⟩ : ∃ d, body.localDecls[k]? = some d := ⟨_, List.getElem?_eq_getElem hk_lt⟩
      obtain ⟨sk, hsk⟩ : ∃ s0, s.frame.locals[k]? = some s0 :=
        ⟨_, List.getElem?_eq_getElem (by rw [hstart.nlocals]; exact hk_lt)⟩
      have hkc : (bodyAddrTakenLocals body).contains k = true := List.contains_iff_mem.mpr hk
      simp only [hdk, hsk, hkc, Bool.not_true, Bool.and_false, Bool.false_or] at hchk
      cases sk with
      | dead => simp [slotIsInit] at hchk
      | uninit => simp [slotIsInit] at hchk
      | init v => exact ⟨v, hsk⟩
    · obtain ⟨hk1, hk2⟩ := haddrP k hk
      refine ⟨fun h => hstart.argsLive k .dead hk2 h rfl, hlmP k (by omega),
        fun d hd => ⟨hnpP k d (by omega) hd, (hstart.addrs k d hk2 hd).1,
          Int.lt_trans (hstart.addrs k d hk2 hd).2 (by decide)⟩⟩
  refine ⟨m0, by rw [initLen, steps_add, hm, ok_bind, steps_one hstep], s.frame.locals, lm, ?_,
    hthr0, hloB, hnsL, hbo⟩
  exact {
    frame := ⟨lm, hthr0, hloB.forget_ptrTargets⟩
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
    borrows := .inl hstart.borrows
    callStack := hstart.callStack
    activeCallee := hstart.activeCallee
    protectors := hstart.protectors
    callerLocals := hstart.callerLocals }

/-- **Init block.** From `StartRel` (Anneal at `(0, 0)` and MiniRust at
`f.start`), `initLen body` MiniRust steps execute `minimize`'s init block
(`StorageLive` of each temporary of `alwaysStorageLiveLocals`, then
`Goto(bb0)`) and land in `StateRel`. -/
theorem step_start {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRel body f ctx s m0 :=
  let ⟨m0, hm0, h0⟩ := step_start_N hfrag hf hstart hns
  ⟨m0, hm0, h0.toStateRel⟩

/-- **Init block (with intermediate non-return invariant).** From `StartRel`
(Anneal at `(0, 0)` and MiniRust at `f.start`), `initLen body` MiniRust steps
execute `minimize`'s init block (`StorageLive` of each temporary of
`alwaysStorageLiveLocals`, then `Goto(bb0)`), land in `StateRel`, and keep a
2-frame stack (`¬ ReturnRel`) at every intermediate step `j ≤ initLen body`. -/
theorem step_start_with_no_returnRel {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    (∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRel body f ctx s m0) ∧
    (∀ j ≤ initLen body, ∀ mj, Interp.steps j mInit = .ok mj →
      ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mj) := by
  obtain ⟨m0, hm0Steps, hrel0⟩ := step_start hfrag hf hstart hns
  refine ⟨⟨m0, hm0Steps, hrel0⟩, fun j hj mj hmj b' c' s' v => ?_⟩
  rcases Nat.lt_or_eq_of_le hj with hjlt | rfl
  · obtain ⟨mk, lmk, hmk, hshk, _⟩ :=
      step_start_key hfrag hf hstart hns j (by rw [initLen] at hjlt; omega)
    rw [hmk] at hmj
    cases hmj
    exact Shape.not_returnRel_of_ne_nil (callerFrames := [ctx.caller]) hshk (by simp)
  · rw [hm0Steps] at hmj
    cases hmj
    exact StateRel.not_returnRel hrel0

/-- No prefix step `j ≤ initLen body` of `step_start` can satisfy `ReturnRel`. -/
theorem step_start_no_returnRel {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∀ j ≤ initLen body, ∀ mj, Interp.steps j mInit = .ok mj →
      ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mj :=
  (step_start_with_no_returnRel hfrag hf hstart hns).2

private theorem argOk_slotOk {T : Gen.Type} {v : Value} (hv : argOk T v = true) :
    SlotOk T (.init v) := by
  match v, hv with
  | .scalar sc, hv =>
    simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨hv.1, (validBits_iff _ _).mp hv.2⟩
  | .aggregate 0 [.scalar sc0, .scalar sc1], hv =>
    simp only [argOk] at hv
    cases ht : tupleIntOfTy T with
    | none => simp [ht] at hv
    | some it =>
      simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact ⟨it, ht, hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩

private theorem declArgOk_declSlotOk {layouts : Layout.LayoutTable} {d : LocalDecl} {v : Value}
    (hv : declArgOk d v layouts = true) : DeclSlotOk d (.init v) layouts := by
  unfold declArgOk at hv
  unfold DeclSlotOk
  split at hv
  · next hsc => simp only [hsc, ↓reduceIte]; exact argOk_slotOk hv
  · next hsc =>
    simp only [hsc, Bool.false_eq_true, ↓reduceIte]
    cases ha : arrayTypeOf d.ty with
    | some p =>
      obtain ⟨elemIt, count⟩ := p
      simp only [ha] at hv ⊢
      cases v with
      | aggregate vIdx elems =>
        cases vIdx with
        | zero =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
          refine ⟨hv.1, fun elem helem => ?_⟩
          have harg := hv.2 elem helem
          cases elem with
          | scalar sc =>
            obtain ⟨h1, h2⟩ := argOk_slotOk harg
            exact ⟨h1, h2⟩
          | aggregate vIdx' flds =>
            cases vIdx' with
            | zero =>
              cases flds with
              | nil => simp [argOk] at harg
              | cons f0 rest =>
                cases rest with
                | nil => simp [argOk] at harg
                | cons f1 rest2 =>
                  cases rest2 with
                  | nil =>
                    cases f0 <;> cases f1 <;> simp [argOk, tupleIntOfTy] at harg
                  | cons _ _ => simp [argOk] at harg
            | succ _ => simp [argOk] at harg
          | _ => simp [argOk] at harg
        | succ _ => simp at hv
      | _ => simp at hv
    | none =>
      cases ht : tupleTypeOf layouts d.ty with
      | some p =>
        obtain ⟨fields, size, align⟩ := p
        simp only [ha, ht, Bool.and_eq_true] at hv ⊢
        exact hv
      | none =>
        simp only [ha, ht] at hv ⊢
        split
        · next hp =>
          obtain ⟨hT, _⟩ := tyOf_isPtrTy (layouts := layouts) hp
          rcases declPtrTy_cases d.ty with hptr | ⟨m', it', _, hptr⟩ <;> {
            rw [hT, hptr] at hv
            exfalso
            revert hv
            unfold argOk
            split <;> simp [validBits, thinRawPtrTy, refTy, refPtrType, tupleIntOfTy]
          }
        · exact argOk_slotOk hv

theorem initLocalsAux_spec (layouts : Layout.LayoutTable) (ds : List LocalDecl) (vs : List Value)
    (idx : Nat) (h : argsOkAux (ds.take vs.length) vs layouts = true) (hlen : vs.length ≤ ds.length) :
    (initLocalsAux (idx + 1) ds vs).length = ds.length ∧
    (∀ (j : Nat) d slot, ds[j]? = some d → (initLocalsAux (idx + 1) ds vs)[j]? = some slot →
      DeclSlotOk d slot layouts) ∧
    (∀ (j : Nat) slot, j < vs.length → (initLocalsAux (idx + 1) ds vs)[j]? = some slot →
      ∃ v, slot = .init v) ∧
    (∀ (j : Nat), vs.length ≤ j → j < ds.length →
      (initLocalsAux (idx + 1) ds vs)[j]? = some .dead) := by
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
        | zero =>
          simp at hs'; subst hs'
          unfold DeclSlotOk
          split <;> trivial
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
      have hvslot : DeclSlotOk d (.init v) layouts := declArgOk_declSlotOk hv
      rw [hcons]
      refine ⟨by simp [hl], fun j d' slot hd' hs' => ?_, fun j slot hj hs' => ?_, fun j hj1 hj2 => ?_⟩
      · cases j with
        | zero => simp at hd' hs'; subst hd' hs'; exact hvslot
        | succ j => simp at hd' hs'; exact hs j d' slot hd' hs'
      · cases j with
        | zero => simp at hs'; exact ⟨v, hs'.symm⟩
        | succ j => simp at hs' hj; exact hlive j slot (by omega) hs'
      · cases j with
        | zero => simp at hj1
        | succ j => simpa using hd j (by simp at hj1; omega) (by simpa using hj2)

private theorem argsOkAux_length {layouts : Layout.LayoutTable} :
    ∀ (ds : List LocalDecl) (vs : List Value), argsOkAux ds vs layouts = true →
      vs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [argsOkAux] at h
  | _ :: _, [], h => by simp [argsOkAux] at h
  | _ :: ds, _ :: vs, h => by
    simp only [argsOkAux, Bool.and_eq_true] at h
    simp [argsOkAux_length ds vs h.2]

theorem initLocalsAux_one_spec (layouts : Layout.LayoutTable) (ds : List LocalDecl) (vs : List Value)
    (h : argsOkAux ds vs layouts = true) :
    (initLocalsAux 1 ds vs).length = ds.length ∧
    ∀ (k : Nat) d slot, ds[k]? = some d → (initLocalsAux 1 ds vs)[k]? = some slot →
      DeclSlotOk d slot layouts := by
  have heq := argsOkAux_length ds vs h
  obtain ⟨hl, hs, _, _⟩ := initLocalsAux_spec layouts ds vs 0
    (by rw [heq, List.take_length]; exact h) (by omega)
  exact ⟨hl, hs⟩

theorem initMachineState_nonScalar {body : CapturedMir}
    (hfrag : inFragment body = true) (args : List Value) (hargs : argsOk body args = true) :
    nonScalarSlotsInit body (initMachineState body args).frame.locals = true := by
  obtain ⟨_, hdeclLen, _, hret0, _, _, _, _, _, _⟩ := inFragment_spec body hfrag
  cases hdecls : body.localDecls with
  | nil => simp [hdecls] at hdeclLen
  | cons d0 ds =>
    rw [hdecls] at hdeclLen
    have hargs' : argsOkAux (ds.take body.argCount) args body.layouts = true := by
      simpa [argsOk, hdecls] using hargs
    have hlenA : args.length = body.argCount := by
      have := argsOkAux_length (ds.take body.argCount) args hargs'
      simp at this hdeclLen
      omega
    obtain ⟨_, _, hlive, _⟩ := initLocalsAux_spec body.layouts ds args 0
      (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega)
    have hinit : (initMachineState body args).frame.locals = .uninit :: initLocalsAux 1 ds args := by
      simp [initMachineState, hdecls, initLocalsAux]
    simp only [nonScalarSlotsInit, List.all_eq_true, List.mem_range]
    intro i hi
    cases i with
    | zero =>
      have h0sc : (scalarTypeOf d0.ty).isSome = true := by simpa [hdecls] using hret0
      obtain ⟨hpa, _⟩ := inFragment_ptr body hfrag
      obtain ⟨haddrP, _, _⟩ := ptrAliasingOk_spec hpa
      have h0not : 0 ∉ bodyAddrTakenLocals body := fun hmem => by
        have := (haddrP 0 hmem).1; omega
      simp [hdecls, hinit, h0sc, h0not]
    | succ k =>
      simp only [hdecls, hinit, List.getElem?_cons_succ]
      cases hd : ds[k]? with
      | none => rfl
      | some d =>
        cases hs : (initLocalsAux 1 ds args)[k]? with
        | none => rfl
        | some slot =>
          obtain ⟨v, rfl⟩ := hlive k slot (by omega) hs
          simp [slotIsInit]

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
        (initMachineState body args).frame.locals body.layouts) :
    StartRel body f ctx (initMachineState body args) mInit := by
  have hbne : body.basicBlocks ≠ [] := by
    simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq] at hfrag
    exact hfrag.1.1.1.1.1.1.2
  obtain ⟨_, hdeclLen, _, hret0, _, _, _, _, _, _⟩ := inFragment_spec body hfrag
  cases hdecls : body.localDecls with
  | nil => simp [hdecls] at hdeclLen
  | cons d0 ds =>
    rw [hdecls] at hdeclLen
    have hargs' : argsOkAux (ds.take body.argCount) args body.layouts = true := by
      simpa [argsOk, hdecls] using hargs
    have hlenA : args.length = body.argCount := by
      have := argsOkAux_length (ds.take body.argCount) args hargs'
      simp at this hdeclLen
      omega
    obtain ⟨hlen, hslots, hlive, hdead⟩ := initLocalsAux_spec body.layouts ds args 0
      (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega)
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
      nextTag_pos := Nat.zero_lt_one
      callStack := rfl
      activeCallee := rfl
      protectors := rfl
      callerLocals := rfl }
    · intro i d slot hd hs
      rw [hdecls] at hd
      rw [hinit] at hs
      cases i with
      | zero =>
        simp at hd hs
        subst hd; subst hs
        have h0sc : (scalarTypeOf d0.ty).isSome = true := by simpa [hdecls] using hret0
        simp [DeclSlotOk, h0sc, SlotOk]
      | succ k => simp at hd hs; exact hslots k d slot hd hs
    · intro i slot hi hs
      rw [hinit] at hs
      cases i with
      | zero => simp at hs; subst hs; simp
      | succ k =>
        simp at hs
        obtain ⟨v, rfl⟩ := hlive k slot (by omega) hs
        simp
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
      (∀ st ∈ bb.statements, progStatementOk body.localDecls st body.layouts = true) ∧
      (terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true ∨
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

/-- The multi-function fragment is scalar-only: every local of a body in
`bodyInProgFragment` has a scalar type. -/
theorem bodyInProgFragment_allScalar {fnMap : FnMap}
    {callees : List CapturedMir} {body : CapturedMir}
    (h : bodyInProgFragment fnMap callees body = true) :
    body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true := by
  simp only [bodyInProgFragment, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hsc⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact hsc

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

/-! #### Unconditional convergence and greatest-fixed-point optimality of `livenessOk` & `tupleInitOk` -/

private def genInitEntries (bbs : List BasicBlockData) (init0 initOther : List Nat) :
    List (List Nat) :=
  (List.range bbs.length).map fun blk => if blk == 0 then init0 else initOther

private def genStepFn (bbs : List BasicBlockData)
    (blockExit : BasicBlockData → List Nat → List Nat)
    (entries : List (List Nat)) (dst : Nat) (acc : List Nat) (src : Nat) : List Nat :=
  match bbs[src]? with
  | some bb =>
    if (termTargets bb.terminator).contains dst then
      let exitSet := blockExit bb (entries.getD src [])
      acc.filter (fun i => exitSet.contains i)
    else acc
  | none => acc

private def genStepEntries (bbs : List BasicBlockData) (init0 initOther : List Nat)
    (blockExit : BasicBlockData → List Nat → List Nat) (entries : List (List Nat)) :
    List (List Nat) :=
  (List.range bbs.length).map fun dst =>
    let initAcc := if dst == 0 then init0 else entries.getD dst initOther
    (List.range bbs.length).foldl (genStepFn bbs blockExit entries dst) initAcc

private def genIterEntries : Nat → List BasicBlockData → List Nat → List Nat →
    (BasicBlockData → List Nat → List Nat) → List (List Nat) → List (List Nat)
  | 0, _, _, _, _, entries => entries
  | n + 1, bbs, init0, initOther, blockExit, entries =>
    let entries' := genStepEntries bbs init0 initOther blockExit entries
    if entries' == entries then entries
    else genIterEntries n bbs init0 initOther blockExit entries'

private theorem filter_true_eq (xs : List Nat) : xs.filter (fun _ => true) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem foldl_genStepFn_filter (bbs : List BasicBlockData)
    (blockExit : BasicBlockData → List Nat → List Nat)
    (entries : List (List Nat)) (dst : Nat) (srcs : List Nat) (acc : List Nat) :
    ∃ q : Nat → Bool, srcs.foldl (genStepFn bbs blockExit entries dst) acc = acc.filter q := by
  induction srcs generalizing acc with
  | nil => exact ⟨fun _ => true, (filter_true_eq acc).symm⟩
  | cons src srcs ih =>
    have h1 : ∃ q1 : Nat → Bool,
        genStepFn bbs blockExit entries dst acc src = acc.filter q1 := by
      simp only [genStepFn]
      cases bbs[src]? with
      | none => exact ⟨fun _ => true, (filter_true_eq acc).symm⟩
      | some bb =>
        simp only
        split
        · exact ⟨_, rfl⟩
        · exact ⟨fun _ => true, (filter_true_eq acc).symm⟩
    obtain ⟨q1, hq1⟩ := h1
    obtain ⟨q2, hq2⟩ := ih (acc.filter q1)
    exact ⟨fun a => q2 a && q1 a, by rw [List.foldl_cons, hq1, hq2, List.filter_filter]⟩

private theorem foldl_genStepFn_mem (bbs : List BasicBlockData)
    (blockExit : BasicBlockData → List Nat → List Nat)
    (entries : List (List Nat)) (dst : Nat) (srcs : List Nat) (acc : List Nat) (i : Nat) :
    i ∈ srcs.foldl (genStepFn bbs blockExit entries dst) acc ↔
      i ∈ acc ∧ ∀ src ∈ srcs, ∀ bb, bbs[src]? = some bb →
        dst ∈ termTargets bb.terminator → i ∈ blockExit bb (entries.getD src []) := by
  induction srcs generalizing acc with
  | nil => simp
  | cons src srcs ih =>
    rw [List.foldl_cons, ih]
    have hstep : i ∈ genStepFn bbs blockExit entries dst acc src ↔
        i ∈ acc ∧ ∀ bb, bbs[src]? = some bb →
          dst ∈ termTargets bb.terminator → i ∈ blockExit bb (entries.getD src []) := by
      cases hbb : bbs[src]? with
      | none => simp [genStepFn, hbb]
      | some bb =>
        simp only [genStepFn, hbb, Option.some.injEq]
        by_cases ht : (termTargets bb.terminator).contains dst = true
        · have ht' : dst ∈ termTargets bb.terminator := List.contains_iff_mem.mp ht
          simp only [ht, ↓reduceIte, List.mem_filter, List.contains_iff_mem]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun _ hEq _ => hEq ▸ h2⟩,
            fun ⟨h1, h2⟩ => ⟨h1, h2 bb rfl ht'⟩⟩
        · simp only [ht, Bool.false_eq_true, ↓reduceIte]
          have ht' : dst ∉ termTargets bb.terminator :=
            fun hm => ht (List.contains_iff_mem.mpr hm)
          exact ⟨fun h1 => ⟨h1, fun _ hEq h => absurd (hEq ▸ h) ht'⟩, fun ⟨h1, _⟩ => h1⟩
    rw [hstep]
    constructor
    · rintro ⟨⟨ha, hs0⟩, hss⟩
      refine ⟨ha, fun s hs bb hbb ht => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hmem
      · exact hs0 bb hbb ht
      · exact hss s hmem bb hbb ht
    · rintro ⟨ha, hss⟩
      exact ⟨⟨ha, fun bb hbb ht => hss src List.mem_cons_self bb hbb ht⟩,
        fun s hs bb hbb ht => hss s (List.mem_cons_of_mem _ hs) bb hbb ht⟩

private theorem genInitEntries_getD (bbs : List BasicBlockData) (init0 initOther : List Nat)
    {dst : Nat} (hdst : dst < bbs.length) :
    (genInitEntries bbs init0 initOther).getD dst [] =
      if dst == 0 then init0 else initOther := by
  simp [genInitEntries, List.getD, List.getElem?_map, List.getElem?_range hdst]

private theorem genStepEntries_getD (bbs : List BasicBlockData) (init0 initOther : List Nat)
    (blockExit : BasicBlockData → List Nat → List Nat) (entries : List (List Nat))
    {dst : Nat} (hdst : dst < bbs.length) :
    (genStepEntries bbs init0 initOther blockExit entries).getD dst [] =
      (List.range bbs.length).foldl (genStepFn bbs blockExit entries dst)
        (if dst == 0 then init0 else entries.getD dst initOther) := by
  simp [genStepEntries, List.getD, List.getElem?_map, List.getElem?_range hdst]

private theorem getD_eq_getD_nil {entries : List (List Nat)} {d : List Nat} {dst : Nat}
    (h : dst < entries.length) : entries.getD dst d = entries.getD dst [] := by
  simp [List.getD, List.getElem?_eq_getElem h]

private def IsFilteredFrom (bbs : List BasicBlockData) (init0 initOther : List Nat)
    (entries : List (List Nat)) : Prop :=
  entries.length = bbs.length ∧
  ∀ dst < bbs.length, ∃ p : Nat → Bool,
    entries.getD dst [] = ((genInitEntries bbs init0 initOther).getD dst []).filter p

private theorem isFilteredFrom_init (bbs : List BasicBlockData) (init0 initOther : List Nat) :
    IsFilteredFrom bbs init0 initOther (genInitEntries bbs init0 initOther) :=
  ⟨by simp [genInitEntries], fun _ _ => ⟨fun _ => true, (filter_true_eq _).symm⟩⟩

private theorem isFilteredFrom_step (bbs : List BasicBlockData) (init0 initOther : List Nat)
    (blockExit : BasicBlockData → List Nat → List Nat) {entries : List (List Nat)}
    (hf : IsFilteredFrom bbs init0 initOther entries) :
    IsFilteredFrom bbs init0 initOther
      (genStepEntries bbs init0 initOther blockExit entries) := by
  refine ⟨by simp [genStepEntries], fun dst hdst => ?_⟩
  rw [genStepEntries_getD bbs init0 initOther blockExit entries hdst,
    genInitEntries_getD bbs init0 initOther hdst]
  have hinitAcc : ∃ p0 : Nat → Bool,
      (if dst == 0 then init0 else entries.getD dst initOther) =
        (if dst == 0 then init0 else initOther).filter p0 := by
    by_cases hd0 : (dst == 0) = true
    · simp only [hd0, ↓reduceIte]
      exact ⟨fun _ => true, (filter_true_eq init0).symm⟩
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p0, hp0⟩ := hf.2 dst hdst
      rw [genInitEntries_getD bbs init0 initOther hdst] at hp0
      simp only [hd0, Bool.false_eq_true, ↓reduceIte] at hp0
      rw [getD_eq_getD_nil (by rw [hf.1]; exact hdst), hp0]
      exact ⟨p0, rfl⟩
  obtain ⟨p0, hp0⟩ := hinitAcc
  obtain ⟨q, hq⟩ := foldl_genStepFn_filter bbs blockExit entries dst (List.range bbs.length)
    (if dst == 0 then init0 else entries.getD dst initOther)
  exact ⟨fun a => q a && p0 a, by rw [hq, hp0, List.filter_filter]⟩

private theorem isFilteredFrom_iter (fuel : Nat) (bbs : List BasicBlockData)
    (init0 initOther : List Nat) (blockExit : BasicBlockData → List Nat → List Nat)
    {entries : List (List Nat)} (hf : IsFilteredFrom bbs init0 initOther entries) :
    IsFilteredFrom bbs init0 initOther
      (genIterEntries fuel bbs init0 initOther blockExit entries) := by
  induction fuel generalizing entries with
  | zero => exact hf
  | succ n ih =>
    simp only [genIterEntries]
    split
    · exact hf
    · exact ih (isFilteredFrom_step bbs init0 initOther blockExit hf)

private theorem genStepEntries_mem (bbs : List BasicBlockData) (init0 initOther : List Nat)
    (blockExit : BasicBlockData → List Nat → List Nat) {entries : List (List Nat)}
    (hlen : entries.length = bbs.length) {dst : Nat} (hdst : dst < bbs.length) (i : Nat) :
    i ∈ (genStepEntries bbs init0 initOther blockExit entries).getD dst [] ↔
      i ∈ (if dst == 0 then init0 else entries.getD dst []) ∧
      ∀ src < bbs.length, ∀ bb, bbs[src]? = some bb →
        dst ∈ termTargets bb.terminator → i ∈ blockExit bb (entries.getD src []) := by
  rw [genStepEntries_getD bbs init0 initOther blockExit entries hdst,
    getD_eq_getD_nil (d := initOther) (by omega),
    foldl_genStepFn_mem]
  simp [List.mem_range]

private theorem genStepEntries_mono (bbs : List BasicBlockData) (init0 initOther : List Nat)
    (blockExit : BasicBlockData → List Nat → List Nat)
    (hmono : ∀ bb (a b : List Nat), (∀ i ∈ a, i ∈ b) → ∀ i ∈ blockExit bb a, i ∈ blockExit bb b)
    {entries1 entries2 : List (List Nat)}
    (hlen1 : entries1.length = bbs.length) (hlen2 : entries2.length = bbs.length)
    (hsub : ∀ src < bbs.length, ∀ i ∈ entries1.getD src [], i ∈ entries2.getD src []) :
    ∀ dst < bbs.length,
      ∀ i ∈ (genStepEntries bbs init0 initOther blockExit entries1).getD dst [],
        i ∈ (genStepEntries bbs init0 initOther blockExit entries2).getD dst [] := by
  intro dst hdst i hi
  rw [genStepEntries_mem bbs init0 initOther blockExit hlen1 hdst] at hi
  rw [genStepEntries_mem bbs init0 initOther blockExit hlen2 hdst]
  refine ⟨?_, fun src hsrc bb hbb ht =>
    hmono bb _ _ (hsub src hsrc) i (hi.2 src hsrc bb hbb ht)⟩
  by_cases h0 : (dst == 0) = true
  · have h1 := hi.1
    simp only [h0, ↓reduceIte] at h1 ⊢
    exact h1
  · have h1 := hi.1
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    exact hsub dst hdst i h1

private theorem eq_or_strict_of_isFiltered {bbs : List BasicBlockData}
    {init0 initOther : List Nat} {entries1 entries2 : List (List Nat)}
    (hf1 : IsFilteredFrom bbs init0 initOther entries1)
    (hf2 : IsFilteredFrom bbs init0 initOther entries2)
    (hsub : ∀ dst < bbs.length, ∀ i ∈ entries1.getD dst [], i ∈ entries2.getD dst []) :
    entries1 = entries2 ∨
      ∃ dst < bbs.length, ∃ j ∈ entries2.getD dst [], j ∉ entries1.getD dst [] := by
  by_cases hall : ∀ dst < bbs.length, ∀ j ∈ entries2.getD dst [], j ∈ entries1.getD dst []
  · left
    apply List.ext_getElem (hf1.1.trans hf2.1.symm)
    intro dst h1 h2
    have hdst : dst < bbs.length := hf1.1 ▸ h1
    have hget1 : entries1[dst] = entries1.getD dst [] := by
      simp [List.getD, List.getElem?_eq_getElem h1]
    have hget2 : entries2[dst] = entries2.getD dst [] := by
      simp [List.getD, List.getElem?_eq_getElem h2]
    rw [hget1, hget2]
    obtain ⟨p1, hp1⟩ := hf1.2 dst hdst
    obtain ⟨p2, hp2⟩ := hf2.2 dst hdst
    rw [hp1, hp2]
    apply List.filter_congr
    intro x hx
    have hiff : p1 x = true ↔ p2 x = true := by
      constructor
      · intro hp1x
        have hx1 : x ∈ entries1.getD dst [] := hp1 ▸ List.mem_filter.mpr ⟨hx, hp1x⟩
        have hx2 : x ∈ ((genInitEntries bbs init0 initOther).getD dst []).filter p2 :=
          hp2 ▸ hsub dst hdst x hx1
        exact (List.mem_filter.mp hx2).2
      · intro hp2x
        have hx2 : x ∈ entries2.getD dst [] := hp2 ▸ List.mem_filter.mpr ⟨hx, hp2x⟩
        have hx1 : x ∈ ((genInitEntries bbs init0 initOther).getD dst []).filter p1 :=
          hp1 ▸ hall dst hdst x hx2
        exact (List.mem_filter.mp hx1).2
    cases hp1x : p1 x <;> cases hp2x : p2 x <;> simp_all
  · right
    obtain ⟨dst, hdst⟩ := Classical.not_forall.mp hall
    obtain ⟨hdstLt, hrest⟩ := Decidable.not_imp_iff_and_not.mp hdst
    obtain ⟨j, hj⟩ := Classical.not_forall.mp hrest
    obtain ⟨hjIn, hjNot⟩ := Decidable.not_imp_iff_and_not.mp hj
    exact ⟨dst, hdstLt, j, hjIn, hjNot⟩

private theorem isFilteredFrom_lt {M : Nat} {bbs : List BasicBlockData}
    {init0 initOther : List Nat}
    (h0 : ∀ i ∈ init0, i < M) (hO : ∀ i ∈ initOther, i < M)
    {entries : List (List Nat)} (hf : IsFilteredFrom bbs init0 initOther entries) :
    ∀ dst < bbs.length, ∀ j ∈ entries.getD dst [], j < M := by
  intro dst hdst j hj
  obtain ⟨p, hp⟩ := hf.2 dst hdst
  rw [hp, genInitEntries_getD bbs init0 initOther hdst] at hj
  have hjBase := (List.mem_filter.mp hj).1
  split at hjBase
  · exact h0 j hjBase
  · exact hO j hjBase

private theorem genIterEntries_stabilizes_from {M : Nat} {bbs : List BasicBlockData}
    {init0 initOther : List Nat} {blockExit : BasicBlockData → List Nat → List Nat}
    (hmono : ∀ bb (a b : List Nat), (∀ i ∈ a, i ∈ b) → ∀ i ∈ blockExit bb a, i ∈ blockExit bb b)
    (h0 : ∀ i ∈ init0, i < M) (hO : ∀ i ∈ initOther, i < M) :
    ∀ (fuel : Nat) (entries : List (List Nat)),
      IsFilteredFrom bbs init0 initOther entries →
      (∀ dst < bbs.length,
        ∀ i ∈ (genStepEntries bbs init0 initOther blockExit entries).getD dst [],
          i ∈ entries.getD dst []) →
      bbs.length * M - remCapAux M entries (List.range bbs.length) ≤ fuel →
      genStepEntries bbs init0 initOther blockExit
          (genIterEntries fuel bbs init0 initOther blockExit entries) =
        genIterEntries fuel bbs init0 initOther blockExit entries := by
  intro fuel
  induction fuel with
  | zero =>
    intro entries hf hsub hcap
    have hf' := isFilteredFrom_step bbs init0 initOther blockExit hf
    rcases eq_or_strict_of_isFiltered hf' hf hsub with hfix | ⟨dst, hdst, j, hin, hnot⟩
    · simpa [genIterEntries] using hfix
    · have hjM : j < M := isFilteredFrom_lt h0 hO hf dst hdst j hin
      have hlt := remCapAux_lt (L := M)
        (fun d hd => hsub d (List.mem_range.mp hd))
        (List.mem_range.mpr hdst) hjM hnot hin
      have hle : remCapAux M
          (genStepEntries bbs init0 initOther blockExit entries)
          (List.range bbs.length) ≤ bbs.length * M := by
        simpa using remCapAux_le M
          (genStepEntries bbs init0 initOther blockExit entries)
          (List.range bbs.length)
      omega
  | succ n ih =>
    intro entries hf hsub hcap
    simp only [genIterEntries]
    by_cases hbeq : (genStepEntries bbs init0 initOther blockExit entries == entries) = true
    · simp only [hbeq, ↓reduceIte]
      exact beq_iff_eq.mp hbeq
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hne : genStepEntries bbs init0 initOther blockExit entries ≠ entries :=
        fun h => hbeq (beq_iff_eq.mpr h)
      have hf' := isFilteredFrom_step bbs init0 initOther blockExit hf
      rcases eq_or_strict_of_isFiltered hf' hf hsub with hfix | ⟨dst, hdst, j, hin, hnot⟩
      · exact False.elim (hne hfix)
      · have hjM : j < M := isFilteredFrom_lt h0 hO hf dst hdst j hin
        have hlt := remCapAux_lt (L := M)
          (fun d hd => hsub d (List.mem_range.mp hd))
          (List.mem_range.mpr hdst) hjM hnot hin
        have hle : remCapAux M (genStepEntries bbs init0 initOther blockExit entries)
            (List.range bbs.length) ≤ bbs.length * M := by
          simpa using remCapAux_le M (genStepEntries bbs init0 initOther blockExit entries)
            (List.range bbs.length)
        have hsub' := genStepEntries_mono bbs init0 initOther blockExit hmono
          hf'.1 hf.1 hsub
        exact ih (genStepEntries bbs init0 initOther blockExit entries) hf' hsub' (by omega)

private theorem genIterEntries_stabilizes {M : Nat} {bbs : List BasicBlockData}
    {init0 initOther : List Nat} {blockExit : BasicBlockData → List Nat → List Nat}
    (hmono : ∀ bb (a b : List Nat), (∀ i ∈ a, i ∈ b) → ∀ i ∈ blockExit bb a, i ∈ blockExit bb b)
    (h0 : ∀ i ∈ init0, i < M) (hO : ∀ i ∈ initOther, i < M) :
    genStepEntries bbs init0 initOther blockExit
        (genIterEntries (bbs.length * M) bbs init0 initOther blockExit
          (genInitEntries bbs init0 initOther)) =
      genIterEntries (bbs.length * M) bbs init0 initOther blockExit
        (genInitEntries bbs init0 initOther) := by
  have hf0 := isFilteredFrom_init bbs init0 initOther
  have hsub0 : ∀ dst < bbs.length,
      ∀ i ∈ (genStepEntries bbs init0 initOther blockExit
        (genInitEntries bbs init0 initOther)).getD dst [],
        i ∈ (genInitEntries bbs init0 initOther).getD dst [] := by
    intro dst hdst i hi
    rw [genStepEntries_mem bbs init0 initOther blockExit hf0.1 hdst] at hi
    rw [genInitEntries_getD bbs init0 initOther hdst]
    have h1 := hi.1
    rw [genInitEntries_getD bbs init0 initOther hdst] at h1
    by_cases h0' : (dst == 0) = true
    · simp only [h0', ↓reduceIte] at h1 ⊢; exact h1
    · simp only [h0', Bool.false_eq_true, ↓reduceIte] at h1 ⊢; exact h1
  exact genIterEntries_stabilizes_from hmono h0 hO (bbs.length * M)
    (genInitEntries bbs init0 initOther) hf0 hsub0 (by omega)

private theorem genIterEntries_greatest (fuel : Nat) (bbs : List BasicBlockData)
    (init0 initOther : List Nat) (blockExit : BasicBlockData → List Nat → List Nat)
    (hmono : ∀ bb (a b : List Nat), (∀ i ∈ a, i ∈ b) → ∀ i ∈ blockExit bb a, i ∈ blockExit bb b)
    {entries' : List (List Nat)}
    (hpost0 : ∀ i ∈ entries'.getD 0 [], i ∈ init0)
    (hpostO : ∀ dst < bbs.length, dst ≠ 0 → ∀ i ∈ entries'.getD dst [], i ∈ initOther)
    (hpostEdge : ∀ src dst (bb : BasicBlockData),
      bbs[src]? = some bb → dst < bbs.length → dst ∈ termTargets bb.terminator →
      ∀ i ∈ entries'.getD dst [], i ∈ blockExit bb (entries'.getD src [])) :
    ∀ dst < bbs.length, ∀ i ∈ entries'.getD dst [],
      i ∈ (genIterEntries fuel bbs init0 initOther blockExit
        (genInitEntries bbs init0 initOther)).getD dst [] := by
  have hstep : ∀ entries : List (List Nat), entries.length = bbs.length →
      (∀ dst < bbs.length, ∀ i ∈ entries'.getD dst [], i ∈ entries.getD dst []) →
      ∀ dst < bbs.length, ∀ i ∈ entries'.getD dst [],
        i ∈ (genStepEntries bbs init0 initOther blockExit entries).getD dst [] := by
    intro entries hlen hsub dst hdst i hi
    rw [genStepEntries_mem bbs init0 initOther blockExit hlen hdst]
    refine ⟨?_, fun src hsrc bb hbb ht =>
      hmono bb _ _ (hsub src hsrc) i (hpostEdge src dst bb hbb hdst ht i hi)⟩
    split
    · exact hpost0 i (by simpa [beq_iff_eq.mp ‹_›] using hi)
    · exact hsub dst hdst i hi
  have hiter : ∀ (n : Nat) (entries : List (List Nat)), entries.length = bbs.length →
      (∀ dst < bbs.length, ∀ i ∈ entries'.getD dst [], i ∈ entries.getD dst []) →
      ∀ dst < bbs.length, ∀ i ∈ entries'.getD dst [],
        i ∈ (genIterEntries n bbs init0 initOther blockExit entries).getD dst [] := by
    intro n
    induction n with
    | zero => intro entries _ hsub; exact hsub
    | succ m ih =>
      intro entries hlen hsub dst hdst i hi
      simp only [genIterEntries]
      split
      · exact hsub dst hdst i hi
      · exact ih _ (by simp [genStepEntries]) (hstep entries hlen hsub) dst hdst i hi
  apply hiter fuel (genInitEntries bbs init0 initOther) (by simp [genInitEntries])
  intro dst hdst i hi
  rw [genInitEntries_getD bbs init0 initOther hdst]
  by_cases hd0 : dst = 0
  · subst hd0; simp [hpost0 i hi]
  · simp [hd0, hpostO dst hdst hd0 i hi]

private theorem iterLiveEntries_eq_gen (fuel : Nat) (body : CapturedMir)
    (entries : List (List Nat)) :
    iterLiveEntries fuel body entries =
      genIterEntries fuel body.basicBlocks
        (List.range (body.argCount + 1)) (List.range body.localDecls.length)
        (fun bb lv => bb.statements.foldl stmtMustLive lv) entries := by
  induction fuel generalizing entries with
  | zero => rfl
  | succ n ih =>
    simp only [iterLiveEntries, genIterEntries]
    have hstep : stepLiveEntries body entries =
        genStepEntries body.basicBlocks
          (List.range (body.argCount + 1)) (List.range body.localDecls.length)
          (fun bb lv => bb.statements.foldl stmtMustLive lv) entries := rfl
    rw [hstep]
    split
    · rfl
    · exact ih _

private theorem iterTupleInitEntries_eq_gen (fuel : Nat) (body : CapturedMir)
    (entries : List (List Nat)) :
    iterTupleInitEntries fuel body entries =
      genIterEntries fuel body.basicBlocks
        (((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls))
        ((List.range body.localDecls.length).filter (isTupleLocal body.localDecls))
        (fun bb ti => termTupleInit body.localDecls
          (bb.statements.foldl (stmtTupleInit body.localDecls) ti) bb.terminator) entries := by
  induction fuel generalizing entries with
  | zero => rfl
  | succ n ih =>
    simp only [iterTupleInitEntries, genIterEntries]
    have hstep : stepTupleInitEntries body entries =
        genStepEntries body.basicBlocks
          (((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls))
          ((List.range body.localDecls.length).filter (isTupleLocal body.localDecls))
          (fun bb ti => termTupleInit body.localDecls
            (bb.statements.foldl (stmtTupleInit body.localDecls) ti) bb.terminator) entries := rfl
    rw [hstep]
    split
    · rfl
    · exact ih _

/-- Helper for `if xs.contains i then xs else i :: xs` monotonicity. -/
private theorem mem_insert_if_contains_mono {xs ys : List Nat}
    (hsub : ∀ k ∈ xs, k ∈ ys) (i j : Nat)
    (hj : j ∈ (if xs.contains i then xs else i :: xs)) :
    j ∈ (if ys.contains i then ys else i :: ys) := by
  have hj' : j = i ∨ j ∈ xs := by
    by_cases hc : xs.contains i = true
    · simp only [hc, ↓reduceIte] at hj; exact .inr hj
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hj; exact List.mem_cons.mp hj
  by_cases hc' : ys.contains i = true
  · simp only [hc', ↓reduceIte]
    rcases hj' with rfl | hm
    · exact List.contains_iff_mem.mp hc'
    · exact hsub j hm
  · simp only [hc', Bool.false_eq_true, ↓reduceIte]
    rcases hj' with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsub j hm)

/-- `stmtMustLive` is monotone with respect to membership in `lv`. -/
theorem stmtMustLive_mono {lv lv' : List Nat} (hsub : ∀ i ∈ lv, i ∈ lv')
    (s : MirAst.Statement) {j : Nat} (hj : j ∈ stmtMustLive lv s) :
    j ∈ stmtMustLive lv' s := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | storageLive i =>
    simp only [stmtMustLive] at hj ⊢
    exact mem_insert_if_contains_mono hsub i j hj
  | storageDead i =>
    simp only [stmtMustLive, List.mem_filter] at hj ⊢
    exact ⟨hsub j hj.1, hj.2⟩
  | _ =>
    simp only [stmtMustLive] at hj ⊢
    exact hsub j hj

private theorem foldl_stmtMustLive_mono (ss : List MirAst.Statement) {lv lv' : List Nat}
    (hsub : ∀ i ∈ lv, i ∈ lv') :
    ∀ j ∈ ss.foldl stmtMustLive lv, j ∈ ss.foldl stmtMustLive lv' := by
  induction ss generalizing lv lv' with
  | nil => exact hsub
  | cons s ss ih => exact ih (fun _ hj => stmtMustLive_mono hsub s hj)

/-- Unconditional finite-fuel convergence of `iterLiveEntries`: whenever
`body.argCount ≤ body.localDecls.length`, `N * (L + 1)` passes of
`stepLiveEntries` from `initLiveEntries body` reach a fixed point. -/
theorem iterLiveEntries_stabilizes {body : CapturedMir}
    (harg : body.argCount ≤ body.localDecls.length) :
    let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
    stepLiveEntries body (iterLiveEntries fuel body (initLiveEntries body)) =
      iterLiveEntries fuel body (initLiveEntries body) := by
  intro fuel
  rw [iterLiveEntries_eq_gen]
  exact genIterEntries_stabilizes
    (fun bb _ _ hsub => foldl_stmtMustLive_mono bb.statements hsub)
    (fun i hi => by have := List.mem_range.mp hi; omega)
    (fun i hi => by have := List.mem_range.mp hi; omega)

/-- `livenessOk body = true` holds unconditionally for every `body` with
`body.argCount ≤ body.localDecls.length`, because `liveAtEntry` is a fixed
point of `stepLiveEntries` (`iterLiveEntries_stabilizes`). -/
theorem livenessOk_eq_true {body : CapturedMir}
    (harg : body.argCount ≤ body.localDecls.length) :
    livenessOk body = true := by
  let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
  have hfix := iterLiveEntries_stabilizes harg
  have hfilt : IsFilteredFrom body.basicBlocks
      (List.range (body.argCount + 1)) (List.range body.localDecls.length)
      (iterLiveEntries fuel body (initLiveEntries body)) := by
    rw [iterLiveEntries_eq_gen]
    exact isFilteredFrom_iter fuel body.basicBlocks
      (List.range (body.argCount + 1)) (List.range body.localDecls.length)
      (fun bb lv => bb.statements.foldl stmtMustLive lv)
      (isFilteredFrom_init _ _ _)
  simp only [livenessOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨fun i hi => ?_, fun blk hblk => ?_⟩
  · by_cases hbbs : 0 < body.basicBlocks.length
    · obtain ⟨p, hp⟩ := hfilt.2 0 hbbs
      have hi' : i ∈ (iterLiveEntries fuel body (initLiveEntries body)).getD 0 [] := hi
      rw [hp, genInitEntries_getD body.basicBlocks _ _ hbbs] at hi'
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_filter, List.mem_range] at hi'
      omega
    · have hlen0 : (iterLiveEntries fuel body (initLiveEntries body)).length = 0 := by
        rw [hfilt.1]; omega
      have hnil := List.eq_nil_of_length_eq_zero hlen0
      simp [liveAtEntry, fuel, hnil, List.getD] at hi
  · cases hbb : body.basicBlocks[blk]? with
    | none => simp
    | some bb =>
      simp only [List.all_eq_true, List.contains_iff_mem]
      intro t ht i hi
      by_cases htLt : t < body.basicBlocks.length
      · have hmem : i ∈ (genStepEntries body.basicBlocks
            (List.range (body.argCount + 1)) (List.range body.localDecls.length)
            (fun bb lv => bb.statements.foldl stmtMustLive lv)
            (iterLiveEntries fuel body (initLiveEntries body))).getD t [] := by
          change i ∈ (stepLiveEntries body
            (iterLiveEntries fuel body (initLiveEntries body))).getD t []
          rw [hfix]
          exact hi
        exact ((genStepEntries_mem body.basicBlocks _ _ _ hfilt.1 htLt i).mp hmem).2
          blk hblk bb hbb ht
      · have htGe : (iterLiveEntries fuel body (initLiveEntries body)).length ≤ t := by
          rw [hfilt.1]; omega
        simp [liveAtEntry, fuel, List.getD, List.getElem?_eq_none htGe] at hi

/-- Greatest post-fixed-point optimality of `liveAtEntry`: any per-block
assignment `entries'` bounded by `_0 .. _argCount` at `bb0`, bounded by
`0 .. localDecls.length - 1` elsewhere, and closed under `stmtMustLive` along
all CFG edges is contained in `liveAtEntry body dst` at every block `dst`. -/
theorem liveAtEntry_greatest {body : CapturedMir} {entries' : List (List Nat)}
    (hpost0 : ∀ i ∈ entries'.getD 0 [], i ≤ body.argCount)
    (hpostO : ∀ dst < body.basicBlocks.length, dst ≠ 0 →
      ∀ i ∈ entries'.getD dst [], i < body.localDecls.length)
    (hpostEdge : ∀ src dst (bb : BasicBlockData),
      body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
      dst ∈ termTargets bb.terminator →
      ∀ i ∈ entries'.getD dst [],
        i ∈ bb.statements.foldl stmtMustLive (entries'.getD src []))
    {dst : Nat} (hdst : dst < body.basicBlocks.length) :
    ∀ i ∈ entries'.getD dst [], i ∈ liveAtEntry body dst := by
  simp only [liveAtEntry, iterLiveEntries_eq_gen]
  exact genIterEntries_greatest
    (body.basicBlocks.length * (body.localDecls.length + 1)) body.basicBlocks
    (List.range (body.argCount + 1)) (List.range body.localDecls.length)
    (fun bb lv => bb.statements.foldl stmtMustLive lv)
    (fun bb _ _ hsub => foldl_stmtMustLive_mono bb.statements hsub)
    (fun i hi => List.mem_range.mpr (by have := hpost0 i hi; omega))
    (fun b hb hne i hi => List.mem_range.mpr (hpostO b hb hne i hi))
    hpostEdge dst hdst

/-- `dropMovedFrom` is monotone with respect to membership in `ti`. -/
theorem dropMovedFrom_mono {ti ti' : List Nat} (hsub : ∀ i ∈ ti, i ∈ ti')
    (ops : List MirAst.Operand) {j : Nat} (hj : j ∈ dropMovedFrom ti ops) :
    j ∈ dropMovedFrom ti' ops := by
  induction ops generalizing ti ti' with
  | nil => exact hsub j hj
  | cons op ops ih =>
    simp only [dropMovedFrom, List.foldl_cons] at hj ⊢
    apply ih _ hj
    intro k hk
    cases hm : opMoved op with
    | none => rw [hm] at hk; exact hsub k hk
    | some m =>
      rw [hm] at hk
      simp only [List.mem_filter] at hk ⊢
      exact ⟨hsub k hk.1, hk.2⟩

/-- `stmtTupleInit` is monotone with respect to membership in `ti`. -/
theorem stmtTupleInit_mono (decls : List LocalDecl) {ti ti' : List Nat}
    (hsub : ∀ i ∈ ti, i ∈ ti') (s : MirAst.Statement) {j : Nat}
    (hj : j ∈ stmtTupleInit decls ti s) : j ∈ stmtTupleInit decls ti' s := by
  obtain ⟨kind, span⟩ := s
  cases kind with
  | assign p rv =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil =>
      simp only [stmtTupleInit] at hj ⊢
      have hd : ∀ k ∈ dropMovedFrom ti (rvOperands rv),
          k ∈ dropMovedFrom ti' (rvOperands rv) :=
        fun _ hk => dropMovedFrom_mono hsub (rvOperands rv) hk
      split at hj
      · next htup =>
        simp only [htup, ↓reduceIte]
        exact mem_insert_if_contains_mono hd i j hj
      · next htup =>
        simp only [htup, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hj ⊢
        exact ⟨hd j hj.1, hj.2⟩
    | cons _ _ =>
      simp only [stmtTupleInit] at hj ⊢
      exact dropMovedFrom_mono hsub (rvOperands rv) hj
  | storageLive i | storageDead i =>
    simp only [stmtTupleInit, List.mem_filter] at hj ⊢
    exact ⟨hsub j hj.1, hj.2⟩
  | deinit p =>
    obtain ⟨i, proj⟩ := p
    cases proj with
    | nil =>
      simp only [stmtTupleInit, List.mem_filter] at hj ⊢
      exact ⟨hsub j hj.1, hj.2⟩
    | cons _ _ =>
      simp only [stmtTupleInit] at hj ⊢
      exact hsub j hj
  | intrinsic intr =>
    cases intr with
    | assume op =>
      simp only [stmtTupleInit] at hj ⊢
      exact dropMovedFrom_mono hsub [op] hj
    | copyNonOverlapping _ _ _ =>
      simp only [stmtTupleInit] at hj ⊢
      exact hsub j hj
  | placeMention _ | setDiscriminant _ _ | retag _ _ | coverage
  | constEvalCounter | backwardIncompatibleDropHint _ | nop =>
    simp only [stmtTupleInit] at hj ⊢
    exact hsub j hj

/-- `termTupleInit` is monotone with respect to membership in `ti`. -/
theorem termTupleInit_mono (decls : List LocalDecl) {ti ti' : List Nat}
    (hsub : ∀ i ∈ ti, i ∈ ti') (t : MirAst.Terminator) {j : Nat}
    (hj : j ∈ termTupleInit decls ti t) : j ∈ termTupleInit decls ti' t := by
  obtain ⟨kind, span⟩ := t
  cases kind with
  | switchInt discr _ =>
    simp only [termTupleInit] at hj ⊢
    exact dropMovedFrom_mono hsub [discr] hj
  | call _ argOps dst target _ =>
    cases target with
    | none =>
      simp only [termTupleInit] at hj ⊢
      exact hsub j hj
    | some _ =>
      obtain ⟨i, proj⟩ := dst
      cases proj with
      | nil =>
        simp only [termTupleInit] at hj ⊢
        have hd : ∀ k ∈ dropMovedFrom ti argOps, k ∈ dropMovedFrom ti' argOps :=
          fun _ hk => dropMovedFrom_mono hsub argOps hk
        split at hj
        · next htup =>
          simp only [htup, ↓reduceIte]
          exact mem_insert_if_contains_mono hd i j hj
        · next htup =>
          simp only [htup, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hj ⊢
          exact ⟨hd j hj.1, hj.2⟩
      | cons _ _ =>
        simp only [termTupleInit] at hj ⊢
        exact dropMovedFrom_mono hsub argOps hj
  | _ =>
    simp only [termTupleInit] at hj ⊢
    exact hsub j hj

private theorem foldl_stmtTupleInit_mono (decls : List LocalDecl)
    (ss : List MirAst.Statement) {ti ti' : List Nat} (hsub : ∀ i ∈ ti, i ∈ ti') :
    ∀ j ∈ ss.foldl (stmtTupleInit decls) ti,
      j ∈ ss.foldl (stmtTupleInit decls) ti' := by
  induction ss generalizing ti ti' with
  | nil => exact hsub
  | cons s ss ih => exact ih (fun _ hj => stmtTupleInit_mono decls hsub s hj)

private theorem isTupleLocal_lt {decls : List LocalDecl} {i : Nat}
    (h : isTupleLocal decls i = true) : i < decls.length := by
  simp only [isTupleLocal] at h
  cases hd : decls[i]? with
  | none => simp [hd] at h
  | some _ => exact (List.getElem?_eq_some_iff.mp hd).1

/-- Unconditional finite-fuel convergence of `iterTupleInitEntries`: for every
`body : CapturedMir`, `N * (L + 1)` passes of `stepTupleInitEntries` from
`initTupleEntries body` reach a fixed point. -/
theorem iterTupleInitEntries_stabilizes (body : CapturedMir) :
    let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
    stepTupleInitEntries body (iterTupleInitEntries fuel body (initTupleEntries body)) =
      iterTupleInitEntries fuel body (initTupleEntries body) := by
  intro fuel
  rw [iterTupleInitEntries_eq_gen]
  exact genIterEntries_stabilizes
    (fun bb _ _ hsub _ hj => termTupleInit_mono body.localDecls
      (foldl_stmtTupleInit_mono body.localDecls bb.statements hsub) bb.terminator hj)
    (fun i hi => by
      have := isTupleLocal_lt (List.mem_filter.mp hi).2
      omega)
    (fun i hi => by
      have := List.mem_range.mp (List.mem_filter.mp hi).1
      omega)

/-- `tupleInitOk body = true` holds unconditionally for every `body : CapturedMir`,
because `tupleInitAtEntry` is a fixed point of `stepTupleInitEntries`
(`iterTupleInitEntries_stabilizes`). -/
theorem tupleInitOk_eq_true (body : CapturedMir) : tupleInitOk body = true := by
  let fuel := body.basicBlocks.length * (body.localDecls.length + 1)
  let init0 := ((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls)
  let initO := (List.range body.localDecls.length).filter (isTupleLocal body.localDecls)
  have hfix := iterTupleInitEntries_stabilizes body
  have hfilt : IsFilteredFrom body.basicBlocks init0 initO
      (iterTupleInitEntries fuel body (initTupleEntries body)) := by
    rw [iterTupleInitEntries_eq_gen]
    exact isFilteredFrom_iter fuel body.basicBlocks init0 initO
      (fun bb ti => termTupleInit body.localDecls
        (bb.statements.foldl (stmtTupleInit body.localDecls) ti) bb.terminator)
      (isFilteredFrom_init _ _ _)
  simp only [tupleInitOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨fun i hi => ?_, fun blk hblk => ?_⟩
  · by_cases hbbs : 0 < body.basicBlocks.length
    · obtain ⟨p, hp⟩ := hfilt.2 0 hbbs
      have hi' : i ∈ (iterTupleInitEntries fuel body (initTupleEntries body)).getD 0 [] := hi
      rw [hp, genInitEntries_getD body.basicBlocks _ _ hbbs] at hi'
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_filter, init0,
        List.mem_map, List.mem_range] at hi'
      obtain ⟨⟨⟨k, hk, rfl⟩, htup⟩, _⟩ := hi'
      exact ⟨⟨by omega, by omega⟩, htup⟩
    · have hlen0 : (iterTupleInitEntries fuel body (initTupleEntries body)).length = 0 := by
        rw [hfilt.1]; omega
      have hnil := List.eq_nil_of_length_eq_zero hlen0
      simp [tupleInitAtEntry, fuel, hnil, List.getD] at hi
  · cases hbb : body.basicBlocks[blk]? with
    | none => simp
    | some bb =>
      simp only [List.all_eq_true, List.contains_iff_mem]
      intro t ht i hi
      by_cases htLt : t < body.basicBlocks.length
      · have hmem : i ∈ (genStepEntries body.basicBlocks init0 initO
            (fun bb ti => termTupleInit body.localDecls
              (bb.statements.foldl (stmtTupleInit body.localDecls) ti) bb.terminator)
            (iterTupleInitEntries fuel body (initTupleEntries body))).getD t [] := by
          change i ∈ (stepTupleInitEntries body
            (iterTupleInitEntries fuel body (initTupleEntries body))).getD t []
          rw [hfix]
          exact hi
        exact ((genStepEntries_mem body.basicBlocks _ _ _ hfilt.1 htLt i).mp hmem).2
          blk hblk bb hbb ht
      · have htGe : (iterTupleInitEntries fuel body (initTupleEntries body)).length ≤ t := by
          rw [hfilt.1]; omega
        simp [tupleInitAtEntry, fuel, List.getD, List.getElem?_eq_none htGe] at hi

/-- Greatest post-fixed-point optimality of `tupleInitAtEntry`: any per-block
assignment `entries'` of `(Int, bool)` tuple locals (`isTupleLocal`) bounded by
`1 .. argCount` at `bb0` and closed under `stmtTupleInit` + `termTupleInit`
along all CFG edges is contained in `tupleInitAtEntry body dst` at every block
`dst`. -/
theorem tupleInitAtEntry_greatest {body : CapturedMir} {entries' : List (List Nat)}
    (hpost0 : ∀ i ∈ entries'.getD 0 [],
      1 ≤ i ∧ i ≤ body.argCount ∧ isTupleLocal body.localDecls i = true)
    (hpostO : ∀ dst < body.basicBlocks.length, dst ≠ 0 →
      ∀ i ∈ entries'.getD dst [], isTupleLocal body.localDecls i = true)
    (hpostEdge : ∀ src dst (bb : BasicBlockData),
      body.basicBlocks[src]? = some bb → dst < body.basicBlocks.length →
      dst ∈ termTargets bb.terminator →
      ∀ i ∈ entries'.getD dst [],
        i ∈ termTupleInit body.localDecls
          (bb.statements.foldl (stmtTupleInit body.localDecls) (entries'.getD src []))
          bb.terminator)
    {dst : Nat} (hdst : dst < body.basicBlocks.length) :
    ∀ i ∈ entries'.getD dst [], i ∈ tupleInitAtEntry body dst := by
  simp only [tupleInitAtEntry, iterTupleInitEntries_eq_gen]
  exact genIterEntries_greatest
    (body.basicBlocks.length * (body.localDecls.length + 1)) body.basicBlocks
    (((List.range body.argCount).map (· + 1)).filter (isTupleLocal body.localDecls))
    ((List.range body.localDecls.length).filter (isTupleLocal body.localDecls))
    (fun bb ti => termTupleInit body.localDecls
      (bb.statements.foldl (stmtTupleInit body.localDecls) ti) bb.terminator)
    (fun bb _ _ hsub _ hj => termTupleInit_mono body.localDecls
      (foldl_stmtTupleInit_mono body.localDecls bb.statements hsub) bb.terminator hj)
    (fun i hi => by
      obtain ⟨h1, h2, htup⟩ := hpost0 i hi
      exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨i - 1, List.mem_range.mpr (by omega), by omega⟩, htup⟩)
    (fun b hb hne i hi => by
      have htup := hpostO b hb hne i hi
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (isTupleLocal_lt htup), htup⟩)
    hpostEdge dst hdst

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

theorem LiveInv.advance_assume {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {op : Operand}
    {mem' : MirSemantics.Memory}
    (hlive : LiveInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .intrinsic (.assume op)) :
    LiveInv body (advanceStmt s (opPost s.frame.locals op) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [mustLiveBefore_succ hbb hst,
    show stmtMustLive (mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      mustLiveBefore body s.frame.blockIdx s.frame.stmtIdx by simp [stmtMustLive, hkind]] at hj
  intro hdead
  exact hlive j hj ((opPost_dead s.frame.locals op j).mp hdead)

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

theorem TupleInv.advance_assume {body : CapturedMir} {s : MachineState}
    {bb : BasicBlockData} {st : MirAst.Statement} {op : Operand}
    {mem' : MirSemantics.Memory}
    (htinv : TupleInv body s.frame) (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hkind : st.kind = .intrinsic (.assume op)) :
    TupleInv body (advanceStmt s (opPost s.frame.locals op) mem').frame := by
  intro j hj
  simp only [advanceStmt] at hj ⊢
  rw [tupleInitBefore_succ hbb hst,
    show stmtTupleInit body.localDecls
        (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) st =
      dropMovedFrom (tupleInitBefore body s.frame.blockIdx s.frame.stmtIdx) [op] by
      simp [stmtTupleInit, hkind]] at hj
  obtain ⟨hjOld, hnotMv⟩ := dropMovedFrom_mem hj
  have hget : (opPost s.frame.locals op)[j]? = s.frame.locals[j]? := by
    simpa [opsPost] using opsPost_get_of_not_mem s.frame.locals [op] j hnotMv
  rw [hget]
  exact htinv j hjOld

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
via `evalStatement_storageLive_init_cand` (lifted by `evalStatement_rethread`),
jumps to `bb0`, and when `callerFrames ≠ []`, preserves a stack depth of at
least `2` (`¬ ReturnRel`) at every intermediate step `j ≤ initLen body`. -/
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
    (hn : candBound + body.localDecls.length < 2 ^ 31)
    (hall : body.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true) :
    ∃ m0 lm,
      Interp.steps (initLen body) mInit = .ok m0 ∧
      Shape m0 rootCtx (callerFrames ++ [calleeFrameL f curCtx lm 0 0])
        m0.mem.memory.allocations ∧
      m0.prog = mInit.prog ∧ m0.fn_ptrs = mInit.fn_ptrs ∧
      LocalsOk body curCtx locals lm m0.mem.memory.allocations ∧
      (callerFrames ≠ [] → ∀ j ≤ initLen body, ∀ mj,
        Interp.steps j mInit = .ok mj → ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mj) := by
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
          (fun _ dj hdj =>
            scalarTypeOf_tyOf_of_isSome (List.all_eq_true.mp hall dj (List.mem_of_getElem? hdj)) _)
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
  have hm0Steps : Interp.steps (initLen body) mInit = .ok m0 := by
    rw [initLen, steps_add, hm, ok_bind, steps_one hstep]
  refine ⟨m0, lm, hm0Steps, ⟨rfl, rfl, rfl⟩, hprog, hfp, hlo, ?_⟩
  intro hne j hj mj hmj b' c' s' v
  rcases Nat.lt_or_eq_of_le hj with hjlt | rfl
  · obtain ⟨mk, lmk, hmk, hshk, _, _, _⟩ := key j (by rw [initLen] at hjlt; omega)
    rw [hmk] at hmj
    cases hmj
    exact hshk.not_returnRel_of_ne_nil hne
  · rw [hm0Steps] at hmj
    cases hmj
    exact hsh0'.not_returnRel_of_ne_nil hne

/-- Every `CallStackRel` frame prefix is non-empty: it begins with
`[rootCtx.caller]` at the root and appends one caller frame per suspended call. -/
theorem CallStackRel.frames_ne_nil {entry : CapturedMir} {callees : List CapturedMir}
    {fnMap : FnMap} {rootCtx : Ctx}
    {cs : List SavedCallerFrame} {cfs : List Frame} {curBody : CapturedMir}
    {curCtx : Ctx} {cb rf : Nat}
    (h : CallStackRel entry callees fnMap rootCtx cs cfs curBody curCtx cb rf) :
    cfs ≠ [] := by
  cases h <;> simp

/-- No `MultiStateRel`-related MiniRust machine can satisfy `ReturnRel`: a
running `MultiStateRel` machine always has at least two stack frames
(`callerFrames ++ [calleeFrameL ...]`, where `callerFrames ≠ []`), whereas
`ReturnRel` requires a single-frame stack `[{ ctx.caller with ... }]` after the
root callee has popped. -/
theorem MultiStateRel.not_returnRel {entry b' : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx c' : Ctx} {s s' : MachineState} {v : Value} {m : Mach}
    (hrel : MultiStateRel entry callees prog rootCtx s m) :
    ¬ ReturnRel b' c' s' v m := by
  obtain ⟨_, hrel⟩ := hrel
  obtain ⟨callerFrames, curCtx, curFn, curLm, _, _, _, curSeg, segStmt,
    _, _, hstack, _, _, _, _, hthr, _, _⟩ :=
    hrel.stack
  have hsh : Shape m rootCtx
      (callerFrames ++ [calleeFrameL curFn curCtx curLm curSeg segStmt])
      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
  exact hsh.not_returnRel_of_ne_nil hstack.frames_ne_nil

theorem MultiStepRel.tau1 {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s s' : MachineState} {m : Mach}
    (m' : Mach) (hm : Interp.step m = .ok m')
    (hrel : MultiStateRel entry callees prog rootCtx s' m') :
    MultiStepRel entry callees prog rootCtx s (.tau (.running s')) m := by
  refine ⟨1, m', Nat.le_refl 1, steps_one hm, hrel, ?_⟩
  intro j hj1 hj2 mj hmj b' c' s'' v
  have hj : j = 1 := by omega
  subst hj
  rw [steps_one hm] at hmj
  cases hmj
  exact hrel.not_returnRel

theorem MultiStepRel.tauK {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s s' : MachineState} {m : Mach}
    (k : Nat) (m' : Mach) (hk : 1 ≤ k) (hm : Interp.steps k m = .ok m')
    (hrel : MultiStateRel entry callees prog rootCtx s' m')
    (hnoRet : ∀ j, 1 ≤ j → j ≤ k → ∀ mj, Interp.steps j m = .ok mj →
      ∀ b' c' s'' v, ¬ ReturnRel b' c' s'' v mj) :
    MultiStepRel entry callees prog rootCtx s (.tau (.running s')) m :=
  ⟨k, m', hk, hm, hrel, hnoRet⟩

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
  | cons _ _ _ _ _ _ _ _ hPayloads => exact hPayloads

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
      (calleeRetDecl : LocalDecl) (callerBudget callerSeg callerSegStmt : Nat),
      callerFrames = preFrames ++ [curCtx.caller] ∧
      CallStackRel entry callees fnMap rootCtx restStack preFrames
        callerBody callerCtx callerCandBound (remFuel + 1) ∧
      savedCaller.callerBody = callerBody ∧
      callerBody ∈ entry :: callees ∧
      translateFnInProg fnMap callerBody = some callerFn ∧
      savedCaller.isDiverging = false ∧
      savedCaller.callerProtector = none ∧
      savedCaller.calleeProtectors = [] ∧
      savedCaller.returnTarget < callerBody.basicBlocks.length ∧
      curCtx.nextBlock = bbName savedCaller.returnTarget ∧
      curCtx.caller = calleeFrameL callerFn callerCtx callerLm callerSeg callerSegStmt ∧
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
  | cons hRest hCallerEq hCallerMem hCallerFn hNotDiv hProtNone hCalleeProts hTargetLt _
      hNextBlk hCallerFrame hCalleeRetDecl hDest hCallerCand hCallerBudget _ _
      hCallerBudgetLt hPostLen hPostStale hPostLive hPostTuple =>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, hRest, hCallerEq, hCallerMem, hCallerFn,
      hNotDiv, hProtNone, hCalleeProts, hTargetLt, hNextBlk, hCallerFrame, hCalleeRetDecl,
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

private theorem segPcZero_of_translateFnInProg {fnMap : FnMap} {body : CapturedMir}
    {f : Gen.Function} (hf : translateFnInProg fnMap body = some f) (t : Nat) :
    ∀ bb, body.basicBlocks[t]? = some bb →
      ∃ tbTerm nc1 nc2 ex1,
        translateTerminatorInProg fnMap body.layouts body.localDecls nc1 bb.terminator =
          some (tbTerm, nc2, ex1) ∧
        SegPc (mapGet f.blocks) body.localDecls body.layouts tbTerm t bb.statements 0 t 0 := by
  intro bb hbb
  obtain ⟨_, _, _, _, _, hBlocks⟩ := translateFnInProg_spec fnMap body f hf
  obtain ⟨tbTerm, nc1, nc2, ex1, htr, hseg⟩ := hBlocks t bb hbb
  exact ⟨tbTerm, nc1, nc2, ex1, htr, hseg.pcZero⟩

theorem MultiStateRelAt.advance {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {rootCtx : Ctx} {s : MachineState}
    {view : List LocalSlot} {m : Mach}
    (hrel : MultiStateRelAt entry callees prog rootCtx s view m)
    {bb : BasicBlockData}
    (hbb : (s.memory.activeCallee.getD entry).basicBlocks[s.frame.blockIdx]? = some bb)
    (hlt : s.frame.stmtIdx < bb.statements.length)
    {callerFrames : List Frame} {curCtx : Ctx} {curFn : Gen.Function}
    {lm' : Map Gen.LocalName Ptr} {candBound remFuel curBudget curSeg' segStmt' : Nat}
    (hcurMem : (s.memory.activeCallee.getD entry) ∈ entry :: callees)
    (hcurFn : translateFnInProg (fnNameMap entry callees) (s.memory.activeCallee.getD entry) =
      some curFn)
    (hstack : CallStackRel entry callees (fnNameMap entry callees) rootCtx s.memory.callStack
      callerFrames (s.memory.activeCallee.getD entry) curCtx candBound remFuel)
    (hpay : curCtx.payloads = rootCtx.payloads)
    (hcand : BaseCandBounded curCtx.base candBound)
    (hbud : maxStackLocalsAux remFuel callees (s.memory.activeCallee.getD entry) = some curBudget)
    (hbudLt : candBound + curBudget < 2 ^ 31)
    (hsegNext : ∃ tbTerm nc1 nc2 ex1,
      translateTerminatorInProg (fnNameMap entry callees)
        (s.memory.activeCallee.getD entry).layouts
        (s.memory.activeCallee.getD entry).localDecls nc1 bb.terminator =
        some (tbTerm, nc2, ex1) ∧
      SegPc (mapGet curFn.blocks) (s.memory.activeCallee.getD entry).localDecls
        (s.memory.activeCallee.getD entry).layouts tbTerm
        s.frame.blockIdx bb.statements (s.frame.stmtIdx + 1) curSeg' segStmt')
    (actual' view' : List LocalSlot) (mem' : MirSemantics.Memory) (m' : Mach)
    (hthr : m'.threads =
      [thread1 rootCtx
        (callerFrames ++ [calleeFrameL curFn curCtx lm' curSeg' segStmt'])])
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
  refine ⟨callerFrames, curCtx, curFn, lm', candBound, remFuel, curBudget, curSeg', segStmt', ?_⟩
  simp only [advanceStmt, hac, hcs]
  refine ⟨hcurMem, hcurFn, hstack, hpay, hcand, hbud, hbudLt, hthr, fun bb' hbb' => ?_, hlo⟩
  rw [hbb] at hbb'
  cases hbb'
  exact hsegNext

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
    stack := ⟨callerFrames, curCtx, curFn, lm, candBound, remFuel, curBudget, t, 0,
      hcurMem, hcurFn, hstack, hpay, hcand, hbud, hbudLt, hthr,
      segPcZero_of_translateFnInProg hcurFn t, hlo⟩
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
    (htr : translateTerminatorInProg fnMap curBody.layouts curBody.localDecls nc1 bb.terminator =
      some (tbTerm, nc2, ex1)) :
    ∃ func argOps destination targetBb unwind dp callee calleeRetDecl restDecls
        fn conv argExprs retExpr unwindBb,
      bb.terminator.kind = .call func argOps destination (some targetBb) unwind ∧
      extractFnDefPath func = some dp ∧
      monoCallee? callees func dp = some callee ∧
      MirSemantics.findCallee? callees dp = some callee ∧
      callee.localDecls = calleeRetDecl :: restDecls ∧
      targetBb < curBody.basicBlocks.length ∧
      argOps.length = callee.argCount ∧
      callee.argCount ≤ restDecls.length ∧
      callArgsOk curBody.layouts curBody.localDecls (restDecls.take callee.argCount) argOps = true ∧
      callDestOk curBody.localDecls (mustLiveBefore curBody blk bb.statements.length)
        (tupleInitBefore curBody blk bb.statements.length) calleeRetDecl destination = true ∧
      (∀ op ∈ argOps, opRead op ≠ some destination.local_) ∧
      lookupFnTarget fnMap dp = some (fn, conv) ∧
      lookupFnName fnMap dp = some fn ∧
      argOps.mapM (translateCallArg curBody.localDecls) = some argExprs ∧
      translatePlace curBody.localDecls destination = some retExpr ∧
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
        cases hintr : translateIntrinsicOrNone curBody.localDecls dp argOps destination (some targetBb) with
        | some _ => simp [hextr, hintr] at hok
        | none =>
          cases hmono : monoCallee? callees func dp with
          | none => simp [hextr, hintr, hmono] at hok
          | some callee =>
            have hfind : MirSemantics.findCallee? callees dp = some callee :=
              (monoCallee?_eq_some_iff.mp hmono).1
            cases hcd : callee.localDecls with
          | nil => simp [hextr, hintr, hmono, hcd] at hok
          | cons calleeRetDecl restDecls =>
            simp only [hextr, hintr, hmono, hcd, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true, bne_iff_ne] at hok
            obtain ⟨⟨⟨⟨⟨⟨⟨htgtLt, _⟩, _⟩, hArgLen⟩, hArgBound⟩, hArgsOk⟩, hDestOk⟩, hNotDst⟩ := hok
            simp only [translateTerminatorInProg, htk, hextr, Option.bind_eq_bind,
              Option.bind_some] at htr
            simp only [hintr] at htr
            cases hlk : lookupFnTarget fnMap dp with
            | none => simp [hlk] at htr
            | some fnConv =>
              obtain ⟨fn, conv⟩ := fnConv
              cases htrArgs : argOps.mapM (translateCallArg curBody.localDecls) with
              | none => simp [hlk, htrArgs] at htr
              | some argExprs =>
                cases hretTr : translatePlace curBody.localDecls destination with
                | none => simp [hlk, htrArgs, hretTr] at htr
                | some retExpr =>
                  simp [hlk, htrArgs, hretTr] at htr
                  obtain ⟨rfl, _, _⟩ := htr
                  exact ⟨func, argOps, destination, targetBb, unwind, dp, callee, calleeRetDecl,
                    restDecls, fn, conv, argExprs, retExpr, (translateUnwindAction nc1 unwind).1,
                    rfl, hextr, hmono, hfind, hcd, htgtLt, hArgLen, hArgBound, hArgsOk, hDestOk,
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
  obtain ⟨callerFrames, curCtx, curFn, curLm, candBound, remFuel, curBudget, curSeg, segStmt,
    hCurMem, hCurFn, hStackRel, hCurPay, hCurCand, hCurBud, hCandBudLt, hthr, hSegPcAll, hlo⟩ :=
    hrel.stack
  obtain ⟨hphase, hargs, _, _, hbbs, hsdOk, hmvOk, hmtOk, hlvOk, htiOk⟩ :=
    bodyInProgFragment_spec (hallFrag curBody hCurMem)
  obtain ⟨hfCur, _, _, _, _, _⟩ := translateFnInProg_spec fnMap curBody curFn hCurFn
  obtain ⟨curBodyLenLe, _⟩ := maxStackLocalsAux_ge hCurBud
  have curBodyLenLe' : curBody.localDecls.length ≤ curBudget := curBodyLenLe
  have hCandCurLt : candBound + curBody.localDecls.length < 2 ^ 31 := by omega
  obtain ⟨bb, hbb⟩ : ∃ bb, curBody.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hrel.blk⟩
  have hbbmem : bb ∈ curBody.basicBlocks := List.mem_of_getElem? hbb
  obtain ⟨_, hstmts, htermOr⟩ := hbbs s.frame.blockIdx bb hbb
  obtain ⟨tbTerm, nc1, nc2, ex1, htermTr, hpc⟩ := hSegPcAll bb hbb
  obtain ⟨hmvS, hmvT, hmvEdge⟩ := movesOk_spec hmvOk hbb
  have hshape : Shape m rootCtx
      (callerFrames ++ [calleeFrameL curFn curCtx curLm curSeg segStmt])
      m.mem.memory.allocations := ⟨hthr, hrel.active, rfl⟩
  let mR := rethread (resetPick m) curCtx
    [curCtx.caller, calleeFrameL curFn curCtx curLm curSeg segStmt]
  have hallSc := bodyInProgFragment_allScalar (hallFrag curBody hCurMem)
  have hframe : FrameOk curBody curFn curCtx view curLm mR curSeg segStmt :=
    ⟨hfCur, ⟨rfl, rfl, rfl⟩, hlo,
      fun d hd => by simp [localDeclOk, List.all_eq_true.mp hallSc d hd],
      fun _ d _ hd _ hnone _ => by
        have := List.all_eq_true.mp hallSc d (List.mem_of_getElem? hd)
        simp [hnone] at this⟩
  have hscOf : ∀ (b : CapturedMir), b ∈ entry :: callees → ∀ (j : Nat) (dj : LocalDecl),
      b.localDecls[j]? = some dj → ∃ T, scalarTypeOf dj.ty = some T := fun b hb j dj hdj =>
    Option.isSome_iff_exists.mp
      (List.all_eq_true.mp (bodyInProgFragment_allScalar (hallFrag b hb)) dj
        (List.mem_of_getElem? hdj))
  have hnoPtr : ∀ (j : Nat) (dj : LocalDecl), curBody.localDecls[j]? = some dj →
      ptrPointeeOf dj.ty = none := by
    intro j dj hdj
    obtain ⟨T, hT⟩ := hscOf curBody hCurMem j dj hdj
    have h := isPtrTy_false_of_scalarTypeOf hT
    cases hp : ptrPointeeOf dj.ty with
    | none => rfl
    | some _ => simp [isPtrTy, hp] at h
  have hslotOf : ∀ {L : Layout.LayoutTable} {dj : LocalDecl} {slot : LocalSlot} {T : Gen.Type},
      scalarTypeOf dj.ty = some T → DeclSlotOk dj slot L → SlotOk (tyOf dj) slot := by
    intro L dj slot T hT h
    have h' := (DeclSlotOk_of_scalarTypeOf (layouts := L) hT slot).mp h
    rwa [tyOf_of_scalarTypeOf (layouts := L) hT,
      ← tyOf_of_scalarTypeOf (layouts := ⟨64, true, []⟩) hT] at h'
  have hslotsA : SlotsOk curBody.layouts curBody.localDecls s.frame.locals :=
    hrel.stale.slots hlo.slots
  have hnA : s.frame.locals.length = curBody.localDecls.length := hrel.stale.1.trans hlo.nlocals
  have hstmt_le := hrel.stmt bb hbb
  rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with hlt | hge
  · ----------------------------------------------------------------- statement
    obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hstmem : st ∈ bb.statements := List.mem_of_getElem? hst
    rw [stepMirFn_active_stmt entry curBody s bb st rfl hphase hbb hst]
    have hprogOk := hstmts st hstmem
    have hreads := hmvS _ st hst
    cases hAss : isAssume st with
    | true =>
      obtain ⟨op, hkind⟩ : ∃ op, st.kind = .intrinsic (.assume op) := by
        obtain ⟨k, sp⟩ := st
        cases k with
        | intrinsic intr =>
          cases intr with
          | assume op => exact ⟨op, rfl⟩
          | copyNonOverlapping _ _ _ => simp [isAssume] at hAss
        | _ => simp [isAssume] at hAss
      obtain ⟨segStmts, op', nextSeg, hgetb, hsegEq, hopTr, hpcNext⟩ :=
        hpc.atStmt_assume hst hkind
      let tb : Gen.BasicBlock :=
        ⟨segStmts, .Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg)), .Regular⟩
      have hif : ((segStmt : Nat) : Int) = (tb.statements.length : Int) := by
        simp [tb, hsegEq]
      have hokB : operandOkB curBody.layouts curBody.localDecls (copyOp op) = true :=
        progStatementOk_assume hprogOk hkind
      have hreadsOp : readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx) [op] = true := by
        simpa [stmtReadsOk, hkind] using hreads
      have hsimple : simpleOp op = true := (readsOk_spec hreadsOp op (by simp)).1
      have hbitsEq : opBits s.frame.locals (copyOp op) = opBits view (copyOp op) :=
        opBits_frame _ (by
          rw [opLocals_copyOp]
          exact fun j hj => hrel.stale.agree ((readsOk_spec hreadsOp op (by simp)).2 j hj))
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      obtain ⟨hAnone, hA0, hA1⟩ := evalStmt_assume_anneal s curBody.localDecls curBody.layouts
        op span hslotsA hnA hsimple hokB
      obtain ⟨hMnone, hM0, hM1⟩ := evalTerminator_assume_spec (m := resetPick m)
        (nextSeg := nextSeg) (resetPick_shape hshape) hframe hokB hopTr
      cases hb : opBits view (copyOp op) with
      | none =>
        rw [hAnone (hbitsEq.trans hb)]
        obtain ⟨msg, hmsg⟩ := hMnone hb
        have hstep : Interp.step m = .error (.ub msg) := by
          rw [step_callee_stack hshape tb hgetb]
          simp [hif, tb, hmsg]
        exact MultiStepRel.ub' msg hstep
      | some bits =>
        by_cases hb0 : bits = 0
        · subst hb0
          rw [hA0 (hbitsEq.trans hb)]
          have hmsg := hM0 hb
          have hstep : Interp.step m =
              .error (.ub "`Assume` intrinsic called on condition that is violated") := by
            rw [step_callee_stack hshape tb hgetb]
            simp [hif, tb, hmsg]
          exact MultiStepRel.ub' _ hstep
        · have hvbits : ValidBits .Bool bits :=
            ((evalValue_operandT hframe (.bool : FragTy .Bool u8Ty) (copyOp op)
              (operandOkB_T hokB) op'
              (by rw [translateOperand_copyOp]; exact hopTr)).1 bits hb).1
          simp only [ValidBits] at hvbits
          have hb1 : bits = 1 := by omega
          subst hb1
          rw [hA1 (hbitsEq.trans hb)]
          obtain ⟨m4, hm4, hsh4, hp4, hfp4, hlo4⟩ := hM1 1 hb hb0
          have hstep : Interp.step m = .ok m4 := by
            rw [step_callee_stack hshape tb hgetb]
            simp [hif, tb, hm4, check_after hsh4]
          exact MultiStepRel.tau1 m4 hstep
            (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
              ⟨tbTerm, nc1, nc2, ex1, htermTr, hpcNext⟩ _ view _ m4 hsh4.threads hsh4.active
              hp4 hfp4 hlo4 (hrel.stale.assume hbb hst rfl) hrel.retLive
              (hrel.liveInv.advance_assume hbb hst rfl)
              (hrel.tupleInv.advance_assume hbb hst rfl)
              rfl hrel.borrows rfl rfl rfl rfl)
    | false =>
    have hok : statementOk curBody.localDecls st curBody.layouts = true := progStatementOk_notAssume hprogOk hAss
    obtain ⟨tb, st', hgetb, hsegLt, htst, hst', hpcNext⟩ := hpc.atStmt_notAssume hst hAss
    have hne : ((segStmt : Nat) : Int) ≠ (tb.statements.length : Int) := by omega
    rcases translateStatement_some hst' with
      ⟨dst, rv, pe, e, hkind, hpe, he, rfl⟩ | ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨i, hkind, rfl⟩ | ⟨i, hkind, rfl⟩ | ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨retagKind, p, pe, hkind, hpe, rfl⟩
    · ------------------------------------------------------------ assign
      obtain ⟨i, projs⟩ := dst
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      obtain ⟨d, hdi⟩ : ∃ d, curBody.localDecls[i]? = some d := by
        cases hdi : curBody.localDecls[i]? with
        | none =>
          exfalso
          cases projs with
          | nil => simp [statementOk, hdi] at hok
          | cons ph pt => cases ph <;> cases pt <;> simp [statementOk, hdi] at hok
        | some d => exact ⟨d, rfl⟩
      obtain ⟨Td, hTd⟩ := hscOf curBody hCurMem i d hdi
      -- the multi-function fragment is scalar-only: no projected destinations
      obtain rfl : projs = [] := by
        cases projs with
        | nil => rfl
        | cons ph pt =>
          exfalso
          have hpn : ptrPointeeOf d.ty = none := hnoPtr i d hdi
          have han : arrayTypeOf d.ty = none := arrayTypeOf_none_of_scalarTypeOf hTd
          have htn : tupleTypeOf curBody.layouts d.ty = none :=
            tupleTypeOf_none_of_scalarTypeOf hTd
          cases ph <;> cases pt <;> simp [statementOk, hdi, hpn, han, htn] at hok
      simp only [translatePlace, Option.some.injEq] at hpe
      subst hpe
      have hal : i ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (local_mem_stmtLocals_assign ⟨i, []⟩ rv span)
      have hi : i < s.frame.locals.length := by
        rw [hnA]; exact (List.getElem?_eq_some_iff.mp hdi).1
      have hpmir : placeMirTy curBody.localDecls ⟨i, []⟩ = some d.ty := by
        simp [placeMirTy, hdi, resolveProjTy]
      rw [hpmir] at he
      have hpdr : ∀ it, ptrDerefReadOk curBody.localDecls it (copyRv rv) = false := by
        intro it
        unfold ptrDerefReadOk
        split
        · next p heq =>
          cases hdp : curBody.localDecls[p]? with
          | none => simp
          | some dp => simp [hnoPtr p dp hdp]
        · rfl
      simp only [statementOk] at hok
      obtain ⟨res, hk, hmf, hreadsMo, hMok, hMnone, hAok, hAnone⟩ : ∃ res : Option Value,
          moveKind rv = true ∧
          MoveFrameOk s.frame.locals rv s.memory curBody.localDecls curBody.layouts ∧
          readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx) (rvOperands rv) = true ∧
          (∀ v, res = some v → view[i]? ≠ some .dead →
            ∃ m3R, evalStatement mR (.Assign (.Local (localName i)) e) = .ok m3R ∧
              FrameOk curBody curFn curCtx (view.set i (.init v)) curLm m3R curSeg segStmt) ∧
          (res = none → view[i]? ≠ some .dead →
            ∃ msg, evalStatement mR (.Assign (.Local (localName i)) e) = .error (.ub msg)) ∧
          (∀ v, res = some v →
            evalRvalue s.frame.locals (copyRv rv) s.memory curBody.localDecls curBody.layouts =
              .ok v s.frame.locals s.memory) ∧
          (res = none →
            evalRvalue s.frame.locals (copyRv rv) s.memory curBody.localDecls curBody.layouts =
              .ub) := by
        cases hb : isBoolTy d.ty with
        | true =>
          have hit : itOf d curBody.layouts = u8Ty := (tyOf_bool hb).2
          have hokB : rvalueOkB curBody.layouts curBody.localDecls (copyRv rv) = true := by
            simpa [hdi, hb] using hok
          have hreadsMo : readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx)
              (rvOperands rv) = true := by
            rw [← stmtReadsOk_root_of_not_deref (span := span) (i := i)
              (by rintro m q rfl; simp [copyRv, rvalueOkB] at hokB)
              (by rintro bk q rfl; simp [copyRv, rvalueOkB] at hokB)
              (by intro p rest h; rw [h] at hokB; simp [rvalueOkB, operandOkB] at hokB)]
            exact hreads
          have hagree := hrel.stale.readsAgree hreadsMo
          have hfr : rvBitsB curBody.localDecls s.frame.locals (copyRv rv) curBody.layouts =
              rvBitsB curBody.localDecls view (copyRv rv) curBody.layouts := rvBitsB_frame hagree
          obtain ⟨hA1, hA2⟩ := evalRvalue_fragB curBody.localDecls s.frame.locals hslotsA hnA
            (copyRv rv) hokB s.memory
          refine ⟨(rvBitsB curBody.localDecls view (copyRv rv) curBody.layouts).map
              (fun r => .scalar ⟨r, (itOf d curBody.layouts).size.bytes⟩),
            moveKind_of_rvalueOkB hokB,
            moveFrameOk_of_rvalueOkB hokB hslotsA hnA s.memory,
            hreadsMo, ?_, ?_, ?_, ?_⟩
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
            have hit : itOf d curBody.layouts = u8Ty := (tyOf_ordering ho).2
            have hokO : rvalueOkO curBody.layouts curBody.localDecls (copyRv rv) = true := by
              simpa [hdi, hb, ho] using hok
            have hreadsMo : readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx)
                (rvOperands rv) = true := by
              rw [← stmtReadsOk_root_of_not_deref (span := span) (i := i)
                (by rintro m q rfl; simp [copyRv, rvalueOkO] at hokO)
                (by rintro bk q rfl; simp [copyRv, rvalueOkO] at hokO)
                (by intro p rest h; rw [h] at hokO; simp [rvalueOkO, operandOkO] at hokO)]
              exact hreads
            have hagree := hrel.stale.readsAgree hreadsMo
            have hfr : rvBitsO curBody.localDecls s.frame.locals (copyRv rv) curBody.layouts =
                rvBitsO curBody.localDecls view (copyRv rv) curBody.layouts := rvBitsO_frame hagree
            obtain ⟨hA1, hA2⟩ := evalRvalue_fragO curBody.localDecls s.frame.locals hslotsA hnA
              (copyRv rv) hokO s.memory
            refine ⟨(rvBitsO curBody.localDecls view (copyRv rv) curBody.layouts).map
                (fun r => .scalar ⟨r, (itOf d curBody.layouts).size.bytes⟩),
              moveKind_of_rvalueOkO hokO,
              moveFrameOk_of_rvalueOkO hokO s.frame.locals s.memory,
              hreadsMo, ?_, ?_, ?_, ?_⟩
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
            cases htup : intBoolTupleOf d.ty with
            | some it =>
              have hitd : itOf d curBody.layouts = it := (tyOf_tuple htup).2
              have htup' : intBoolTupleOf d.ty = some (itOf d curBody.layouts) := by
                rw [hitd]; exact htup
              have hokT : rvalueOkTuple curBody.layouts curBody.localDecls (itOf d curBody.layouts)
                  (copyRv rv) = true := by
                rw [hitd]; simpa [hdi, hb, ho, htup] using hok
              have hreadsMo : readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx)
                  (rvOperands rv) = true := by
                rw [← stmtReadsOk_root_of_not_deref (span := span) (i := i)
                  (by rintro m q rfl; simp [copyRv, rvalueOkTuple] at hokT)
                  (by rintro bk q rfl; simp [copyRv, rvalueOkTuple] at hokT)
                  (by intro p rest h; rw [h] at hokT; simp [rvalueOkTuple, operandOkTuple] at hokT)]
                exact hreads
              have hagree := hrel.stale.readsAgree hreadsMo
              have hgood := hframe.decl_good i d hdi
              have hfr : rvTupleBits s.frame.locals (itOf d curBody.layouts) (copyRv rv) =
                  rvTupleBits view (itOf d curBody.layouts) (copyRv rv) := rvTupleBits_frame hagree
              obtain ⟨hA1, hA2⟩ := evalRvalue_fragTuple curBody.localDecls s.frame.locals hslotsA
                hnA (itOf d curBody.layouts) hgood (copyRv rv) hokT s.memory
              refine ⟨(rvTupleBits view (itOf d curBody.layouts) (copyRv rv)).map
                  (fun pr => .aggregate 0
                    [.scalar ⟨pr.1, (itOf d curBody.layouts).size.bytes⟩, .scalar ⟨pr.2, 1⟩]),
                moveKind_of_rvalueOkTuple hokT,
                moveFrameOk_of_rvalueOkTuple hokT s.frame.locals s.memory,
                hreadsMo, ?_, ?_, ?_, ?_⟩
              · intro v hv hlive
                obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
                exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv)
                  hokT e he).1 bits b hpb
              · intro hv hlive
                exact (evalStatement_assignTuple hframe i d hdi hlive htup' (copyRv rv)
                  hokT e he).2 (Option.map_eq_none_iff.mp hv)
              · intro v hv
                obtain ⟨⟨bits, b⟩, hpb, rfl⟩ := Option.map_eq_some_iff.mp hv
                exact hA1 bits b (hfr.trans hpb)
              · intro hv
                exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
            | none =>
              cases hit : intTypeOf d.ty with
              | none =>
                exfalso
                rcases scalarTypeOf_cases hTd with ⟨hb', _⟩ | ⟨it, hit', _⟩ | ⟨ho', _⟩ |
                  ⟨it, htup', _⟩
                · rw [hb] at hb'; cases hb'
                · rw [hit] at hit'; cases hit'
                · rw [ho] at ho'; cases ho'
                · rw [htup] at htup'; cases htup'
              | some it =>
                have hitd : itOf d curBody.layouts = it := (tyOf_int hit).2
                have hok' : rvalueOk curBody.layouts curBody.localDecls (itOf d curBody.layouts)
                    (copyRv rv) = true := by
                  rw [hitd]; simpa [hdi, hb, ho, htup, hit, hpdr] using hok
                have hint : intTypeOf d.ty = some (itOf d curBody.layouts) := by
                  rw [hitd]; exact hit
                have hreadsMo : readsOk (movedBefore curBody s.frame.blockIdx s.frame.stmtIdx)
                    (rvOperands rv) = true := by
                  rw [← stmtReadsOk_root_of_not_deref (span := span) (i := i)
                    (by rintro m q rfl; simp [copyRv, rvalueOk] at hok')
                    (by rintro bk q rfl; simp [copyRv, rvalueOk] at hok')
                    (by
                      intro p rest h; rw [h] at hok'
                      cases hdp : curBody.localDecls[p]? with
                      | none => cases rest <;> simp [rvalueOk, operandOk, placeOk, hdp] at hok'
                      | some dp =>
                        obtain ⟨Tp, hTp⟩ := hscOf curBody hCurMem p dp hdp
                        cases rest <;> simp [rvalueOk, operandOk, placeOk, hdp,
                          arrayTypeOf_none_of_scalarTypeOf hTp] at hok')]
                  exact hreads
                have hagree := hrel.stale.readsAgree hreadsMo
                have hgood := hframe.decl_good i d hdi
                have hfr : rvBits curBody.localDecls s.frame.locals (itOf d curBody.layouts)
                    curBody.layouts (copyRv rv) =
                    rvBits curBody.localDecls view (itOf d curBody.layouts) curBody.layouts
                      (copyRv rv) := rvBits_frame hagree
                have hnsOps : OpsNonScalarInit curBody.localDecls s.frame.locals
                    (rvOperands (copyRv rv)) := (hframe.nonScalar.opsInit_of_readsAgree hagree).copy
                obtain ⟨hA1, hA2⟩ := evalRvalue_frag curBody.localDecls s.frame.locals hslotsA
                  hnA (itOf d curBody.layouts) hgood (copyRv rv) hok' hnsOps s.memory
                refine ⟨(rvBits curBody.localDecls view (itOf d curBody.layouts) curBody.layouts
                    (copyRv rv)).map (fun r => .scalar ⟨r, (itOf d curBody.layouts).size.bytes⟩),
                  moveKind_of_rvalueOk hok',
                  moveFrameOk_of_rvalueOk hok' s.frame.locals s.memory,
                  hreadsMo, ?_, ?_, ?_, ?_⟩
                · intro v hv hlive
                  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                  exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv)
                    hok' e he).1 r hr
                · intro hv hlive
                  exact (evalStatement_assign hframe i d hdi hlive hint (copyRv rv)
                    hok' e he).2 (Option.map_eq_none_iff.mp hv)
                · intro v hv
                  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hv
                  exact hA1 r (hfr.trans hr)
                · intro hv
                  exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
      have hr0 : readsOk [] (rvOperands rv) = true :=
        readsOk_mono (fun _ h => by simp at h) hreadsMo
      obtain ⟨hA1, hA2⟩ := evalStmt_assign_move s curBody.localDecls curBody.layouts i rv span
        hk hr0 hi (fun b hb => by rw [hrel.borrows] at hb; cases hb) hrel.protectors hmf
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
            hslotOf hTd (hlo4.slots i d (.init v) hdi (List.getElem?_set_self hvil))
          exact MultiStepRel.tau1 m4 hstep
            (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
              ⟨tbTerm, nc1, nc2, ex1, htermTr, hpcNext⟩ _ (view.set i (.init v)) _ m4
              hsh4.threads hsh4.active hp4 hfp4 hlo4
              (hrel.stale.assign hbb hst rfl (.init v))
              (retLive_set hrel.retLive i (by simp))
              (hrel.liveInv.advance_assign hbb hst rfl)
              (hrel.tupleInv.advance_assign hbb hst rfl hdi hi hvOk)
              rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ placeMention
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      have hpOk : mentionPlaceOk curBody.layouts curBody.localDecls p = true := by
        simpa [statementOk] using hok
      have hal : p.local_ ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simpa [stmtLocals] using local_mem_placeLocals p)
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
            ⟨tbTerm, nc1, nc2, ex1, htermTr, hpcNext⟩ _ view _ m4
            hsh4.threads hsh4.active hp4 hfp4 hlo4
            (hrel.stale.keep hbb hst rfl) hrel.retLive
            (hrel.liveInv.advance_placeMention hbb hst rfl)
            (hrel.tupleInv.advance_placeMention hbb hst rfl)
            rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ storageLive
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      have hin : i < curBody.localDecls.length := by
        simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
      have hal : i ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      obtain ⟨d, hd⟩ : ∃ d, curBody.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageLive s curBody.localDecls curBody.layouts i span hi
        (fun b hb => by rw [hrel.borrows] at hb; cases hb)]
      obtain ⟨m3R, lm3, hm3R, h3⟩ :=
        evalStatement_storageLive_cand hframe i d hd hal
          (.inl (List.all_eq_true.mp hallSc d (List.mem_of_getElem? hd))) hCurCand hCandCurLt
      obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
        lift_stmt_ok hshape hgetb hne htst hm3R h3
      exact MultiStepRel.tau1 m4 hstep
        (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
          ⟨tbTerm, nc1, nc2, ex1, htermTr, hpcNext⟩ _ (view.set i .uninit) _ m4
          hsh4.threads hsh4.active hp4 hfp4 hlo4
          (hrel.stale.setBoth hbb hst rfl .uninit)
          (retLive_set hrel.retLive i (by simp))
          (hrel.liveInv.advance_storageLive hbb hst rfl hi)
          (hrel.tupleInv.advance_clear hbb hst (by simp [stmtTupleInit]))
          rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ storageDead
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      have hin : i < curBody.localDecls.length := by
        simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
      have hal : i ∉ alwaysStorageLiveLocals curBody :=
        mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals])
      have hi0 : curBody.argCount < i := storageDeadOk_spec hsdOk hbbmem hstmem rfl
      obtain ⟨d, hd⟩ : ∃ d, curBody.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
      have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
      rw [evalStmt_storageDead s curBody.localDecls curBody.layouts i span hi
        (fun b hb => by rw [hrel.borrows] at hb; cases hb)]
      obtain ⟨m3R, hm3R, h3⟩ := evalStatement_storageDead hframe i d hd hal
        (.inl (List.all_eq_true.mp hallSc d (List.mem_of_getElem? hd)))
      obtain ⟨m4, hstep, hsh4, hp4, hfp4, hlo4⟩ :=
        lift_stmt_ok hshape hgetb hne htst hm3R h3
      exact MultiStepRel.tau1 m4 hstep
        (hrel.advance hbb hlt hCurMem hCurFn hStackRel hCurPay hCurCand hCurBud hCandBudLt
          ⟨tbTerm, nc1, nc2, ex1, htermTr, hpcNext⟩ _ (view.set i .dead) _ m4
          hsh4.threads hsh4.active hp4 hfp4 hlo4
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
        have hin : i < curBody.localDecls.length := by
          simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
        simp only [translatePlace, Option.some.injEq] at hpe; subst hpe
        have hal : i ∉ alwaysStorageLiveLocals curBody :=
          mentionsOk_stmt hmtOk hbbmem hstmem (by simp [stmtLocals, placeLocals])
        obtain ⟨d, hd⟩ : ∃ d, curBody.localDecls[i]? = some d := ⟨_, List.getElem?_eq_getElem hin⟩
        have hi : i < s.frame.locals.length := by rw [hnA]; exact hin
        obtain ⟨hMlive, hMdead⟩ := evalStatement_deinit hframe i d hd
          (.inl (List.all_eq_true.mp hallSc d (List.mem_of_getElem? hd)))
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
              ⟨tbTerm, nc1, nc2, ex1, htermTr, hpcNext⟩ _ (view.set i .uninit) _ m4
              hsh4.threads hsh4.active hp4 hfp4 hlo4
              (hrel.stale.setBoth hbb hst rfl .uninit)
              (retLive_set hrel.retLive i (by simp))
              (hrel.liveInv.advance_deinit hbb hst rfl)
              (hrel.tupleInv.advance_clear hbb hst (by simp [stmtTupleInit]))
              rfl hrel.borrows rfl rfl rfl rfl)
    · ------------------------------------------------------------ retag
      -- outside the scalar-only multi-function fragment: retags need a pointer local
      exfalso
      obtain ⟨kind, span⟩ := st
      simp only at hkind; subst hkind
      obtain ⟨i, di, _, _, rfl, _, hdi, hpt⟩ := statementOk_retag_spec hok
      rw [hnoPtr i di hdi] at hpt
      cases hpt
  · ----------------------------------------------------------------- terminator
    have heq : s.frame.stmtIdx = bb.statements.length := by omega
    obtain ⟨tbStmts, hgetb, hsegEq⟩ := hpc.atEnd heq
    let tb : Gen.BasicBlock := ⟨tbStmts, tbTerm, .Regular⟩
    have hif : ((segStmt : Nat) : Int) = (tb.statements.length : Int) := by
      simp [tb, hsegEq]
    rw [stepMirFn_active_term entry curBody s bb rfl hphase hbb heq]
    have hstale_end : StaleOk curBody s.frame.locals view s.frame.blockIdx bb.statements.length := by
      rw [← heq]; exact hrel.stale
    rcases htermOr with hterm | hcallOk
    · ----------------------------------------------------- non-call terminators
      have htermspec : translateTerminator curBody.layouts curBody.localDecls bb.terminator = some tb.terminator := by
        cases htk : bb.terminator.kind with
        | call _ _ _ _ _ => simp [terminatorOk, htk] at hterm
        | _ =>
          change translateTerminatorInProg fnMap curBody.layouts curBody.localDecls nc1 bb.terminator =
            some (tbTerm, nc2, ex1) at htermTr
          simp only [translateTerminatorInProg, htk, Option.bind_eq_bind] at htermTr
          cases ht : translateTerminator curBody.layouts curBody.localDecls bb.terminator with
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
            rw [opLocals_copyOp]
            exact fun j hj => hstale_end.agree ((readsOk_spec hreadsD discr (by simp)).2 j hj))
        obtain ⟨hAok, hAnone⟩ := evalRelOperand_frag curBody.localDecls s.frame.locals hslotsA hnA
          (copyOp discr) hokT s.memory.borrows s.memory.globals s.memory.callerLocals
        have hdeq := evalOperand_decls_eq_nil_of_RelOperandOk curBody.localDecls s.frame.locals
          (copyOp discr) hokT s.memory.borrows s.memory.globals s.memory.callerLocals
        have hmove := evalOperand_move s.frame.locals discr hsimple s.memory.borrows
          s.memory.globals curBody.layouts s.memory.callerLocals []
        obtain ⟨hvOkRe, hvErrRe⟩ := evalValue_rethread vExpr (resetPick m) rootCtx curCtx
          callerFrames (calleeFrameL curFn curCtx curLm curSeg segStmt)
          hshape.threads rfl
        cases hb : opBits view (copyOp discr) with
        | none =>
          have hA : MirSemantics.evalTerminator s bb.terminator (some curBody) =
              MirStepNode.fail .ub := by
            simp [MirSemantics.evalTerminator, hk, hmove, hdeq, hAnone (hbitsEq.trans hb),
              opWithLocals]
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
              (callerFrames ++ [calleeFrameL curFn curCtx curLm curSeg segStmt])
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
            simp [MirSemantics.evalTerminator, hk, hmove, hdeq, hAok bits (hbitsEq.trans hb),
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
              [rootCtx.caller, calleeFrameL curFn rootCtx curLm curSeg segStmt]
              m.mem.memory.allocations := by
            simpa [hcfEq, hCtxEq] using hshape
          have hloRoot : LocalsOk curBody rootCtx view curLm m.mem.memory.allocations :=
            hCtxEq ▸ hlo
          have hd0Entry : entry.localDecls[0]? = some d0 := hCurEq ▸ hd0
          obtain ⟨r0, a0, hp, hr0, hliveR, haddrr, hlenr, halr⟩ := hRetRoot d0 hd0Entry
          have hframeRoot : FrameOk curBody curFn rootCtx view curLm (resetPick m)
              curSeg segStmt :=
            ⟨hfCur, resetPick_shape hshapeRoot, hloRoot,
              fun d hd => by simp [localDeclOk, List.all_eq_true.mp hallSc d hd],
              fun _ d _ hd _ hnone _ => by
                have := List.all_eq_true.mp hallSc d (List.mem_of_getElem? hd)
                simp [hnone] at this⟩
          have hsc0 : (scalarTypeOf d0.ty).isSome = true :=
            List.all_eq_true.mp hallSc d0 (List.mem_of_getElem? hd0)
          have hRet := evalReturn_frame hframeRoot d0 hd0 hsc0 r0 a0 hp hr0 hliveR haddrr
            (by rw [tyOf_scalar_layouts hsc0 curBody.layouts ⟨64, true, []⟩]; exact hlenr)
            (by rw [itOf_scalar_layouts hsc0 curBody.layouts ⟨64, true, []⟩]; exact halr)
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
              ⟨r0, a0, d0, R, hd0Entry,
                (by
                  obtain ⟨T0, hT0⟩ := Option.isSome_iff_exists.mp hsc0
                  rw [tyOf_scalar_layouts hsc0 entry.layouts curBody.layouts]
                  exact (DeclSlotOk_of_scalarTypeOf hT0 _).mp hv0),
                hp, hr0, hs'.threads,
                (by rw [hs'.allocs,
                      declSlotData_scalar_layouts hsc0 (.init v) curBody.layouts entry.layouts]),
                hR⟩
        | cons savedCaller restStack =>
          rw [hcs] at hStackRel
          obtain ⟨preFrames, callerBody, callerFn, callerCtx, callerCandBound,
            callerView, callerLm, calleeRetDecl, callerBudget, callerSeg, callerSegStmt,
            hcfEq, hRest, hCallerEq, hCallerMem, hCallerFn, hNotDiv, hProtNone, hCalleeProts,
            hTargetLt, hNextBlk, hCallerFrame, hCalleeRetDecl, hDest, hCallerCand,
            hCallerBudget, hCallerBudgetLt, hPostLen, hPostStale, hPostLive, hPostTuple⟩ :=
            hStackRel.inv_cons
          subst hcfEq
          have hTermEq : bb.terminator = ⟨.return_, bb.terminator.span⟩ := by
            cases hbt : bb.terminator with
            | mk kind span => rw [hbt] at hk; exact congrArg (MirAst.Terminator.mk · span) hk
          obtain ⟨hAokRet, hAubRet⟩ :=
            evalTerminator_return_caller_anneal (curBody := curBody) (span := bb.terminator.span)
              hcs hNotDiv hProtNone hCalleeProts hDest
          have hMRet :=
            evalReturn_caller_spec hfCur (resetPick_shape hshape) hCallerFrame hNextBlk
              hCalleeRetDecl hallSc hlo hrel.retLive hDest
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
                  (fun d hd => by
                    obtain ⟨T, hT⟩ := hscOf callerBody hCallerMem _ d hd
                    exact hslotOf hT (hloCaller.slots _ d (.init w) hd hwView))
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
                remFuel + 1, callerBudget, savedCaller.returnTarget, 0, ?_⟩
              simp only [Option.getD_some, hCallerEq]
              exact ⟨hCallerMem, hCallerFn, hRest, hRest.payloads, hCallerCand,
                hCallerBudget, hCallerBudgetLt, hsh'.threads,
                segPcZero_of_translateFnInProg hCallerFn savedCaller.returnTarget, hloCaller⟩
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
        hk, hextr, hmono, hfind, hCalleeDecls, htgtLt, hArgLen, hArgBound, hArgsOk, hDestOk,
        hNotDst, hlkTgt, hlk, htrArgs, hretTr, htt⟩ :=
        callTerminatorOk_unpack hbb hcallOk htermTr
      have hmonoS : monoCallee? s.memory.callees func dp = some callee := by
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
        evalArguments_spec hfCur hallSc hsh1 hDest1 (hstale_end.1.trans hv1Len.symm) hstale1
          (fun _ h => h) hreadsArgs hNotDst hArgsOk htrArgs
      have hTermEq : bb.terminator =
          ⟨.call func argOps destination (some targetBb) unwind, bb.terminator.span⟩ := by
        cases hbt : bb.terminator with
        | mk kind span => rw [hbt] at hk; exact congrArg (MirAst.Terminator.mk · span) hk
      obtain ⟨hACallOk, hACallUb⟩ :=
        evalTerminator_call_anneal (callerBody := curBody) (span := bb.terminator.span)
          (targetBb := targetBb) (unwind := unwind) (destination := destination)
          hextr hmonoS hslotsA hnA hallSc hArgsOk htrArgs
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
          hDest2.baseCandBounded hCurCand (fun i d hd => by
            obtain ⟨T, hT⟩ := hscOf curBody hCurMem i d hd
            rw [tyOf_of_scalarTypeOf hT]; exact hT)
        obtain ⟨hfCalleeSpec, _, hargsC, hstartC, hinitC, _⟩ :=
          translateFnInProg_spec fnMap callee fCallee hfCallee
        obtain ⟨calleeLm0, mCall, hmCall, hshCall, hpCall, hfpCall, hloCall0⟩ :=
          evalCall_spec (retPlace := retPlace) (targetBb := bbName targetBb) (unwindBb := unwindBb)
            hsh2 (.inr ⟨hfCalleeSpec, hargsC, hstartC⟩)
            hd0Callee (bodyInProgFragment_allScalar (hallFrag callee hCalleeMem))
            hCalleeArgc hpdsEq hAvLenArgc hAvSlots hbase2 hCandCalleeLt
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
          caller := calleeFrameL curFn curCtx curLm curSeg segStmt
          payloads := rootCtx.payloads
          base := m2.mem.memory.allocations
          addrs := []
          nextBlock := bbName targetBb
          unwindBlock := some unwindBb
          retPtr := retPlace.ptr.thin_pointer
        }
        obtain ⟨mCallee0, calleeLm, hstepsInit, hshCallee0, hpInit, hfpInit, hloCallee, hnoRetInit⟩ :=
          steps_initBlock_stack hfCalleeSpec hinitC hshCall hloCall0 hILdead hbase2 hCandCalleeLt
            (bodyInProgFragment_allScalar (hallFrag callee hCalleeMem))
        have hkSteps : Interp.steps (1 + initLen callee) m = .ok mCallee0 := by
          rw [steps_add, steps_one hstep1, ok_bind, hstepsInit]
        have hnoRetStep : ∀ j, 1 ≤ j → j ≤ 1 + initLen callee → ∀ mj,
            Interp.steps j m = .ok mj → ∀ b' c' s'' v, ¬ ReturnRel b' c' s'' v mj := by
          intro j hj1 hj2 mj hmj b' c' s'' v
          have hjEq : j = 1 + (j - 1) := by omega
          rw [hjEq, steps_add, steps_one hstep1, ok_bind] at hmj
          exact hnoRetInit (by simp) (j - 1) (by omega) mj hmj b' c' s'' v
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
               calleeProtectors := s.memory.activeProtectors
               returnUnwind := unwind } :: s.memory.callStack)
            (callerFrames ++ [calleeCtx.caller]) callee calleeCtx
            (candBound + curBody.localDecls.length) calleeFuel :=
          .cons hStackRel rfl hCurMem hCurFn rfl rfl hrel.protectors htgtLt rfl rfl rfl
            hd0Callee hDest2 hCurCand hCurBud hCalleeBud hStepBud hCandBudLt halen2
            hPostStale' hPostLive' hPostTuple'
        have hCalleeBbsPos : 0 < callee.basicBlocks.length := by
          cases hcb : callee.basicBlocks with
          | nil => exact absurd hcb hCalleeHasBbs
          | cons _ _ => simp
        refine MultiStepRel.tauK (1 + initLen callee) mCallee0 (by omega) hkSteps ?_ hnoRetStep
        refine ⟨MirSemantics.initLocals callee argVals, {
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
          candBound + curBody.localDecls.length, calleeFuel, calleeBudget, 0, 0, ?_⟩
        simp only [Option.getD_some]
        exact ⟨hCalleeMem, hfCallee, hStackNext, rfl, hbase2, hCalleeBud,
          by omega, hshCallee0.threads, segPcZero_of_translateFnInProg hfCallee 0, hloCallee⟩

/-! ### Layout independence of scalar-family locals

`MultiStartRel` states its per-local facts at the default layout table, while
`StartRel` and `CtxOk` state them at `body.layouts`. The two agree on
scalar-family locals, which are the only locals of the multi-function fragment
(`bodyInProgFragment_allScalar`). -/

theorem localAllocsFrom_scalar_layouts (ctx : Ctx) :
    ∀ (i : Nat) (decls : List LocalDecl) (locals : List LocalSlot) (L L' : Layout.LayoutTable),
      (∀ d ∈ decls, (scalarTypeOf d.ty).isSome = true) →
      localAllocsFrom ctx i decls locals L = localAllocsFrom ctx i decls locals L'
  | _, [], locals, _, _, _ => by cases locals <;> rfl
  | _, _ :: _, [], _, _, _ => rfl
  | i, d :: ds, slot :: slots, L, L', h => by
    have hd := h d List.mem_cons_self
    simp only [localAllocsFrom]
    rw [itOf_scalar_layouts hd L L', declSlotData_scalar_layouts hd slot L L',
      localAllocsFrom_scalar_layouts ctx (i + 1) ds slots L L'
        (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]

/-- Initial locals map at `fEntry.start` under `MultiStartRel`. -/
theorem MultiStartRel.localsOk {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function} {rootCtx : Ctx}
    {s : MachineState} {mInit : Mach}
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit)
    (hargs : entry.argCount + 1 ≤ entry.localDecls.length)
    (hall : entry.localDecls.all (fun d => (scalarTypeOf d.ty).isSome) = true) :
    LocalsOkA entry rootCtx [] s.frame.locals (localsMap rootCtx (entry.argCount + 1))
      mInit.mem.memory.allocations := by
  have hsc : ∀ (i : Nat) d, entry.localDecls[i]? = some d → (scalarTypeOf d.ty).isSome = true :=
    fun _ d hd => List.all_eq_true.mp hall d (List.mem_of_getElem? hd)
  have hs1 : StartRel entry fEntry rootCtx s mInit := {
    threads := hstart.threads
    active := hstart.active
    allocs := by
      rw [hstart.allocs, localAllocs, localAllocs,
        localAllocsFrom_scalar_layouts rootCtx 0 _ s.frame.locals ⟨64, true, []⟩
          entry.layouts
          (fun d hd => List.all_eq_true.mp hall d (List.mem_of_mem_take hd))]
    blk0 := hstart.blk0
    stmt0 := hstart.stmt0
    hasBlocks := hstart.hasBlocks
    nlocals := hstart.nlocals
    slots := fun i d slot hd hs => by
      obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (hsc i d hd)
      rw [DeclSlotOk_of_scalarTypeOf hT,
        tyOf_scalar_layouts (hsc i d hd) entry.layouts ⟨64, true, []⟩]
      exact hstart.slots i d slot hd hs
    argsLive := hstart.argsLive
    tempsDead := hstart.tempsDead
    addrs := fun i d hi hd => by
      rw [itOf_scalar_layouts (hsc i d hd) entry.layouts ⟨64, true, []⟩,
        tyOf_scalar_layouts (hsc i d hd) entry.layouts ⟨64, true, []⟩]
      exact hstart.addrs i d hi hd
    ret := fun d hd => by
      rw [itOf_scalar_layouts (hsc 0 d hd) entry.layouts ⟨64, true, []⟩,
        tyOf_scalar_layouts (hsc 0 d hd) entry.layouts ⟨64, true, []⟩]
      exact hstart.ret d hd
    baseLow := hstart.baseLow
    borrows := hstart.borrows
    nextTag_pos := hstart.nextTag_pos
    callStack := hstart.callStack
    activeCallee := hstart.activeCallee
    protectors := hstart.protectors
    callerLocals := hstart.callerLocals
  }
  exact hs1.localsOk hargs (fun i d _ hd =>
    let ⟨_, hT⟩ := Option.isSome_iff_exists.mp (hsc i d hd)
    isPtrTy_false_of_scalarTypeOf hT)

/-- **Multi-function init block (`fEntry.start`, with intermediate non-return
invariant).** From `MultiStartRel` (Anneal at `(0, 0)` of `entry` with `callees`
loaded and MiniRust at `fEntry.start`), `initLen entry` MiniRust steps execute
`minimize`'s `initBlock`, land in `MultiStateRel`, and maintain `¬ ReturnRel` at
every intermediate step `j ≤ initLen entry`. -/
theorem multi_step_start_with_no_returnRel {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function} {rootCtx : Ctx}
    {s : MachineState} {mInit : Mach}
    (hfrag : progInFragment entry callees = true)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit) :
    (∃ m0, Interp.steps (initLen entry) mInit = .ok m0 ∧
      MultiStateRel entry callees prog rootCtx s m0) ∧
    (∀ j ≤ initLen entry, ∀ mj, Interp.steps j mInit = .ok mj →
      ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mj) := by
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
  obtain ⟨m0, lm, hm0, hsh, hp0, hfp0, hlo0, hnoRetInit⟩ :=
    steps_initBlock_stack hfSpec hInitBlk hsh0
      (hstart.localsOk hargs (bodyInProgFragment_allScalar (hallFrag entry List.mem_cons_self)))
      hstart.tempsDead hstart.baseLow.toBaseCandBounded (by omega)
      (bodyInProgFragment_allScalar (hallFrag entry List.mem_cons_self))
  refine ⟨⟨m0, hm0, s.frame.locals, {
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
    callerLocals := hstart.callerLocals }⟩, hnoRetInit (by simp)⟩
  refine ⟨[rootCtx.caller], rootCtx, fEntry, lm, 0, callees.length + 1, rootBudget, 0, 0, ?_⟩
  rw [hstart.activeCallee, Option.getD_none, hstart.callStack,
    hstart.blk0, hstart.stmt0]
  exact ⟨List.mem_cons_self, hstart.hfEntry,
    .nil hstart.baseLow hstart.ret rootBudget hRootBud hRootBudLt,
    rfl, hstart.baseLow.toBaseCandBounded, hRootBud, by omega, hsh.threads,
    segPcZero_of_translateFnInProg hstart.hfEntry 0, hlo0⟩

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
      MultiStateRel entry callees prog rootCtx s m0 :=
  (multi_step_start_with_no_returnRel hfrag hstart).1

/-- No prefix step `j ≤ initLen entry` of `multi_step_start` can satisfy
`ReturnRel`. -/
theorem multi_step_start_no_returnRel {entry : CapturedMir} {callees : List CapturedMir}
    {prog : Gen.Program} {fEntry : Gen.Function} {rootCtx : Ctx}
    {s : MachineState} {mInit : Mach}
    (hfrag : progInFragment entry callees = true)
    (hstart : MultiStartRel entry callees prog fEntry rootCtx s mInit) :
    ∀ j ≤ initLen entry, ∀ mj, Interp.steps j mInit = .ok mj →
      ∀ b' c' s' v, ¬ ReturnRel b' c' s' v mj :=
  (multi_step_start_with_no_returnRel hfrag hstart).2

private theorem initLocalsAux_argsInit (layouts : Layout.LayoutTable) (ds : List LocalDecl)
    (vs : List Value) (idx : Nat)
    (h : argsOkAux (ds.take vs.length) vs layouts = true) (hlen : vs.length ≤ ds.length)
    (hsc : ∀ d ∈ ds, (scalarTypeOf d.ty).isSome = true) :
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
        obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (hsc d0 List.mem_cons_self)
        have h1 := (DeclSlotOk_of_scalarTypeOf hT (.init v)).mp (declArgOk_declSlotOk hv)
        rwa [tyOf_scalar_layouts (hsc d0 List.mem_cons_self) layouts ⟨64, true, []⟩] at h1
      intro j d hj hd
      cases j with
      | zero =>
        simp at hd; subst hd
        exact ⟨v, rfl, hvslot⟩
      | succ j =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
        simp only [List.getElem?_cons_succ] at hd
        simp only [initLocalsAux, Nat.add_eq, List.getElem?_cons_succ]
        exact ih vs idx hvs (by simpa using hlen)
          (fun d' hd' => hsc d' (List.mem_cons_of_mem _ hd')) j d hj hd

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
  have hentryFrag := hallFrag entry List.mem_cons_self
  obtain ⟨_, hdeclLen, _, hbne, _⟩ := bodyInProgFragment_spec hentryFrag
  have hall := bodyInProgFragment_allScalar hentryFrag
  have hscd : ∀ (i : Nat) d, entry.localDecls[i]? = some d → (scalarTypeOf d.ty).isSome = true :=
    fun _ d hd => List.all_eq_true.mp hall d (List.mem_of_getElem? hd)
  cases hdecls : entry.localDecls with
  | nil => simp [hdecls] at hdeclLen
  | cons d0 ds =>
    rw [hdecls] at hdeclLen
    have hscds : ∀ d ∈ ds, (scalarTypeOf d.ty).isSome = true := fun d hd =>
      List.all_eq_true.mp hall d (by rw [hdecls]; exact List.mem_cons_of_mem _ hd)
    have hargs' : argsOkAux (ds.take entry.argCount) args entry.layouts = true := by
      simpa [argsOk, hdecls] using hargs
    have hlenA : args.length = entry.argCount := by
      have := argsOkAux_length (ds.take entry.argCount) args hargs'
      simp at this hdeclLen
      omega
    obtain ⟨hlen, hslots, hlive, hdead⟩ := initLocalsAux_spec entry.layouts ds args 0
      (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega)
    have hainit := initLocalsAux_argsInit entry.layouts ds args 0
      (by rw [hlenA]; exact hargs') (by simp at hdeclLen; omega) hscds
    have hinit : (initMachineStateWithCallees entry args callees).frame.locals =
        .uninit :: initLocalsAux 1 ds args := by
      cases callees <;> simp [initMachineStateWithCallees, initMachineState, hdecls, initLocalsAux]
    refine {
      hfEntry := hfEntry
      env := henv
      threads := hthreads
      active := hactive
      allocs := hallocs
      blk0 := by cases callees <;> rfl
      stmt0 := by cases callees <;> rfl
      hasBlocks := by
        cases hbbs : entry.basicBlocks with | nil => exact absurd hbbs hbne | cons _ _ => simp
      nlocals := by simp [hinit, hdecls, hlen]
      slots := ?_
      argsInit := ?_
      argsLive := ?_
      tempsDead := ?_
      addrs := fun i d hi hd => by
        rw [itOf_scalar_layouts (hscd i d hd) ⟨64, true, []⟩ entry.layouts,
          tyOf_scalar_layouts (hscd i d hd) ⟨64, true, []⟩ entry.layouts]
        exact hctx.addrs i d hi hd
      ret := fun d hd => by
        rw [itOf_scalar_layouts (hscd 0 d hd) ⟨64, true, []⟩ entry.layouts,
          tyOf_scalar_layouts (hscd 0 d hd) ⟨64, true, []⟩ entry.layouts]
        exact hctx.ret d hd
      baseLow := hctx.baseLow
      calleesEq := by cases callees <;> rfl
      borrows := by cases callees <;> rfl
      nextTag_pos := by cases callees <;> exact Nat.zero_lt_one
      callStack := by cases callees <;> rfl
      activeCallee := by cases callees <;> rfl
      protectors := by cases callees <;> rfl
      callerLocals := by cases callees <;> rfl }
    · intro i d slot hd hs
      have hsc := hscd i d hd
      obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hsc
      rw [hdecls] at hd; rw [hinit] at hs
      cases i with
      | zero => simp at hd hs; subst hs; trivial
      | succ k =>
        simp at hd hs
        have h1 := (DeclSlotOk_of_scalarTypeOf hT slot).mp (hslots k d slot hd hs)
        rwa [tyOf_scalar_layouts hsc entry.layouts ⟨64, true, []⟩] at h1
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
      | succ k =>
        simp at hs
        obtain ⟨v, rfl⟩ := hlive k slot (by omega) hs
        simp
    · intro i hi1 hi2
      rw [hinit]
      cases i with
      | zero => omega
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hdead k (by omega) (by rw [hdecls] at hi2; simpa using hi2)

/-! ## Provenance-tracked state relation (`MR-3.3`) -/

/-- `StateRelN` extended with `ProvenanceRel` tracking the correspondence
between Anneal's exposed borrow tags `exposedTags` and MiniRust's
`m.intptrcast.exposed` provenance set (`spec/mem/intptrcast.md`). -/
def StateRelNProv (body : CapturedMir) (f : Gen.Function) (ctx : Ctx)
    (s : MachineState) (m : Mach) (exposedTags : List Nat) : Prop :=
  StateRelN body f ctx s m ∧ ProvenanceRel body ctx s m exposedTags

theorem StateRelNProv.empty {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {s : MachineState} {m : Mach}
    (hrel : StateRelN body f ctx s m) (hexp : m.intptrcast.exposed.elems = [])
    (hemptyA : s.memory.exposedAllocIds = [] := by rfl) :
    StateRelNProv body f ctx s m [] :=
  ⟨hrel, ProvenanceRel.empty body ctx s m hexp hemptyA⟩

/-- Under `StateRelN`, every borrow entry `entry` found by `lookupBorrow`
targets an address-taken local `entry.targetLocal ∈ bodyAddrTakenLocals body`
with a valid `ptrTargetSpec`. -/
theorem StateRelN.expose_provenance_rel {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {s : MachineState} {m : Mach} {exposedTags : List Nat}
    (hrel : StateRelN body f ctx s m)
    (hprov : ProvenanceRel body ctx s m exposedTags)
    {tag : Nat} {p : Prov} (addr : Int) (htag_ne : tag ≠ 0)
    (htgt : ExposedTargetOk body ctx s m.mem.memory.allocations tag p) :
    ∃ entry,
      lookupBorrow s.memory.borrows tag = some entry ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ProvenanceRel body ctx { s with memory := exposeMem s.memory tag }
        { m with intptrcast := IntPtrCast.expose m.intptrcast { addr := addr, provenance := some p } }
        (tag :: exposedTags) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := hrel
  have htgt' := htgt
  obtain ⟨entry, _, _, _, hlk, hk, _⟩ := htgt'
  exact ⟨entry, hlk, hk, hprov.expose_some addr htag_ne htgt⟩

/-- Under `StateRelNProv` (without requiring `inFragment`, which excludes
provenance casts by `inFragment_not_hasProvCast`), every provenance `prov` in
`m.intptrcast.exposed` is `targetProv ctx k` for an address-taken local
`k ∈ bodyAddrTakenLocals body` backed by a live stack allocation at index
`ctx.base.length + k` and address `ctx.addrs.getD k 0`. -/
theorem StateRelNProv.exposed_target_localPtr {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {s : MachineState} {m : Mach} {exposedTags : List Nat}
    (h : StateRelNProv body f ctx s m exposedTags)
    {prov : Prov} (hc : setContains m.intptrcast.exposed prov = true) :
    ∃ (tag : Nat) (entry : BorrowEntry) (pointeeIt : Gen.IntType) (relOff : Nat)
      (alloc : Gen.Allocation),
      tag ∈ exposedTags ∧
      lookupBorrow s.memory.borrows tag = some entry ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (pointeeIt, relOff) ∧
      prov = targetProv ctx entry.targetLocal ∧
      m.mem.memory.allocations[ctx.base.length + entry.targetLocal]? = some alloc ∧
      alloc.live = true ∧
      alloc.addr = ctx.addrs.getD entry.targetLocal 0 ∧
      relOff + pointeeIt.size.bytes ≤ (Allocation.size alloc).bytes := by
  obtain ⟨_, hprov⟩ := h
  obtain ⟨tag, htag, entry, pointeeIt, relOff, alloc, hlk, hk, hspec, hpeq, halloc, hlive, haddr, hsz⟩ :=
    hprov.sound prov hc
  exact ⟨tag, entry, pointeeIt, relOff, alloc, htag, hlk, hk, hspec, hpeq, halloc, hlive, haddr, hsz⟩

/-! ### Provenance-cast steps: allocation shapes and the `ProvenanceRel` step lemmas (MR-3.3 B3)

Pass A2 stated these step lemmas with the hypotheses
`m4.mem.memory.allocations = m.mem.memory.allocations` and
`m4.intptrcast = ...` on the MiniRust post-state. The first is unsatisfiable at
every real `PointerExposeProvenance` / `PointerWithExposedProvenance` step,
because the intrinsic stores its result into the destination local's
allocation (`ProvenanceWitness.passA2_hm4_allocs_unsatisfiable_expose`,
`..._withExposed`), so those lemmas applied to no execution. The lemmas below
instead *derive* what the MiniRust step does: `placeStore`, `placeLoad`, local
`evalPlace`, and `jumpToBlock` never touch `intptrcast` and change allocations
only in their bytes (`AllocShapeEq`), which is all `ExposedTargetOk` and
`ProvenanceRel` read. -/

/-- Monadic inversion for `Interp`. -/
theorem interpBind_ok {α β : Type} {m : Interp α} {f : α → Interp β} {y : β}
    (h : (m >>= f) = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem listIndex_ok_get {T : Type} {xs : List T} {i : Int} {what : String} {x : T}
    (h : listIndex xs i what = .ok x) : 0 ≤ i ∧ xs[i.toNat]? = some x := by
  unfold listIndex at h
  split at h
  · next hge =>
    cases hget : xs[i.toNat]? with
    | none => simp [hget, specPanic] at h
    | some y =>
      simp only [hget, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨hge, rfl⟩
  · simp [specPanic] at h

theorem listSet_ok_eq {T : Type} {xs : List T} {i : Int} {x : T} {what : String} {ys : List T}
    (h : listSet xs i x what = .ok ys) : ys = xs.set i.toNat x := by
  unfold listSet at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  · simp [specPanic] at h

theorem writeSubsliceAtIndex_length {T : Type} {xs : List T} {start : Int} {src ys : List T}
    (h : writeSubsliceAtIndex xs start src = .ok ys) : ys.length = xs.length := by
  unfold writeSubsliceAtIndex at h
  split at h
  · next hb =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · simp [specPanic] at h

/-- Two allocation lists agree on length and, index by index, on address,
liveness, and size: only the stored bytes may differ. This is everything
`ExposedTargetOk` (and so `ProvenanceRel`) reads. -/
def AllocShapeEq (as bs : List Gen.Allocation) : Prop :=
  as.length = bs.length ∧
    ∀ (i : Nat) (a : Gen.Allocation), as[i]? = some a →
      ∃ b, bs[i]? = some b ∧ b.addr = a.addr ∧ b.live = a.live ∧ b.data.length = a.data.length

theorem AllocShapeEq.refl (as : List Gen.Allocation) : AllocShapeEq as as :=
  ⟨rfl, fun _ a h => ⟨a, h, rfl, rfl, rfl⟩⟩

theorem AllocShapeEq.trans {as bs cs : List Gen.Allocation} (h1 : AllocShapeEq as bs)
    (h2 : AllocShapeEq bs cs) : AllocShapeEq as cs := by
  refine ⟨h1.1.trans h2.1, fun i a ha => ?_⟩
  obtain ⟨b, hb, hb1, hb2, hb3⟩ := h1.2 i a ha
  obtain ⟨c, hc, hc1, hc2, hc3⟩ := h2.2 i b hb
  exact ⟨c, hc, hc1.trans hb1, hc2.trans hb2, hc3.trans hb3⟩

theorem AllocShapeEq.set {as : List Gen.Allocation} {k : Nat} {a a' : Gen.Allocation}
    (ha : as[k]? = some a) (haddr : a'.addr = a.addr) (hlive : a'.live = a.live)
    (hlen : a'.data.length = a.data.length) :
    AllocShapeEq as (as.set k a') := by
  refine ⟨by simp, fun i b hb => ?_⟩
  by_cases hik : k = i
  · subst hik
    rw [ha] at hb
    cases hb
    have hk : k < as.length := (List.getElem?_eq_some_iff.mp ha).1
    exact ⟨a', by simp [hk], haddr, hlive, hlen⟩
  · exact ⟨b, by rw [List.getElem?_set_ne hik]; exact hb, rfl, rfl, rfl⟩

/-- `BasicMemory::store` only rewrites the bytes of one allocation. -/
theorem BM.store_shape {mem mem' : BM} {ptr : Ptr} {bytes : List Byte} {align : Align}
    (h : BM.store mem ptr bytes align = .ok mem') :
    AllocShapeEq mem.allocations mem'.allocations := by
  unfold BM.store at h
  split at h
  · simp [ub] at h
  · obtain ⟨r, _, h⟩ := interpBind_ok h
    cases r with
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact AllocShapeEq.refl _
    | some t =>
      obtain ⟨id, pe, off⟩ := t
      dsimp only at h
      obtain ⟨alloc, hidx, h⟩ := interpBind_ok h
      obtain ⟨data, hw, h⟩ := interpBind_ok h
      obtain ⟨allocs', hs, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨_, hget⟩ := listIndex_ok_get hidx
      rw [listSet_ok_eq hs]
      exact AllocShapeEq.set hget rfl rfl (writeSubsliceAtIndex_length hw)

/-- `BasicMemory::load` leaves the allocations unchanged up to shape. -/
theorem BM.load_shape {mem mem' : BM} {ptr : Ptr} {len : Size} {align : Align}
    {bytes : List Byte} (h : BM.load mem ptr len align = .ok (bytes, mem')) :
    AllocShapeEq mem.allocations mem'.allocations := by
  unfold BM.load at h
  split at h
  · simp [ub] at h
  · obtain ⟨r, _, h⟩ := interpBind_ok h
    cases r with
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact AllocShapeEq.refl _
    | some t =>
      obtain ⟨id, pe, off⟩ := t
      dsimp only at h
      obtain ⟨alloc, hidx, h⟩ := interpBind_ok h
      obtain ⟨allocs', hs, h⟩ := interpBind_ok h
      obtain ⟨bs, _, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      obtain ⟨_, hget⟩ := listIndex_ok_get hidx
      rw [listSet_ok_eq hs]
      exact AllocShapeEq.set hget rfl rfl rfl

/-- `Machine::place_store` changes only bytes of allocations, never
`intptrcast`. -/
theorem placeStore_shape {m m' : Mach} {pl : Gen.Place BM} {v : Val} {ty : Gen.Type}
    (h : placeStore m pl v ty = .ok m') :
    AllocShapeEq m.mem.memory.allocations m'.mem.memory.allocations ∧
      m'.intptrcast = m.intptrcast := by
  unfold placeStore at h
  split at h
  · simp [ub] at h
  · unfold typedStore at h
    cases hcv : checkValue v ty (some m) with
    | error e => simp [hcv, specPanic, bind, Except.bind] at h
    | ok u =>
      simp only [hcv] at h
      obtain ⟨bytes, _, h⟩ := interpBind_ok h
      obtain ⟨cm, hcm, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      unfold CM.store at hcm
      obtain ⟨mem', hbm, hcm⟩ := interpBind_ok hcm
      simp only [pure, Except.pure, Except.ok.injEq] at hcm
      subst hcm
      exact ⟨BM.store_shape hbm, rfl⟩

/-- `Machine::place_load` changes no allocation shape and never `intptrcast`. -/
theorem placeLoad_shape {m m' : Mach} {pl : Gen.Place BM} {ty : Gen.Type} {v : Val}
    (h : placeLoad m pl ty = .ok (v, m')) :
    AllocShapeEq m.mem.memory.allocations m'.mem.memory.allocations ∧
      m'.intptrcast = m.intptrcast := by
  unfold placeLoad at h
  split at h
  · simp [ub] at h
  · unfold typedLoad at h
    obtain ⟨l, _, h⟩ := interpBind_ok h
    obtain ⟨size, _, h⟩ := interpBind_ok h
    obtain ⟨⟨bytes, cm⟩, hcm, h⟩ := interpBind_ok h
    obtain ⟨dv, _, h⟩ := interpBind_ok h
    unfold CM.load at hcm
    obtain ⟨⟨bytes', mem'⟩, hbm, hcm⟩ := interpBind_ok hcm
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcm
    obtain ⟨_, rfl⟩ := hcm
    cases dv with
    | none => simp [ub] at h
    | some val =>
      dsimp only at h
      obtain ⟨u, _, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨BM.load_shape hbm, rfl⟩

/-- Evaluating a local place leaves the machine unchanged. -/
theorem evalPlace_local_eq {m m' : Mach} {name : Gen.LocalName} {out : Gen.Place BM × Gen.Type}
    (h : evalPlace m (.Local name) = .ok (out, m')) : m' = m := by
  unfold evalPlace at h
  obtain ⟨fr, _, h⟩ := interpBind_ok h
  obtain ⟨ty, _, h⟩ := interpBind_ok h
  cases hmg : mapGet fr.locals name with
  | none => simp [hmg, ub] at h
  | some ptr =>
    simp only [hmg, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- Loading a local changes no allocation shape and never `intptrcast`. -/
theorem evalValue_load_local_shape {m m' : Mach} {name : Gen.LocalName} {out : Val × Gen.Type}
    (h : evalValue m (.Load (.Local name)) = .ok (out, m')) :
    AllocShapeEq m.mem.memory.allocations m'.mem.memory.allocations ∧
      m'.intptrcast = m.intptrcast := by
  unfold evalValue at h
  cases hpl : evalPlace m (.Local name) with
  | error e => simp [hpl, bind, Except.bind] at h
  | ok r =>
    obtain ⟨⟨place, ty⟩, m1⟩ := r
    have hm1 := evalPlace_local_eq hpl
    simp only [hpl, bind, Except.bind] at h
    cases hld : placeLoad m1 place ty with
    | error e => simp [hld] at h
    | ok r2 =>
      obtain ⟨v, m2⟩ := r2
      simp only [hld] at h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have := placeLoad_shape hld
      rw [hm1] at this
      exact this

/-- `Machine::jump_to_block` changes only the current frame. -/
theorem jumpToBlock_mem {m m' : Mach} {b : Gen.BbName} (h : jumpToBlock m b = .ok m') :
    m'.mem = m.mem ∧ m'.intptrcast = m.intptrcast := by
  unfold jumpToBlock mutateCurFrame at h
  obtain ⟨t, _, h⟩ := interpBind_ok h
  cases hl : t.stack.getLast? with
  | none => simp [hl, specPanic] at h
  | some fr =>
    simp only [hl] at h
    obtain ⟨threads, _, h⟩ := interpBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem ExposedTargetOk.of_shape {body : CapturedMir} {ctx : Ctx} {s : MachineState}
    {as bs : List Gen.Allocation} {tag : Nat} {p : Prov}
    (h : ExposedTargetOk body ctx s as tag p) (hs : AllocShapeEq as bs) :
    ExposedTargetOk body ctx s bs tag p := by
  obtain ⟨entry, pointeeIt, relOff, alloc, hlk, hk, hspec, hp, halloc, hlive, haddr, hsz⟩ := h
  obtain ⟨b, hb, hb1, hb2, hb3⟩ := hs.2 _ alloc halloc
  refine ⟨entry, pointeeIt, relOff, b, hlk, hk, hspec, hp, hb, hb2 ▸ hlive, hb1 ▸ haddr, ?_⟩
  simpa [Allocation.size, hb3] using hsz

theorem ProvenanceRel.of_shape {body : CapturedMir} {ctx : Ctx} {s : MachineState}
    {m m' : Mach} {tags : List Nat} (h : ProvenanceRel body ctx s m tags)
    (hipc : m'.intptrcast = m.intptrcast)
    (hs : AllocShapeEq m.mem.memory.allocations m'.mem.memory.allocations) :
    ProvenanceRel body ctx s m' tags where
  nodup := hipc ▸ h.nodup
  anneal_exposed := h.anneal_exposed
  sound p hp := by
    rw [hipc] at hp
    obtain ⟨t, ht, htgt⟩ := h.sound p hp
    exact ⟨t, ht, htgt.of_shape hs⟩
  complete t ht := by
    obtain ⟨p, hp, htgt⟩ := h.complete t ht
    exact ⟨p, hipc ▸ hp, htgt.of_shape hs⟩

/-- `ProvenanceRel` reads the Anneal state only through its borrow and exposed tables,
which `advanceStmt` keeps. -/
theorem ProvenanceRel.of_advanceStmt {body : CapturedMir} {ctx : Ctx} {s : MachineState}
    {m : Mach} {tags : List Nat} (locals' : List LocalSlot)
    (h : ProvenanceRel body ctx s m tags) :
    ProvenanceRel body ctx (advanceStmt s locals' s.memory) m tags :=
  ⟨h.nodup, h.anneal_exposed, h.sound, h.complete⟩

/-- Anneal-side canonical address and exposure recovery specification for
`pv` (`pv.tag ≠ 0`, `fullAddr < 2^64`, `ptrAddress?` evaluates to `some fullAddr`,
and `recoverExposedPtrValue?` after `recordExposedAllocId` recovers `.ptr pv 8`
whenever borrow-target locals agree with `s.frame.locals`).

Discharged structurally by `AnnealExposeRoundTripOk.of_structural` from
`BorrowsOk`, `localDeclOk`, `ExposeTargetSlotOk`, and `NoCompetingExposedBorrow`
at `fullAddr = canonicalLocalAddr entry.targetLocal relOff` (so none of the
`ProvenanceRel.*_from_frameOk` theorems need an external `hart` hypothesis). -/
structure AnnealExposeRoundTripOk (body : CapturedMir) (s : MachineState)
    (pv : ProvenancePtr) (fullAddr : Nat) : Prop where
  tag_ne_zero : pv.tag ≠ 0
  addr_lt : fullAddr < 2 ^ 64
  ptr_addr : ∀ (localsPost : List LocalSlot),
    (∀ b ∈ s.memory.borrows, localsPost[b.targetLocal]? = s.frame.locals[b.targetLocal]?) →
    MirSemantics.ptrAddress? localsPost s.memory.borrows s.memory.callerLocals
      body.localDecls body.layouts 8 pv = some fullAddr
  recover_eq : ∀ (localsPost : List LocalSlot),
    (∀ b ∈ s.memory.borrows, localsPost[b.targetLocal]? = s.frame.locals[b.targetLocal]?) →
    MirSemantics.recoverExposedPtrValue? localsPost s.memory.borrows s.memory.globals
      s.memory.callerLocals (MirSemantics.recordExposedAllocId s.memory.exposedAllocIds pv.allocId)
      body.localDecls body.layouts 8 fullAddr = some (.ptr pv 8)

/-- Target-slot readiness for `entry` in `s.frame.locals`: `entry.targetLocal`
is not `.dead`, and if `entry` borrows a proper sub-place (`entry.targetProjection
≠ []`), `body` satisfies `ptrDeclLayoutsOk` and `s.frame.locals[entry.targetLocal]?`
holds a well-typed initialized value (automatic for whole-local borrows
`entry.targetProjection = []`, and automatic for sub-place borrows whenever
`ptrDeclLayoutsOk body = true` and `s.frame.locals` agrees with `view`). -/
def ExposeTargetSlotOk (body : CapturedMir) (s : MachineState)
    (entry : BorrowEntry) : Prop :=
  s.frame.locals[entry.targetLocal]? ≠ some .dead ∧
  (entry.targetProjection ≠ [] →
    ptrDeclLayoutsOk body = true ∧
    ∃ dk v,
      body.localDecls[entry.targetLocal]? = some dk ∧
      s.frame.locals[entry.targetLocal]? = some (.init v) ∧
      DeclSlotOk dk (.init v) body.layouts)

/-- Non-interference condition on previously exposed stack borrow entries when
exposing `pv` (resolved to `entry` at byte offset `relOff`): every *other*
already-exposed borrow entry `b ∈ s.memory.borrows` (`b.tag ≠ pv.tag` with
`isExposedAllocId s.memory.exposedAllocIds b.tag = true`) either:
1. has strictly lower Tree Borrows permission rank (`exposedPermScore b.perm <
   exposedPermScore entry.perm`, e.g. `.disabled` or `.frozen` under an `.active`
   or `.reserved` child/reborrow), or
2. targets a higher stack local page `entry.targetLocal < b.targetLocal` (with
   `relOff < 65536`), or
3. targets a lower stack local page `b.targetLocal < entry.targetLocal` whose
   sub-place span stays strictly inside its 64 KiB page (`placeOff_b + bound_b <
   65536`).
Vacuously true whenever `s.memory.exposedAllocIds` contains no other tag in
`s.memory.borrows` (in particular whenever `exposedTags = []` under
`ProvenanceRel`, or when re-exposing the same `pv.tag`). -/
def NoCompetingExposedBorrow (body : CapturedMir) (s : MachineState)
    (pv : ProvenancePtr) (entry : BorrowEntry) (relOff : Nat) : Prop :=
  ∀ b ∈ s.memory.borrows,
    MirSemantics.isExposedAllocId s.memory.exposedAllocIds b.tag = true →
    b.tag ≠ pv.tag →
    MirSemantics.exposedPermScore b.perm < MirSemantics.exposedPermScore entry.perm ∨
    (entry.targetLocal < b.targetLocal ∧ relOff < 65536) ∨
    (b.targetLocal < entry.targetLocal ∧
      ∀ (localsPost : List LocalSlot),
        localsPost[b.targetLocal]? = s.frame.locals[b.targetLocal]? →
        ∃ placeOff bound,
          MirSemantics.borrowPlaceByteOffset? localsPost s.memory.callerLocals
            body.localDecls body.layouts b = some placeOff ∧
          MirSemantics.ptrAllocByteBound? localsPost
            { emptyMemory with
              globals := s.memory.globals
              borrows := [{ b with perm := .active }]
              callerLocals := s.memory.callerLocals }
            body.localDecls body.layouts { allocId := b.tag, offsetBytes := 0 } = some bound ∧
          placeOff + bound < 65536)

theorem NoCompetingExposedBorrow.of_same_or_unexposed {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m : Mach} {exposedTags : List Nat}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    {pv : ProvenancePtr} {entry : BorrowEntry} {relOff : Nat}
    (hsub : ∀ t ∈ exposedTags, t = pv.tag) :
    NoCompetingExposedBorrow body s pv entry relOff := by
  intro b _ hexp hne
  exact absurd (hsub b.tag ((hprov.anneal_exposed b.tag).mp hexp)) hne

theorem NoCompetingExposedBorrow.of_unexposed {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m : Mach}
    (hprov : ProvenanceRel body ctx s m [])
    (pv : ProvenancePtr) (entry : BorrowEntry) (relOff : Nat) :
    NoCompetingExposedBorrow body s pv entry relOff :=
  NoCompetingExposedBorrow.of_same_or_unexposed hprov (fun _ hm => by cases hm)

private def exposedStackStepCore
    (pageBase pageScale : Nat)
    (expFlag targetLive : Bool)
    (boffOpt rawBoundOpt : Option Nat)
    (bTag bLocal pScore addrBits : Nat)
    (restPair : Option (Nat × Nat × Nat × Nat × Nat) × Bool) :
    Option (Nat × Nat × Nat × Nat × Nat) × Bool :=
  let (restBest, restAmbig) := restPair
  match expFlag with
  | false => (restBest, restAmbig)
  | true =>
    match targetLive with
    | false => (restBest, restAmbig)
    | true =>
      let localPage := Nat.add pageBase bLocal
      let localPageBase := Nat.mul localPage pageScale
      match boffOpt with
      | .none =>
        let onLocalPage :=
          Bool.and (Nat.ble localPageBase addrBits)
            (Nat.blt addrBits (Nat.add localPageBase pageScale))
        (restBest, Bool.or restAmbig onLocalPage)
      | .some placeOff =>
        let tagBase := Nat.add localPageBase placeOff
        match Nat.ble tagBase addrBits with
        | false =>
          let beforeSubPlace := Nat.ble localPageBase addrBits
          (restBest, Bool.or restAmbig beforeSubPlace)
        | true =>
          let candOff := Nat.sub addrBits tagBase
          let bound : Nat :=
            match rawBoundOpt with
            | .some b => b
            | .none => Nat.sub pageScale (Nat.min placeOff pageScale)
          match Nat.ble candOff bound with
          | false => (restBest, restAmbig)
          | true =>
            let interiorBit :=
              match Nat.blt candOff bound with
              | true => 1
              | false => 0
            let remSpan := Nat.sub bound candOff
            let cand := (bTag, candOff, pScore, interiorBit, remSpan)
            let pickCand : Bool :=
              match restBest with
              | .none => true
              | .some (_, _, bestPerm, bestInt, bestRem) =>
                match Nat.blt bestPerm pScore with
                | true => true
                | false =>
                  match Nat.beq bestPerm pScore with
                  | false => false
                  | true =>
                    match Nat.blt bestInt interiorBit with
                    | true => true
                    | false =>
                      match Nat.beq bestInt interiorBit with
                      | false => false
                      | true => Nat.blt bestRem remSpan
            match pickCand with
            | true => (.some cand, restAmbig)
            | false => (restBest, restAmbig)

private theorem findBestExposedStackBorrow_cons_eq
    (locals : List LocalSlot) (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) (expIds : List AllocId)
    (decls : List LocalDecl) (layouts : Layout.LayoutTable)
    (addrBits : Nat) (b : BorrowEntry) (rest : List BorrowEntry) :
    MirSemantics.findBestExposedStackBorrow locals globals callerLocals expIds
      decls layouts 8 addrBits (b :: rest) =
    exposedStackStepCore
      (MirSemantics.stackLocalAddrPageBase 8) 65536
      (MirSemantics.isExposedAllocId expIds b.tag)
      (match get? locals b.targetLocal with
       | .some (.init _) => true
       | .some .uninit => true
       | .some .dead => false
       | .none =>
         match get? callerLocals b.targetLocal with
         | .some (.init _) => true
         | .some .uninit => true
         | _ => false)
      (MirSemantics.borrowPlaceByteOffset? locals callerLocals decls layouts b)
      (MirSemantics.ptrAllocByteBound? locals
        { emptyMemory with
          globals := globals
          borrows := { b with perm := .active } :: .nil
          callerLocals := callerLocals }
        decls layouts { allocId := b.tag, offsetBytes := 0 })
      b.tag b.targetLocal (MirSemantics.exposedPermScore b.perm) addrBits
      (MirSemantics.findBestExposedStackBorrow locals globals callerLocals expIds
        decls layouts 8 addrBits rest) := rfl

private theorem exposedStackStepCore_nonwinning
    (pageBase pageScale addrBits : Nat)
    (hbase : pageBase = 1048576) (hscale : pageScale = 65536)
    (expFlag targetLive : Bool) (boffOpt rawBoundOpt : Option Nat)
    (bTag bLocal pScore entryTag entryLocal entryScore relOff : Nat)
    (haddr : addrBits = (1048576 + entryLocal) * 65536 + relOff)
    (restPair : Option (Nat × Nat × Nat × Nat × Nat) × Bool)
    (hcomp :
      expFlag = false ∨
      pScore < entryScore ∨
      (entryLocal < bLocal ∧ relOff < 65536) ∨
      (bLocal < entryLocal ∧
        ∃ placeOff bound,
          boffOpt = some placeOff ∧
          rawBoundOpt = some bound ∧
          placeOff + bound < 65536)) :
    let res := exposedStackStepCore pageBase pageScale expFlag targetLive boffOpt rawBoundOpt
      bTag bLocal pScore addrBits restPair
    ((restPair.1 = none ∨
        ∃ t o bp ib rs, restPair.1 = some (t, o, bp, ib, rs) ∧ bp < entryScore) →
      (res.1 = none ∨
        ∃ t o bp ib rs, res.1 = some (t, o, bp, ib, rs) ∧ bp < entryScore)) ∧
    ((∃ ib rs, restPair.1 = some (entryTag, 0, entryScore, ib, rs)) →
      (∃ ib rs, res.1 = some (entryTag, 0, entryScore, ib, rs))) := by
  intro res
  rcases restPair with ⟨restBest, restAmbig⟩
  dsimp only [res, exposedStackStepCore]
  rcases hcomp with hnot_exp | hperm_lt | ⟨hlt_hi, hrel_lt⟩ |
      ⟨hlt_lo, placeOff, bound, hboff, hbound, hspan_lt⟩
  · subst hnot_exp
    exact ⟨id, id⟩
  · cases expFlag with
    | false => exact ⟨id, id⟩
    | true =>
      cases targetLive with
      | false => exact ⟨id, id⟩
      | true =>
        cases boffOpt with
        | none => exact ⟨id, id⟩
        | some poff =>
          dsimp only
          cases Nat.ble (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) poff) addrBits with
          | false => exact ⟨id, id⟩
          | true =>
            dsimp only
            cases Nat.ble
                (Nat.sub addrBits (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) poff))
                (match rawBoundOpt with
                 | .some b => b
                 | .none => Nat.sub pageScale (Nat.min poff pageScale)) with
            | false => exact ⟨id, id⟩
            | true =>
              dsimp only
              constructor
              · intro hpre
                rcases hpre with hnone | ⟨t, o, bp, ib, rs, hsome, hbp⟩
                · subst hnone
                  exact .inr ⟨_, _, _, _, _, rfl, hperm_lt⟩
                · subst hsome
                  dsimp only
                  split
                  · exact .inr ⟨_, _, _, _, _, rfl, hperm_lt⟩
                  · exact .inr ⟨t, o, bp, ib, rs, rfl, hbp⟩
              · rintro ⟨ib, rs, hsome⟩
                subst hsome
                have hblt : Nat.blt entryScore pScore = false := by
                  cases h : Nat.blt entryScore pScore with
                  | false => rfl
                  | true => have := Nat.blt_eq.mp h; omega
                have hbeq : Nat.beq entryScore pScore = false := by
                  cases h : Nat.beq entryScore pScore with
                  | false => rfl
                  | true => have := Nat.beq_eq.mp h; omega
                dsimp only
                rw [hblt]
                dsimp only
                rw [hbeq]
                exact ⟨ib, rs, rfl⟩
  · cases expFlag with
    | false => exact ⟨id, id⟩
    | true =>
      cases targetLive with
      | false => exact ⟨id, id⟩
      | true =>
        cases boffOpt with
        | none => exact ⟨id, id⟩
        | some poff =>
          dsimp only
          have hble : Nat.ble
              (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) poff) addrBits = false := by
            cases h : Nat.ble (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) poff) addrBits with
            | false => rfl
            | true =>
              have hle := Nat.ble_eq.mp h
              subst hbase; subst hscale; subst haddr
              simp only [Nat.add_eq, Nat.mul_eq] at hle
              omega
          rw [hble]
          exact ⟨id, id⟩
  · subst hboff; subst hbound
    cases expFlag with
    | false => exact ⟨id, id⟩
    | true =>
      cases targetLive with
      | false => exact ⟨id, id⟩
      | true =>
        dsimp only
        cases Nat.ble
            (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) placeOff) addrBits with
        | false => exact ⟨id, id⟩
        | true =>
          dsimp only
          have hble_cand : Nat.ble
              (Nat.sub addrBits (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) placeOff))
              bound = false := by
            cases h : Nat.ble
                (Nat.sub addrBits (Nat.add (Nat.mul (Nat.add pageBase bLocal) pageScale) placeOff))
                bound with
            | false => rfl
            | true =>
              have hle := Nat.ble_eq.mp h
              subst hbase; subst hscale; subst haddr
              simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hle
              omega
          rw [hble_cand]
          exact ⟨id, id⟩

private theorem exposedStackStepCore_at_entry
    (pageBase pageScale addrBits : Nat)
    (rawBoundOpt : Option Nat)
    (entryTag entryLocal entryScore relOff : Nat)
    (haddr : Nat.add (Nat.mul (Nat.add pageBase entryLocal) pageScale) relOff = addrBits)
    (restPair : Option (Nat × Nat × Nat × Nat × Nat) × Bool)
    (hrest : restPair.1 = none ∨
      ∃ t o bp ib rs, restPair.1 = some (t, o, bp, ib, rs) ∧ bp < entryScore) :
    ∃ ib rs,
      (exposedStackStepCore pageBase pageScale true true (some relOff) rawBoundOpt
        entryTag entryLocal entryScore addrBits restPair).1 =
      some (entryTag, 0, entryScore, ib, rs) := by
  rcases restPair with ⟨restBest, restAmbig⟩
  dsimp only [exposedStackStepCore] at hrest ⊢
  rw [haddr, Nat.ble_self_eq_true]
  dsimp only
  rw [Nat.sub_eq, Nat.sub_self]
  have hble0 : ∀ bnd : Nat, Nat.ble 0 bnd = true := fun bnd => Nat.ble_eq.mpr (Nat.zero_le bnd)
  rw [hble0]
  dsimp only
  rcases hrest with hnone | ⟨t, o, bp, ib0, rs0, hsome, hbp⟩
  · subst hnone
    exact ⟨_, _, rfl⟩
  · subst hsome
    dsimp only
    have hblt : Nat.blt bp entryScore = true := Nat.blt_eq.mpr hbp
    rw [hblt]
    exact ⟨_, _, rfl⟩

/-- Direct borrow-table structural derivation of `AnnealExposeRoundTripOk` at
`fullAddr = canonicalLocalAddr entry.targetLocal relOff` from tag positivity,
borrow-tag uniqueness (`Nodup`), `bodyDirectBorrowPlaces` membership,
`ExposeTargetSlotOk`, and `NoCompetingExposedBorrow` (without requiring a full
`BorrowsOk` or MiniRust frame witness). -/
theorem AnnealExposeRoundTripOk.of_borrows {body : CapturedMir} {s : MachineState}
    {pv : ProvenancePtr} {entry : BorrowEntry} {pointeeIt : Gen.IntType} {relOff : Nat}
    (htag_ne : pv.tag ≠ 0)
    (hnodup : (s.memory.borrows.map (·.tag)).Nodup)
    (hplace_mem : ⟨entry.targetLocal, entry.targetProjection⟩ ∈ bodyDirectBorrowPlaces body)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hs_len : s.frame.locals.length = body.localDecls.length)
    (hlen_lt : body.localDecls.length < 2 ^ 31)
    (hoff0 : pv.offsetBytes = 0)
    (hlookup : lookupBorrow s.memory.borrows pv.tag = some entry)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨entry.targetLocal, entry.targetProjection⟩ = some (pointeeIt, relOff))
    (hslot_ok : ExposeTargetSlotOk body s entry)
    (hnocomp : NoCompetingExposedBorrow body s pv entry relOff) :
    AnnealExposeRoundTripOk body s pv (canonicalLocalAddr entry.targetLocal relOff) := by
  obtain ⟨hmem_entry, htag_eq⟩ := lookupBorrow_mem_and_tag hlookup
  have hk_lt_decls : entry.targetLocal < body.localDecls.length :=
    (ptrTargetSpec_cases hdeclsOk htspec).1
  have hk_lt_s : entry.targetLocal < s.frame.locals.length := by
    rw [hs_len]; exact hk_lt_decls
  obtain ⟨slot_k, hsk⟩ : ∃ sl, s.frame.locals[entry.targetLocal]? = some sl :=
    ⟨_, List.getElem?_eq_getElem hk_lt_s⟩
  have hsk_nd : slot_k ≠ .dead := fun hc => hslot_ok.1 (hc ▸ hsk)
  have hboff_post : ∀ (localsPost : List LocalSlot),
      (∀ b ∈ s.memory.borrows, localsPost[b.targetLocal]? = s.frame.locals[b.targetLocal]?) →
      MirSemantics.borrowPlaceByteOffset? localsPost s.memory.callerLocals
        body.localDecls body.layouts entry = some relOff := by
    intro localsPost hloc
    refine borrowPlaceByteOffset?_of_ptrTargetSpec htspec (fun hne => ?_)
    obtain ⟨hdlo, dk, v, hdk, hsv, hdslot⟩ := hslot_ok.2 hne
    exact ⟨hdeclsOk, hdlo, hplace_mem, dk, v, hdk, (hloc entry hmem_entry).trans hsv, hdslot⟩
  refine {
    tag_ne_zero := htag_ne
    addr_lt := canonicalLocalAddr_lt_two_pow_64 hdeclsOk hlen_lt htspec
    ptr_addr := fun localsPost hloc => by
      have hoff := hboff_post localsPost hloc
      unfold MirSemantics.ptrAddress?
      rw [hlookup]
      dsimp only [MirSemantics.borrowBaseAddress?]
      rw [hoff, hoff0]
      simp [canonicalLocalAddr, Nat.add_eq, Nat.mul_eq]
    recover_eq := fun localsPost hloc => ?_ }
  let expIds := MirSemantics.recordExposedAllocId s.memory.exposedAllocIds pv.allocId
  let fullAddr := canonicalLocalAddr entry.targetLocal relOff
  have halloc_eq : pv.allocId = pv.tag := rfl
  have hexp_self : MirSemantics.isExposedAllocId expIds entry.tag = true := by
    rw [htag_eq]
    exact (isExposedAllocId_recordExposedAllocId_iff s.memory.exposedAllocIds htag_ne pv.tag).mpr
      (.inl rfl)
  obtain ⟨pre, suf, hsplit, _, hpre_ne, hsuf_ne⟩ :=
    lookupBorrow_split_of_nodup hnodup hlookup
  have hcomp_other : ∀ b ∈ s.memory.borrows, b.tag ≠ pv.tag →
      MirSemantics.isExposedAllocId expIds b.tag = false ∨
      MirSemantics.exposedPermScore b.perm < MirSemantics.exposedPermScore entry.perm ∨
      (entry.targetLocal < b.targetLocal ∧ relOff < 65536) ∨
      (b.targetLocal < entry.targetLocal ∧
        ∃ placeOff bound,
          MirSemantics.borrowPlaceByteOffset? localsPost s.memory.callerLocals
            body.localDecls body.layouts b = some placeOff ∧
          MirSemantics.ptrAllocByteBound? localsPost
            { emptyMemory with
              globals := s.memory.globals
              borrows := [{ b with perm := .active }]
              callerLocals := s.memory.callerLocals }
            body.localDecls body.layouts { allocId := b.tag, offsetBytes := 0 } = some bound ∧
          placeOff + bound < 65536) := by
    intro b hb_mem hne
    cases hexp_b : MirSemantics.isExposedAllocId expIds b.tag with
    | false => exact .inl rfl
    | true =>
      have hexp_old : MirSemantics.isExposedAllocId s.memory.exposedAllocIds b.tag = true := by
        rcases (isExposedAllocId_recordExposedAllocId_iff s.memory.exposedAllocIds htag_ne b.tag).mp
          hexp_b with heq | hold
        · exact absurd heq hne
        · exact hold
      rcases hnocomp b hb_mem hexp_old hne with h1 | h2 | ⟨h3a, h3b⟩
      · exact .inr (.inl h1)
      · exact .inr (.inr (.inl h2))
      · exact .inr (.inr (.inr ⟨h3a, h3b localsPost (hloc b hb_mem)⟩))
  have hsuf_gen : ∀ (bs : List BorrowEntry),
      (∀ b ∈ bs, b ∈ s.memory.borrows ∧ b.tag ≠ pv.tag) →
      let res := MirSemantics.findBestExposedStackBorrow localsPost s.memory.globals
        s.memory.callerLocals expIds body.localDecls body.layouts 8 fullAddr bs
      res.1 = none ∨
        ∃ t o bp ib rs, res.1 = some (t, o, bp, ib, rs) ∧
          bp < MirSemantics.exposedPermScore entry.perm := by
    intro bs
    induction bs with
    | nil => intro _; exact .inl rfl
    | cons b rest ih =>
      intro hmem_bs
      have hrest := ih (fun x hx => hmem_bs x (List.mem_cons_of_mem b hx))
      obtain ⟨hb_mem, hb_ne⟩ := hmem_bs b List.mem_cons_self
      rw [findBestExposedStackBorrow_cons_eq]
      exact (exposedStackStepCore_nonwinning (MirSemantics.stackLocalAddrPageBase 8) 65536 fullAddr
        rfl rfl _ _ _ _ _ _ _ entry.tag entry.targetLocal
        (MirSemantics.exposedPermScore entry.perm) relOff rfl _
        (hcomp_other b hb_mem hb_ne)).1 hrest
  have hsuf_res := hsuf_gen suf (fun b hb_suf =>
    ⟨by rw [hsplit]; exact List.mem_append_right pre (List.mem_cons_of_mem entry hb_suf),
     hsuf_ne b hb_suf⟩)
  have hpost_slot : localsPost[entry.targetLocal]? = some slot_k :=
    (hloc entry hmem_entry).trans hsk
  have htlive_entry :
      (match get? localsPost entry.targetLocal with
       | .some (.init _) => true
       | .some .uninit => true
       | .some .dead => false
       | .none =>
         match get? s.memory.callerLocals entry.targetLocal with
         | .some (.init _) => true
         | .some .uninit => true
         | _ => false) = true := by
    have hg : get? localsPost entry.targetLocal = some slot_k := by simpa [get?] using hpost_slot
    rw [hg]
    cases slot_k with
    | init _ => rfl
    | uninit => rfl
    | dead => exact absurd rfl hsk_nd
  have hentry_res :
      ∃ ib rs,
        (MirSemantics.findBestExposedStackBorrow localsPost s.memory.globals
          s.memory.callerLocals expIds body.localDecls body.layouts 8 fullAddr (entry :: suf)).1 =
        some (entry.tag, 0, MirSemantics.exposedPermScore entry.perm, ib, rs) := by
    rw [findBestExposedStackBorrow_cons_eq, hexp_self, htlive_entry, hboff_post localsPost hloc]
    exact exposedStackStepCore_at_entry (MirSemantics.stackLocalAddrPageBase 8) 65536 fullAddr
      _ entry.tag entry.targetLocal (MirSemantics.exposedPermScore entry.perm) relOff rfl _ hsuf_res
  have hpre_gen : ∀ (bs : List BorrowEntry),
      (∀ b ∈ bs, b ∈ s.memory.borrows ∧ b.tag ≠ pv.tag) →
      ∃ ib rs,
        (MirSemantics.findBestExposedStackBorrow localsPost s.memory.globals
          s.memory.callerLocals expIds body.localDecls body.layouts 8 fullAddr
          (bs ++ entry :: suf)).1 =
        some (entry.tag, 0, MirSemantics.exposedPermScore entry.perm, ib, rs) := by
    intro bs
    induction bs with
    | nil => intro _; simpa using hentry_res
    | cons b rest ih =>
      intro hmem_bs
      have hrest := ih (fun x hx => hmem_bs x (List.mem_cons_of_mem b hx))
      obtain ⟨hb_mem, hb_ne⟩ := hmem_bs b List.mem_cons_self
      simp only [List.cons_append]
      rw [findBestExposedStackBorrow_cons_eq]
      exact (exposedStackStepCore_nonwinning (MirSemantics.stackLocalAddrPageBase 8) 65536 fullAddr
        rfl rfl _ _ _ _ _ _ _ entry.tag entry.targetLocal
        (MirSemantics.exposedPermScore entry.perm) relOff rfl _
        (hcomp_other b hb_mem hb_ne)).2 hrest
  obtain ⟨ib, rs, hbest⟩ := hpre_gen pre (fun b hb_pre =>
    ⟨by rw [hsplit]; exact List.mem_append_left (entry :: suf) hb_pre,
     hpre_ne b hb_pre⟩)
  rw [← hsplit] at hbest
  unfold MirSemantics.recoverExposedPtrValue?
  rcases hpair : MirSemantics.findBestExposedStackBorrow localsPost s.memory.globals
      s.memory.callerLocals expIds body.localDecls body.layouts 8 fullAddr s.memory.borrows with
    ⟨bestOpt, sawAmbig⟩
  rw [hpair] at hbest
  dsimp only at hbest
  subst hbest
  dsimp only
  have hpv_eq : ({ allocId := entry.tag, offsetBytes := 0 } : ProvenancePtr) = pv := by
    cases pv with | mk aid off =>
      dsimp only [ProvenancePtr.tag] at htag_eq hoff0
      subst htag_eq; subst hoff0; rfl
  rw [hpv_eq]

/-- Structural derivation of `AnnealExposeRoundTripOk` at
`fullAddr = canonicalLocalAddr entry.targetLocal relOff` from `BorrowsOk`,
`localDeclOk`, `body.localDecls.length < 2^31`, `ExposeTargetSlotOk`, and
`NoCompetingExposedBorrow`. -/
theorem AnnealExposeRoundTripOk.of_structural {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {pv : ProvenancePtr} {entry : BorrowEntry} {pointeeIt : Gen.IntType} {relOff : Nat}
    (hb : BorrowsOk body ctx view s lm)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hs_len : s.frame.locals.length = body.localDecls.length)
    (hlen_lt : body.localDecls.length < 2 ^ 31)
    (hoff0 : pv.offsetBytes = 0)
    (hlookup : lookupBorrow s.memory.borrows pv.tag = some entry)
    (htspec : ptrTargetSpec body.layouts body.localDecls
      ⟨entry.targetLocal, entry.targetProjection⟩ = some (pointeeIt, relOff))
    (hslot_ok : ExposeTargetSlotOk body s entry)
    (hnocomp : NoCompetingExposedBorrow body s pv entry relOff) :
    AnnealExposeRoundTripOk body s pv (canonicalLocalAddr entry.targetLocal relOff) :=
  AnnealExposeRoundTripOk.of_borrows (hb.lookupBorrow_tag_ne_zero hlookup).1 hb.tags_nodup
    (hb.entries_place entry (lookupBorrow_mem_and_tag hlookup).1)
    hdeclsOk hs_len hlen_lt hoff0 hlookup htspec hslot_ok hnocomp

private theorem opPost_ne_dead {locals : List LocalSlot} {op : MirAst.Operand} {k : Nat}
    (hk : locals[k]? ≠ some .dead) :
    (opPost locals op)[k]? ≠ some .dead := by
  unfold opPost
  cases opMoved op with
  | none => exact hk
  | some j =>
    dsimp only
    split
    · exact hk
    · by_cases hjk : j = k
      · subst hjk
        by_cases hlt : j < locals.length
        · simp [List.getElem?_set_self hlt]
        · rw [List.set_eq_of_length_le (Nat.not_lt.mp hlt)]
          exact hk
      · rwa [List.getElem?_set_ne hjk]

private theorem set_init_ne_dead {locals : List LocalSlot} (i : Nat) (v : Value) {k : Nat}
    (hk : locals[k]? ≠ some .dead) :
    (locals.set i (.init v))[k]? ≠ some .dead := by
  by_cases hik : i = k
  · subst hik
    by_cases hlt : i < locals.length
    · simp [List.getElem?_set_self hlt]
    · rw [List.set_eq_of_length_le (Nat.not_lt.mp hlt)]
      exact hk
  · rwa [List.getElem?_set_ne hik]

private theorem opPost_bool_eq_of_nonbool_decl {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {locals : List LocalSlot} {opA : MirAst.Operand}
    (hokBA : operandOkB layouts decls (copyOp opA) = true)
    {k : Nat} {dk : LocalDecl} (hdk : decls[k]? = some dk)
    (hnot_bool : isBoolTy dk.ty = false) :
    (opPost locals opA)[k]? = locals[k]? := by
  unfold opPost
  cases hm : opMoved opA with
  | none => rfl
  | some j =>
    have hop_eq : opA = .move ⟨j, []⟩ := by
      cases opA with
      | copy _ => simp [opMoved] at hm
      | constant _ => simp [opMoved] at hm
      | move pl =>
        rcases pl with ⟨l, pr⟩
        cases pr with
        | nil => simp [opMoved] at hm; subst hm; rfl
        | cons _ _ => simp [opMoved] at hm
    subst hop_eq
    simp only [copyOp, operandOkB, operandIsBool, operandType, Bool.and_eq_true] at hokBA
    have hjk : j ≠ k := by
      intro heq
      subst heq
      have hb2 := hokBA.2
      rw [hdk] at hb2
      dsimp only [Option.bind_eq_bind, Option.bind_some] at hb2
      unfold scalarTypeOf at hb2
      rw [hnot_bool] at hb2
      cases hisOrd : isOrderingTy dk.ty with
      | true => simp [hisOrd, orderingTy] at hb2
      | false =>
        rw [hisOrd] at hb2
        cases hibt : intBoolTupleOf dk.ty with
        | some it => simp [hibt, intBoolTupleTy] at hb2
        | none =>
          rw [hibt] at hb2
          cases hit_dk : intTypeOf dk.ty <;> simp [hit_dk] at hb2
    dsimp only
    split
    · rfl
    · exact List.getElem?_set_ne hjk

private theorem isBoolTy_false_of_ptrTargetSpec {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    {q : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (htspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff)) :
    ∃ dk, decls[q.local_]? = some dk ∧ isBoolTy dk.ty = false := by
  obtain ⟨_, hcases⟩ := ptrTargetSpec_cases hdeclsOk htspec
  rcases hcases with ⟨_, dk, hdk, hit⟩ |
    ⟨_, _, _, dk, _, _, hdk, ha, _, _⟩ |
    ⟨_, _, _, _, _, _, dk, _, _, _, _, hdk, htu, _⟩
  · refine ⟨dk, hdk, ?_⟩
    cases hb : isBoolTy dk.ty with
    | false => rfl
    | true =>
      unfold isBoolTy at hb
      rcases dk with ⟨_, ⟨k, _⟩, _⟩
      cases k <;> simp [intTypeOf, intTyBytes] at hb hit
  · refine ⟨dk, hdk, ?_⟩
    cases hb : isBoolTy dk.ty with
    | false => rfl
    | true =>
      unfold isBoolTy at hb
      rcases dk with ⟨_, ⟨k, _⟩, _⟩
      cases k <;> simp [arrayTypeOf] at hb ha
  · refine ⟨dk, hdk, ?_⟩
    cases hb : isBoolTy dk.ty with
    | false => rfl
    | true =>
      unfold isBoolTy at hb
      rcases dk with ⟨_, ⟨k, _⟩, _⟩
      cases k <;> simp [tupleTypeOf] at hb htu

private theorem opPost_getElem?_eq_of_ne (locals : List LocalSlot) {op : MirAst.Operand}
    {k j : Nat} (hop : copyOp op = .copy ⟨k, []⟩) (hne : j ≠ k) :
    (opPost locals op)[j]? = locals[j]? := by
  cases op with
  | copy pl => simp [opPost, opMoved]
  | move pl =>
    simp only [copyOp, Operand.copy.injEq] at hop
    subst hop
    simp only [opPost, opMoved]
    split <;> simp [List.getElem?_set_ne hne.symm]
  | constant c => simp [copyOp] at hop

private theorem operandTy_of_copyOp_local {decls : List LocalDecl} {layouts : Layout.LayoutTable}
    {op : MirAst.Operand} {k : Nat} {dk : LocalDecl}
    (hop : copyOp op = .copy ⟨k, []⟩) (hdk : decls[k]? = some dk) :
    MirSemantics.operandTy decls layouts op = some dk.ty := by
  cases op with
  | copy pl =>
    simp only [copyOp, Operand.copy.injEq] at hop
    subst hop
    simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hdk, MirSemantics.resolveProjectedTy]
  | move pl =>
    simp only [copyOp, Operand.copy.injEq] at hop
    subst hop
    simp [MirSemantics.operandTy, MirSemantics.placeTy, get?, hdk, MirSemantics.resolveProjectedTy]
  | constant c => simp [copyOp] at hop

private theorem isExposePtrSourceTy_of_rawPtrPointeeOf {decls : List LocalDecl}
    {layouts : Layout.LayoutTable} {op : MirAst.Operand} {p : Nat} {dp : LocalDecl}
    {mutbl : MirAst.Mutability} {it : Gen.IntType}
    (hop : copyOp op = .copy ⟨p, []⟩) (hdp : decls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (mutbl, it)) :
    MirSemantics.isExposePtrSourceTy (MirSemantics.operandTy decls layouts op) = true := by
  rw [operandTy_of_copyOp_local hop hdp]
  unfold rawPtrPointeeOf at hp_ty
  cases htk : dp.ty.kind with
  | rawPtr m pk =>
    rw [htk] at hp_ty
    obtain ⟨_, hb, _⟩ := Option.map_eq_some_iff.mp hp_ty
    cases hpk : pk <;> rw [hpk] at hb <;> try (simp [intTyBytes] at hb)
    all_goals simp [MirSemantics.isExposePtrSourceTy, MirSemantics.isThinRawPtrTy, htk, hpk]
  | _ => rw [htk] at hp_ty; cases hp_ty

private theorem isExposeIntSourceTy_of_usize {decls : List LocalDecl}
    {layouts : Layout.LayoutTable} {op : MirAst.Operand} {u : Nat} {du : LocalDecl}
    (hop : copyOp op = .copy ⟨u, []⟩) (hdu : decls[u]? = some du)
    (hit_u : intTypeOf du.ty = some usizeIt) :
    MirSemantics.isExposeIntSourceTy 8 (MirSemantics.operandTy decls layouts op) = true ∧
      MirSemantics.operandIsSigned decls op layouts = false := by
  have hop_ty := operandTy_of_copyOp_local (layouts := layouts) hop hdu
  unfold intTypeOf at hit_u
  cases htk : du.ty.kind with
  | uint ut =>
    rw [htk] at hit_u
    cases ut <;> simp [intTyBytes, usizeIt] at hit_u
    all_goals
      simp [MirSemantics.isExposeIntSourceTy, MirSemantics.exposeTargetBytes?,
        MirSemantics.intCastTargetBytes, MirSemantics.operandIsSigned,
        MirSemantics.tyIsSigned, hop_ty, htk]
  | int it =>
    rw [htk] at hit_u
    cases it <;> simp [intTyBytes, usizeIt] at hit_u
  | _ => rw [htk] at hit_u; simp [intTyBytes] at hit_u

/-- **`PointerExposeProvenance` step (MR-3.3 B3).** Anneal's `evalStmt` on
`_i = Cast(PointerExposeProvenance, copy _p, targetTy)` and MiniRust's
`evalTerminator` on the corresponding `Terminator::Intrinsic` both succeed;
the MiniRust step changes `intptrcast` exactly by exposing the loaded pointer
and allocations only in their bytes (`AllocShapeEq`), so `ProvenanceRel`
extends to `pv.tag :: exposedTags` and `ExposedLocalRel` holds for `_i`. Unlike
Pass A2's statement, nothing is assumed about the post-state `m4`. -/
theorem ProvenanceRel.expose_step {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m m1 m2 m3 m4 : Mach} {exposedTags : List Nat}
    {i p fullAddr : Nat} {targetTy : MirAst.Ty} {span : String} {nb : Gen.BbName}
    {retPlace : Gen.Place BM} {argTy : Gen.Type}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = [])
    (hnd : s.frame.locals[i]? ≠ some .dead)
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hoff0 : pv.offsetBytes = 0)
    (hart : AnnealExposeRoundTripOk body s pv fullAddr)
    (hsrc : MirSemantics.isExposePtrSourceTy
      (MirSemantics.operandTy body.localDecls body.layouts (.copy ⟨p, []⟩)) = true)
    (htgt : ExposedTargetOk body ctx s m.mem.memory.allocations pv.tag tProv)
    (hplace : evalPlace m (.Local (localName i)) = .ok ((retPlace, .Int usizeIt), m1))
    (harg : evalValue m1 (.Load (.Local (localName p))) =
      .ok ((.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩, argTy), m2))
    (hstore : placeStore
        { m2 with intptrcast :=
            (IntPtrCast.expose m2.intptrcast { addr := tAddr, provenance := some tProv }) }
        retPlace (.Int tAddr) (.Int usizeIt) = .ok m3)
    (hjump : jumpToBlock m3 nb = .ok m4)
    (hin_bounds : ∃ (idx : Nat) (a : Gen.Allocation),
      tProv = (⟨(idx : Int)⟩, ()) ∧
      m.mem.memory.allocations[idx]? = some a ∧
      a.live = true ∧
      (a.addr : Int) ≤ tAddr ∧
      tAddr ≤ (a.addr : Int) + (Allocation.size a).bytes)
    (hty : MirSemantics.exposeTargetBytes? 8 targetTy = some 8 := by rfl)
    (hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 := by rfl) :
    let locals' := s.frame.locals.set i (.init (.scalar ⟨fullAddr, 8⟩))
    let s' := advanceStmt s locals' (exposeMem s.memory pv.allocId)
    evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance (.copy ⟨p, []⟩) targetTy), span⟩
        body.localDecls body.layouts = .tau (.running s') ∧
    Interp.evalTerminator m
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some nb)) = .ok m4 ∧
    m4.intptrcast = IntPtrCast.expose m.intptrcast ({ addr := tAddr, provenance := some tProv }) ∧
    AllocShapeEq m.mem.memory.allocations m4.mem.memory.allocations ∧
    ProvenanceRel body ctx s' m4 (pv.tag :: exposedTags) ∧
    ExposedLocalRel body ctx locals' s' m4 i pv tAddr tProv fullAddr := by
  have hA := (evalStmt_assign_expose s body.localDecls body.layouts i p targetTy span hi hbor_i
    hprot hty hsrc hptr8).1 pv fullAddr hp (hart.ptr_addr _ (fun _ _ => rfl)) hart.addr_lt hnd
  have hM := evalTerminator_intrinsic_expose_ok hplace harg hstore hjump
  have hm1 := evalPlace_local_eq hplace
  subst hm1
  obtain ⟨hs2, hipc2⟩ := evalValue_load_local_shape harg
  obtain ⟨hs3, hipc3⟩ := placeStore_shape hstore
  obtain ⟨hmem4, hipc4⟩ := jumpToBlock_mem hjump
  have hipc : m4.intptrcast =
      IntPtrCast.expose m1.intptrcast ({ addr := tAddr, provenance := some tProv }) := by
    rw [hipc4, hipc3, hipc2]
  have hshape : AllocShapeEq m1.mem.memory.allocations m4.mem.memory.allocations := by
    rw [hmem4]
    exact hs2.trans hs3
  have hprov0 := (hprov.expose_some tAddr hart.tag_ne_zero htgt).of_shape (m' := m4) hipc hshape
  have hprov4 : ProvenanceRel body ctx
      (advanceStmt s (s.frame.locals.set i (.init (.scalar ⟨fullAddr, 8⟩)))
        (exposeMem s.memory pv.allocId))
      m4 (pv.tag :: exposedTags) :=
    ⟨hprov0.nodup, hprov0.anneal_exposed, hprov0.sound, hprov0.complete⟩
  have hexp_id : MirSemantics.isExposedAllocId
      (MirSemantics.recordExposedAllocId s.memory.exposedAllocIds pv.allocId) pv.allocId = true :=
    (isExposedAllocId_recordExposedAllocId_iff s.memory.exposedAllocIds hart.tag_ne_zero pv.allocId).mpr
      (.inl rfl)
  refine ⟨hA, hM, hipc, hshape, hprov4, ?_⟩
  refine ⟨by simp [hi], hart.addr_lt, ?_, hoff0, hexp_id, htgt.of_shape hshape, ?_, ?_⟩
  · intro localsPost hagree
    refine hart.recover_eq localsPost (fun b hb => ?_)
    have hag := hagree b hb
    dsimp only [advanceStmt] at hag
    rw [hag, List.getElem?_set_ne (hbor_i b hb).symm]
  · rw [hipc, setContains_expose_some_iff]
    exact .inl rfl
  · obtain ⟨idx, a, hpe, ha, hlive, hlo, hhi⟩ := hin_bounds
    obtain ⟨b, hb, hb1, hb2, hb3⟩ := hshape.2 idx a ha
    refine ⟨idx, b, hpe, hb, hb2 ▸ hlive, hb1 ▸ hlo, ?_⟩
    have : (Allocation.size b).bytes = (Allocation.size a).bytes := by
      simp [Allocation.size, hb3]
    rw [hb1, this]
    exact hhi

/-- **`PointerWithExposedProvenance` step (MR-3.3 B3).** From `ExposedLocalRel`
on `_u`, Anneal's `evalStmt` on `_i = Cast(PointerWithExposedProvenance, copy _u,
targetTy)` recovers exactly `pv`; when MiniRust loads `tAddr` from `_u`, the
uniqueness of the angelic resolution (`IntPtrCast.int2ptr_of_unique_candidate`)
makes `int2ptr` return `tProv` as soon as no other live exposed allocation's
range contains `tAddr`, and the step preserves `ProvenanceRel`. Unlike Pass A2's
statement, neither the `int2ptr` result nor anything about the post-state `m4`
is assumed. -/
theorem ProvenanceRel.withExposed_step {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m m1 m2 m3 m4 : Mach} {exposedTags : List Nat}
    {i u fullAddr : Nat} {targetTy : MirAst.Ty} {span : String} {nb : Gen.BbName}
    {retPlace : Gen.Place BM} {retPtrTy : Gen.PtrType} {argTy : Gen.Type}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hexp_loc : ExposedLocalRel body ctx s.frame.locals s m u pv tAddr tProv fullAddr)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = [])
    (hnd : s.frame.locals[i]? ≠ some .dead)
    (hsrc : MirSemantics.isExposeIntSourceTy 8
      (MirSemantics.operandTy body.localDecls body.layouts (.copy ⟨u, []⟩)) = true)
    (hsigned : MirSemantics.operandIsSigned body.localDecls (.copy ⟨u, []⟩) body.layouts = false)
    (hplace : evalPlace m (.Local (localName i)) = .ok ((retPlace, .Ptr retPtrTy), m1))
    (harg : evalValue m1 (.Load (.Local (localName u))) = .ok ((.Int tAddr, argTy), m2))
    (hmeta : PtrType.meta_kind retPtrTy = .None)
    (honly : ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed tAddr,
      q = tProv)
    (hstore : placeStore m2 retPlace
        (.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩)
        (.Ptr retPtrTy) = .ok m3)
    (hjump : jumpToBlock m3 nb = .ok m4)
    (hbad : MirSemantics.isBadWithExposedTargetTy targetTy = false := by rfl)
    (hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 := by rfl) :
    let s' := advanceStmt s (s.frame.locals.set i (.init (.ptr pv 8))) s.memory
    evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerWithExposedProvenance (.copy ⟨u, []⟩) targetTy), span⟩
        body.localDecls body.layouts = .tau (.running s') ∧
    IntPtrCast.int2ptr m2 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
    Interp.evalTerminator m
        (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName u))]
          (.Local (localName i)) (some nb)) = .ok m4 ∧
    m4.intptrcast = m.intptrcast ∧
    AllocShapeEq m.mem.memory.allocations m4.mem.memory.allocations ∧
    ProvenanceRel body ctx s' m4 exposedTags := by
  have hA0 := (evalStmt_assign_withExposed s body.localDecls body.layouts i u targetTy span hi
    hbor_i hprot hbad hsrc hsigned hptr8).1 ⟨fullAddr, 8⟩ (.ptr pv 8)
    hexp_loc.slot_eq rfl hexp_loc.addr_lt hexp_loc.anneal_roundtrip hnd
  have hm1 := evalPlace_local_eq hplace
  subst hm1
  obtain ⟨hs2, hipc2⟩ := evalValue_load_local_shape harg
  obtain ⟨hs3, hipc3⟩ := placeStore_shape hstore
  obtain ⟨hmem4, hipc4⟩ := jumpToBlock_mem hjump
  -- `int2ptr` at `m2` sees `m1`'s exposed set and allocation shapes
  have hcand1 := hexp_loc.candidate_mem
  have hint : IntPtrCast.int2ptr m2 tAddr = .ok { addr := tAddr, provenance := some tProv } := by
    apply IntPtrCast.int2ptr_of_unique_candidate
    · rw [hipc2]; exact hexp_loc.exposed_mem
    · rw [hipc2]
      obtain ⟨i0, a, ha, hlive, hlo, hhi, hexp, hpe⟩ := mem_int2ptrCandidates hcand1
      obtain ⟨b, hb, hb1, hb2, hb3⟩ := hs2.2 i0 a ha
      rw [hpe]
      refine int2ptrCandidates_mem_of hb (hb2 ▸ hlive) (hb1 ▸ hlo) ?_ hexp
      have : (Allocation.size b).bytes = (Allocation.size a).bytes := by
        simp [Allocation.size, hb3]
      rw [hb1, this]
      exact hhi
    · intro q hq
      rw [hipc2] at hq
      obtain ⟨i0, b, hb, hlive, hlo, hhi, hexp, hpe⟩ := mem_int2ptrCandidates hq
      -- transport back to `m1`'s allocations
      have hlen := hs2.1
      have hi0 : i0 < m1.mem.memory.allocations.length := by
        rw [hlen]; exact (List.getElem?_eq_some_iff.mp hb).1
      obtain ⟨a, ha⟩ : ∃ a, m1.mem.memory.allocations[i0]? = some a :=
        ⟨_, List.getElem?_eq_getElem hi0⟩
      obtain ⟨b', hb', hb1, hb2, hb3⟩ := hs2.2 i0 a ha
      rw [hb] at hb'
      cases hb'
      apply honly
      rw [hpe]
      refine int2ptrCandidates_mem_of ha (hb2 ▸ hlive) (hb1 ▸ hlo) ?_ hexp
      have : (Allocation.size b).bytes = (Allocation.size a).bytes := by
        simp [Allocation.size, hb3]
      rw [← hb1, ← this]
      exact hhi
  have hM := evalTerminator_intrinsic_withExposed_ok hplace harg hmeta hint hstore hjump
  have hipc : m4.intptrcast = m1.intptrcast := by rw [hipc4, hipc3, hipc2]
  have hshape : AllocShapeEq m1.mem.memory.allocations m4.mem.memory.allocations := by
    rw [hmem4]
    exact hs2.trans hs3
  exact ⟨hA0, hint, hM, hipc, hshape, (hprov.of_shape hipc hshape).of_advanceStmt _⟩

/-- `ExposedTargetAtAddr` is preserved when replacing `as` with `bs` whose
allocation table is `AllocShapeEq`-related. -/
theorem ExposedTargetAtAddr.of_shape {body : CapturedMir} {ctx : Ctx} {s : MachineState}
    {as bs : List Gen.Allocation} {tag : Nat} {tAddr : Int} {p : Prov}
    (h : ExposedTargetAtAddr body ctx s as tag tAddr p) (hs : AllocShapeEq as bs) :
    ExposedTargetAtAddr body ctx s bs tag tAddr p := by
  obtain ⟨entry, pointeeIt, relOff, alloc, hlk, hk, hspec, hp, halloc, hlive, haddr, hsz, hlo, hhi⟩ := h
  obtain ⟨b, hb, hb1, hb2, hb3⟩ := hs.2 _ alloc halloc
  refine ⟨entry, pointeeIt, relOff, b, hlk, hk, hspec, hp, hb, hb2 ▸ hlive, hb1 ▸ haddr, ?_,
    hb1 ▸ hlo, ?_⟩
  · simpa [Allocation.size, hb3] using hsz
  · simpa [Allocation.size, hb1, hb3] using hhi

/-- Reading back the exact subslice written by `writeSubsliceAtIndex` returns
the written bytes `src`. -/
theorem subsliceWithLength_of_writeSubsliceAtIndex {T : Type} {xs : List T} {start : Int}
    {src ys : List T} (h : writeSubsliceAtIndex xs start src = .ok ys) :
    subsliceWithLength ys start (src.length : Int) = .ok src := by
  have hlen : ys.length = xs.length := writeSubsliceAtIndex_length h
  unfold writeSubsliceAtIndex at h
  split at h
  · next hb =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    have hstart : (start.toNat : Int) = start := Int.toNat_of_nonneg hb.1
    have hle : start.toNat + src.length ≤ xs.length := by omega
    have hys : ys = spliceAt xs start.toNat src := h.symm
    have hle' : start.toNat + src.length ≤ ys.length := by omega
    rw [← hstart, subsliceWithLength_eq_drop_take ys start.toNat src.length hle', hys]
    rw [drop_take_spliceAt_self xs start.toNat src hle]
  · simp [specPanic] at h

/-- `BasicMemory::load` preserves the entire `BasicMemory` unchanged (`mem' = mem`),
because `listSet mem.allocations id._0 allocation` writes back the identical
`allocation` read by `listIndex mem.allocations id._0`. -/
theorem BM.load_eq {mem mem' : BM} {ptr : Ptr} {len : Size} {align : Align}
    {bytes : List Byte} (h : BM.load mem ptr len align = .ok (bytes, mem')) :
    mem' = mem := by
  unfold BM.load at h
  split at h
  · simp [ub] at h
  · obtain ⟨r, _, h⟩ := interpBind_ok h
    cases r with
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    | some t =>
      obtain ⟨id, pe, off⟩ := t
      dsimp only at h
      obtain ⟨alloc, hidx, h⟩ := interpBind_ok h
      obtain ⟨allocs', hs, h⟩ := interpBind_ok h
      obtain ⟨bs, _, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      obtain ⟨_, hget⟩ := listIndex_ok_get hidx
      rw [listSet_ok_eq hs]
      cases mem
      simp only [Gen.BasicMemory.mk.injEq]
      exact ⟨set_self_of_getElem? _ _ _ hget, trivial⟩

/-- `Machine::place_load` preserves `mem.memory`, `intptrcast`, and `threads`
literally (`m'.mem.memory = m.mem.memory ∧ m'.intptrcast = m.intptrcast ∧ m'.threads = m.threads`),
changing only the concurrent access log `m'.mem.accesses`. -/
theorem placeLoad_mem_eq {m m' : Mach} {pl : Gen.Place BM} {ty : Gen.Type} {v : Val}
    (h : placeLoad m pl ty = .ok (v, m')) :
    m'.mem.memory = m.mem.memory ∧ m'.intptrcast = m.intptrcast ∧ m'.threads = m.threads := by
  unfold placeLoad at h
  split at h
  · simp [ub] at h
  · unfold typedLoad at h
    obtain ⟨l, _, h⟩ := interpBind_ok h
    obtain ⟨size, _, h⟩ := interpBind_ok h
    obtain ⟨⟨bytes, cm⟩, hcm, h⟩ := interpBind_ok h
    obtain ⟨dv, _, h⟩ := interpBind_ok h
    unfold CM.load at hcm
    obtain ⟨⟨bytes', mem'⟩, hbm, hcm⟩ := interpBind_ok hcm
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcm
    obtain ⟨_, rfl⟩ := hcm
    cases dv with
    | none => simp [ub] at h
    | some val =>
      dsimp only at h
      obtain ⟨u, _, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨BM.load_eq hbm, rfl, rfl⟩

/-- `evalValue m (.Load (.Local name))` preserves `mem.memory`, `intptrcast`,
and `threads` literally. -/
theorem evalValue_load_local_eq {m m' : Mach} {name : Gen.LocalName} {out : Val × Gen.Type}
    (h : evalValue m (.Load (.Local name)) = .ok (out, m')) :
    m'.mem.memory = m.mem.memory ∧ m'.intptrcast = m.intptrcast ∧ m'.threads = m.threads := by
  unfold evalValue at h
  cases hpl : evalPlace m (.Local name) with
  | error e => simp [hpl, bind, Except.bind] at h
  | ok r =>
    obtain ⟨⟨place, ty⟩, m1⟩ := r
    have hm1 := evalPlace_local_eq hpl
    simp only [hpl, bind, Except.bind] at h
    cases hld : placeLoad m1 place ty with
    | error e => simp [hld] at h
    | ok r2 =>
      obtain ⟨v, m2⟩ := r2
      simp only [hld] at h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have := placeLoad_mem_eq hld
      rw [hm1] at this
      exact this

theorem listIndex_set_self {T : Type} {xs : List T} {i : Int} {x : T} (x' : T)
    (hge : 0 ≤ i) (hget : xs[i.toNat]? = some x) (what : String) :
    listIndex (xs.set i.toNat x') i what = .ok x' := by
  have hlt : i.toNat < xs.length := (List.getElem?_eq_some_iff.mp hget).1
  unfold listIndex
  simp [hge, List.getElem?_set_self hlt, pure, Except.pure]

theorem listSet_set_self {T : Type} {xs : List T} {i : Int} {x : T} (x' : T)
    (hge : 0 ≤ i) (hget : xs[i.toNat]? = some x) (what : String) :
    listSet (xs.set i.toNat x') i x' what = .ok (xs.set i.toNat x') := by
  have hlt : i.toNat < xs.length := (List.getElem?_eq_some_iff.mp hget).1
  unfold listSet
  simp [hge, hlt, List.set_set, pure, Except.pure]

theorem BM.check_ptr_set_data {mem : BM} {ptr : Ptr} {len : Size}
    {id : Gen.AllocId} {pe : Unit} {off : Size} {alloc : Gen.Allocation} {data : List Byte}
    (hchk : BM.check_ptr mem ptr len = .ok (some (id, pe, off)))
    (hidx : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok alloc)
    (hlen : data.length = alloc.data.length) :
    BM.check_ptr { mem with allocations := mem.allocations.set id._0.toNat { alloc with data := data } }
      ptr len = .ok (some (id, pe, off)) := by
  obtain ⟨hge, hget⟩ := listIndex_ok_get hidx
  unfold BM.check_ptr at hchk ⊢
  split at hchk
  · simp [pure, Except.pure] at hchk
  · next hne0 =>
    simp only [hne0, ↓reduceIte]
    cases hp : ptr.provenance with
    | none => simp [hp, ub] at hchk
    | some p =>
      rcases p with ⟨id', pe'⟩
      simp only [hp] at hchk ⊢
      obtain ⟨alloc', hidx', hrest⟩ := interpBind_ok hchk
      split at hrest
      · simp [ub] at hrest
      · next hlive =>
        split at hrest
        · simp [ub] at hrest
        · next hinb =>
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hrest
          rcases hrest with ⟨rfl, _, rfl⟩
          rw [hidx] at hidx'
          cases hidx'
          rw [listIndex_set_self _ hge hget]
          simp only [bind, Except.bind, hlive, Allocation.size, hlen] at hinb ⊢
          simp [hinb, pure, Except.pure]

/-- After `BM.store mem ptr bytes align = .ok mem'`, loading `⟨bytes.length⟩`
bytes back from `ptr` with the same `align` succeeds and returns `(bytes, mem')`. -/
theorem BM.load_of_store {mem mem' : BM} {ptr : Ptr} {bytes : List Byte} {align : Align}
    (h : BM.store mem ptr bytes align = .ok mem') :
    BM.load mem' ptr ⟨bytes.length⟩ align = .ok (bytes, mem') := by
  unfold BM.store at h
  split at h
  · simp [ub] at h
  · next hal =>
    obtain ⟨r, hchk, h⟩ := interpBind_ok h
    cases r with
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      unfold BM.check_ptr at hchk
      split at hchk
      · next hzero =>
        have hnil : bytes = [] := List.eq_nil_of_length_eq_zero hzero
        subst hnil
        unfold BM.load
        simp [hal, BM.check_ptr, pure, Except.pure]
      · cases hp : ptr.provenance with
        | none => simp [hp, ub] at hchk
        | some p =>
          rcases p with ⟨id, pe⟩
          simp only [hp] at hchk
          obtain ⟨alloc, _, hrest⟩ := interpBind_ok hchk
          split at hrest
          · simp [ub] at hrest
          · split at hrest <;> simp [ub, pure, Except.pure] at hrest
    | some t =>
      rcases t with ⟨id, pe, off⟩
      dsimp only at h
      obtain ⟨alloc, hidx, h⟩ := interpBind_ok h
      obtain ⟨data, hw, h⟩ := interpBind_ok h
      obtain ⟨allocs', hs, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hge, hget⟩ := listIndex_ok_get hidx
      have hs_eq := listSet_ok_eq hs
      subst hs_eq
      have hchk' := BM.check_ptr_set_data hchk hidx (writeSubsliceAtIndex_length hw)
      have hidx' := listIndex_set_self { alloc with data := data } hge hget "self.allocations[id.0]"
      have hs' := listSet_set_self { alloc with data := data } hge hget "set"
      have hsub := subsliceWithLength_of_writeSubsliceAtIndex hw
      unfold BM.load
      simp [hal, hchk', bind, Except.bind, hidx', hs', hsub, pure, Except.pure]

/-- After `placeStore m pl (.Int tAddr) (.Int it) = .ok m'` at any valid integer
type `it`, loading `(pl, .Int it)` from any machine `m''` with
`m''.mem.memory = m'.mem.memory` succeeds and returns `.Int tAddr`. -/
theorem placeLoad_of_placeStore_int {m m' m'' : Mach} {pl : Gen.Place BM}
    {it : Gen.IntType} (hgood : GoodSize it.size.bytes) {tAddr : Int}
    (hstore : placeStore m pl (.Int tAddr) (.Int it) = .ok m')
    (hmem : m''.mem.memory = m'.mem.memory) :
    ∃ m_load,
      placeLoad m'' pl (.Int it) = .ok (.Int tAddr, m_load) ∧
      m_load.mem.memory = m''.mem.memory := by
  unfold placeStore at hstore
  split at hstore
  · simp [ub] at hstore
  · next hal =>
    unfold typedStore at hstore
    have hcv_eq : checkValue (.Int tAddr) (.Int it) (some m) =
        ensureElseUb (IntType.can_represent it tAddr) "Value::Int: invalid integer value" := rfl
    cases hrep : IntType.can_represent it tAddr with
    | false =>
      simp [hcv_eq, hrep, ensureElseUb, ub, specPanic, bind, Except.bind] at hstore
    | true =>
      have hcv : checkValue (.Int tAddr) (.Int it) (some m) = .ok () :=
        checkValue_int hrep
      have henc := encode_int it tAddr hgood hrep
      simp only [hcv, henc, bind, Except.bind] at hstore
      obtain ⟨cm, hcm, hstore⟩ := interpBind_ok hstore
      simp only [pure, Except.pure, Except.ok.injEq] at hstore
      subst hstore
      unfold CM.store at hcm
      obtain ⟨mem', hbm, hcm⟩ := interpBind_ok hcm
      simp only [pure, Except.pure, Except.ok.injEq] at hcm
      subst hcm
      dsimp only at hmem
      have hload := BM.load_of_store hbm
      have hblen : (⟨(scalarBytes it (tAddr % 2 ^ (8 * it.size.bytes)).toNat).length⟩ : Size) = it.size := by
        rw [scalarBytes_length]
      rw [hblen, ← hmem] at hload
      have hpos := two_pow_pos (8 * it.size.bytes)
      have h0 := Int.emod_nonneg tAddr (Int.ne_of_gt hpos)
      have h1 := Int.emod_lt_of_pos tAddr hpos
      have hbits_lt : (tAddr % 2 ^ (8 * it.size.bytes)).toNat < 2 ^ (8 * it.size.bytes) := by
        have : ((tAddr % 2 ^ (8 * it.size.bytes)).toNat : Int) < 2 ^ (8 * it.size.bytes) := by
          rw [Int.toNat_of_nonneg h0]; exact h1
        exact_mod_cast this
      have hdec := decode_int_scalarBytes it (tAddr % 2 ^ (8 * it.size.bytes)).toNat hbits_lt
      have hn : 0 < 8 * it.size.bytes := by have := hgood.pos; omega
      have hw := (inBounds_iff tAddr it.signed it.size (by simpa [Size.bits] using hn)).mp hrep
      rw [← eq_intFromBits tAddr it hn (by simpa [Size.bits] using hw.1) (by simpa [Size.bits] using hw.2)] at hdec
      refine ⟨{ m'' with mem := ({ memory := m''.mem.memory, accesses := m''.mem.accesses ++ [⟨.Load, .None, pl.ptr.thin_pointer.addr, it.size⟩] }) }, ?_, rfl⟩
      unfold placeLoad
      simp [hal]
      simp only [typedLoad, layout_eq it hgood, LayoutStrategy.expect_size, bind, Except.bind, CM.load, hload, hdec, checkValue_int hrep, pure, Except.pure]

/-- After `placeStore m pl (.Int tAddr) (.Int usizeIt) = .ok m'`, loading
`(pl, .Int usizeIt)` from any machine `m''` with `m''.mem.memory = m'.mem.memory`
succeeds and returns `.Int tAddr`. -/
theorem placeLoad_of_placeStore_usize {m m' m'' : Mach} {pl : Gen.Place BM} {tAddr : Int}
    (hstore : placeStore m pl (.Int tAddr) (.Int usizeIt) = .ok m')
    (hmem : m''.mem.memory = m'.mem.memory) :
    ∃ m_load,
      placeLoad m'' pl (.Int usizeIt) = .ok (.Int tAddr, m_load) ∧
      m_load.mem.memory = m''.mem.memory :=
  placeLoad_of_placeStore_int (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hstore hmem

theorem placeStore_curFrame {m m' : Mach} {pl : Gen.Place BM} {v : Val} {ty : Gen.Type}
    (h : placeStore m pl v ty = .ok m') :
    curFrame m' = curFrame m := by
  unfold placeStore at h
  split at h
  · simp [ub] at h
  · unfold typedStore at h
    cases hcv : checkValue v ty (some m) with
    | error e => simp [hcv, specPanic, bind, Except.bind] at h
    | ok u =>
      simp only [hcv] at h
      obtain ⟨bytes, _, h⟩ := interpBind_ok h
      obtain ⟨cm, _, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rfl

theorem evalValue_load_local_curFrame {m m' : Mach} {name : Gen.LocalName} {out : Val × Gen.Type}
    (h : evalValue m (.Load (.Local name)) = .ok (out, m')) :
    curFrame m' = curFrame m := by
  unfold evalValue at h
  obtain ⟨⟨⟨place, ty⟩, m1⟩, hpl, h⟩ := interpBind_ok h
  obtain ⟨⟨v, m2⟩, hld, h⟩ := interpBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  have hm1 := evalPlace_local_eq hpl
  subst hm1
  unfold placeLoad at hld
  split at hld
  · simp [ub] at hld
  · unfold typedLoad at hld
    obtain ⟨_, _, hld⟩ := interpBind_ok hld
    obtain ⟨_, _, hld⟩ := interpBind_ok hld
    obtain ⟨_, _, hld⟩ := interpBind_ok hld
    obtain ⟨dv, _, hld⟩ := interpBind_ok hld
    cases dv with
    | none => simp [ub] at hld
    | some val =>
      dsimp only at hld
      obtain ⟨_, _, hld⟩ := interpBind_ok hld
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hld
      obtain ⟨_, rfl⟩ := hld
      rfl

theorem jumpToBlock_curFrame {m m' : Mach} {b : Gen.BbName}
    (h : jumpToBlock m b = .ok m') :
    ∃ fr, curFrame m = .ok fr ∧
      curFrame m' = .ok { fr with next_block := b, next_stmt := 0 } := by
  unfold jumpToBlock mutateCurFrame at h
  obtain ⟨t, ht, h⟩ := interpBind_ok h
  cases hl : t.stack.getLast? with
  | none => simp [hl, specPanic] at h
  | some fr =>
    simp only [hl] at h
    obtain ⟨threads, hs, h⟩ := interpBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hge, hget⟩ := listIndex_ok_get ht
    have hs_eq := listSet_ok_eq hs
    subst hs_eq
    refine ⟨fr, ?_, ?_⟩
    · unfold curFrame
      simp [ht, hl, bind, Except.bind, pure, Except.pure]
    · unfold curFrame activeThread
      rw [listIndex_set_self _ hge hget]
      simp [bind, Except.bind, pure, Except.pure]

theorem evalPlace_local_of_curFrame {m m' : Mach} {name : Gen.LocalName}
    {out : Gen.Place BM × Gen.Type} {fr fr' : Frame}
    (h : evalPlace m (.Local name) = .ok (out, m))
    (hfr : curFrame m = .ok fr) (hfr' : curFrame m' = .ok fr')
    (hfunc : fr'.func = fr.func) (hlocals : fr'.locals = fr.locals) :
    evalPlace m' (.Local name) = .ok (out, m') := by
  unfold evalPlace at h ⊢
  rw [hfr] at h
  rw [hfr']
  simp only [bind, Except.bind, hfunc, hlocals] at h ⊢
  obtain ⟨ty, hty, h⟩ := interpBind_ok h
  rw [hty]
  cases hmg : mapGet fr.locals name with
  | none => simp [hmg, ub] at h
  | some ptr =>
    simpa [hmg, pure, Except.pure] using h

/-- Strengthened `ProvenanceRel.expose_step` (`ProvenanceRel.expose_step_synced`):
from `ExposedTargetAtAddr` (which unifies `ExposedTargetOk` and `hin_bounds`
without a redundant existential) and any root-local operand `op` with
`copyOp op = .copy ⟨p, []⟩` (covering both `.copy ⟨p, []⟩` and `.move ⟨p, []⟩`),
we ALSO establish `ExposedLocalSynced body ctx locals' s' m4 i pv tAddr tProv`,
proving that loading `localName i` at `m4` succeeds and returns `(.Int tAddr, .Int usizeIt)`. -/
theorem ProvenanceRel.expose_step_synced {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m m1 m2 m3 m4 : Mach} {exposedTags : List Nat}
    {i p fullAddr : Nat} {op : MirAst.Operand} {targetTy : MirAst.Ty} {span : String} {nb : Gen.BbName}
    {retPlace : Gen.Place BM} {argTy : Gen.Type}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hop : copyOp op = .copy ⟨p, []⟩)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hbor_p : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ p)
    (hprot : s.memory.activeProtectors = [])
    (hnd : s.frame.locals[i]? ≠ some .dead)
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hoff0 : pv.offsetBytes = 0)
    (hart : AnnealExposeRoundTripOk body s pv fullAddr)
    (hsrc : MirSemantics.isExposePtrSourceTy
      (MirSemantics.operandTy body.localDecls body.layouts op) = true)
    (htgt : ExposedTargetAtAddr body ctx s m.mem.memory.allocations pv.tag tAddr tProv)
    (hplace : evalPlace m (.Local (localName i)) = .ok ((retPlace, .Int usizeIt), m1))
    (harg : evalValue m1 (.Load (.Local (localName p))) =
      .ok ((.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩, argTy), m2))
    (hstore : placeStore
        { m2 with intptrcast :=
            (IntPtrCast.expose m2.intptrcast { addr := tAddr, provenance := some tProv }) }
        retPlace (.Int tAddr) (.Int usizeIt) = .ok m3)
    (hjump : jumpToBlock m3 nb = .ok m4)
    (hty : MirSemantics.exposeTargetBytes? 8 targetTy = some 8 := by rfl)
    (hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 := by rfl) :
    let locals' := (opPost s.frame.locals op).set i
      (.init (.scalar ⟨fullAddr, 8⟩))
    let s' := advanceStmt s locals' (exposeMem s.memory pv.allocId)
    evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op targetTy), span⟩
        body.localDecls body.layouts = .tau (.running s') ∧
    Interp.evalTerminator m
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some nb)) = .ok m4 ∧
    m4.intptrcast = IntPtrCast.expose m.intptrcast ({ addr := tAddr, provenance := some tProv }) ∧
    AllocShapeEq m.mem.memory.allocations m4.mem.memory.allocations ∧
    ProvenanceRel body ctx s' m4 (pv.tag :: exposedTags) ∧
    ExposedLocalSynced body ctx locals' s' m4 i pv tAddr tProv fullAddr := by
  have hop_agree : ∀ b ∈ s.memory.borrows,
      (opPost s.frame.locals op)[b.targetLocal]? = s.frame.locals[b.targetLocal]? :=
    fun b hb => opPost_getElem?_eq_of_ne s.frame.locals hop (hbor_p b hb)
  have hsrc_copy : MirSemantics.isExposePtrSourceTy
      (MirSemantics.operandTy body.localDecls body.layouts (.copy ⟨p, []⟩)) = true := by
    cases op with
    | copy pl => simp only [copyOp, Operand.copy.injEq] at hop; subst hop; exact hsrc
    | move pl =>
      simp only [copyOp, Operand.copy.injEq] at hop; subst hop
      simpa [MirSemantics.operandTy] using hsrc
    | constant c => simp [copyOp] at hop
  have hA := (evalStmt_assign_expose_op s body.localDecls body.layouts i p op targetTy span
    hop hi hbor_i hprot hty hsrc hptr8).1 pv fullAddr hp (hart.ptr_addr _ hop_agree) hart.addr_lt hnd
  have hstep := hprov.expose_step (targetTy := targetTy) (span := span) hi hbor_i hprot hnd
    hp hoff0 hart hsrc_copy htgt.toExposedTargetOk hplace harg hstore hjump htgt.in_bounds hty hptr8
  rcases hstep with ⟨_, hM, hipc, hshape, hprov_copy, hrel_copy⟩
  have hprov' : ProvenanceRel body ctx
      (advanceStmt s ((opPost s.frame.locals op).set i
        (.init (.scalar ⟨fullAddr, 8⟩))) (exposeMem s.memory pv.allocId))
      m4 (pv.tag :: exposedTags) :=
    ⟨hprov_copy.nodup, hprov_copy.anneal_exposed, hprov_copy.sound, hprov_copy.complete⟩
  have hslot_i : ((opPost s.frame.locals op).set i
      (.init (.scalar ⟨fullAddr, 8⟩)))[i]? =
      some (.init (.scalar ⟨fullAddr, 8⟩)) := by
    have hil : i < (opPost s.frame.locals op).length := by rw [opPost_length]; exact hi
    exact List.getElem?_set_self hil
  have hrel' : ExposedLocalRel body ctx
      ((opPost s.frame.locals op).set i (.init (.scalar ⟨fullAddr, 8⟩)))
      (advanceStmt s ((opPost s.frame.locals op).set i
        (.init (.scalar ⟨fullAddr, 8⟩))) (exposeMem s.memory pv.allocId))
      m4 i pv tAddr tProv fullAddr := by
    refine ⟨hslot_i, hart.addr_lt, ?_, hoff0, hrel_copy.anneal_exposed,
      hrel_copy.target_ok, hrel_copy.exposed_mem, hrel_copy.in_bounds⟩
    intro localsPost hagree
    refine hart.recover_eq localsPost (fun b hb => ?_)
    have hag := hagree b hb
    dsimp only [advanceStmt] at hag
    rw [hag, List.getElem?_set_ne (hbor_i b hb).symm, hop_agree b hb]
  refine ⟨hA, hM, hipc, hshape, hprov', ⟨hrel', ?_⟩⟩
  have hm1 := evalPlace_local_eq hplace
  subst hm1
  have hfr_arg := evalValue_load_local_curFrame harg
  have hfr_store := placeStore_curFrame hstore
  obtain ⟨fr3, hfr3, hfr4⟩ := jumpToBlock_curFrame hjump
  have hfr1 : curFrame m1 = .ok fr3 := by
    rw [← hfr_arg]
    exact hfr_store.symm.trans hfr3
  have hpl4 : evalPlace m4 (.Local (localName i)) = .ok ((retPlace, .Int usizeIt), m4) :=
    evalPlace_local_of_curFrame hplace hfr1 hfr4 rfl rfl
  obtain ⟨hmem4, _⟩ := jumpToBlock_mem hjump
  obtain ⟨m_load, hld4, _⟩ := placeLoad_of_placeStore_usize hstore (by rw [hmem4])
  refine ⟨m_load, ?_⟩
  unfold evalValue
  simp [hpl4, hld4, bind, Except.bind, pure, Except.pure]

/-- `ProvenanceRel.withExposed_step_synced`: uses `ExposedLocalSynced` and any
root-local operand `op` with `copyOp op = .copy ⟨u, []⟩` (covering both `.copy`
and `.move`) to step `PointerWithExposedProvenance` on both Anneal and MiniRust. -/
theorem ProvenanceRel.withExposed_step_synced {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m m1 m2 m3 m4 : Mach} {exposedTags : List Nat}
    {i u fullAddr : Nat} {op : MirAst.Operand} {targetTy : MirAst.Ty} {span : String} {nb : Gen.BbName}
    {retPlace : Gen.Place BM} {retPtrTy : Gen.PtrType} {argTy : Gen.Type}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hop : copyOp op = .copy ⟨u, []⟩)
    (hsync : ExposedLocalSynced body ctx s.frame.locals s m u pv tAddr tProv fullAddr)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hbor_u : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ u)
    (hprot : s.memory.activeProtectors = [])
    (hnd : s.frame.locals[i]? ≠ some .dead)
    (hsrc : MirSemantics.isExposeIntSourceTy 8
      (MirSemantics.operandTy body.localDecls body.layouts op) = true)
    (hsigned : MirSemantics.operandIsSigned body.localDecls op body.layouts = false)
    (hplace : evalPlace m (.Local (localName i)) = .ok ((retPlace, .Ptr retPtrTy), m1))
    (harg : evalValue m1 (.Load (.Local (localName u))) = .ok ((.Int tAddr, argTy), m2))
    (hmeta : PtrType.meta_kind retPtrTy = .None)
    (honly : ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed tAddr,
      q = tProv)
    (hstore : placeStore m2 retPlace
        (.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩)
        (.Ptr retPtrTy) = .ok m3)
    (hjump : jumpToBlock m3 nb = .ok m4)
    (hbad : MirSemantics.isBadWithExposedTargetTy targetTy = false := by rfl)
    (hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 := by rfl) :
    let locals' := (opPost s.frame.locals op).set i (.init (.ptr pv 8))
    let s' := advanceStmt s locals' s.memory
    evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerWithExposedProvenance op targetTy), span⟩
        body.localDecls body.layouts = .tau (.running s') ∧
    IntPtrCast.int2ptr m2 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
    Interp.evalTerminator m
        (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName u))]
          (.Local (localName i)) (some nb)) = .ok m4 ∧
    m4.intptrcast = m.intptrcast ∧
    AllocShapeEq m.mem.memory.allocations m4.mem.memory.allocations ∧
    ProvenanceRel body ctx s' m4 exposedTags := by
  have hop_agree : ∀ b ∈ s.memory.borrows,
      (opPost s.frame.locals op)[b.targetLocal]? = s.frame.locals[b.targetLocal]? :=
    fun b hb => opPost_getElem?_eq_of_ne s.frame.locals hop (hbor_u b hb)
  have hsrc_copy : MirSemantics.isExposeIntSourceTy 8
      (MirSemantics.operandTy body.localDecls body.layouts (.copy ⟨u, []⟩)) = true ∧
      MirSemantics.operandIsSigned body.localDecls (.copy ⟨u, []⟩) body.layouts = false := by
    cases op with
    | copy pl => simp only [copyOp, Operand.copy.injEq] at hop; subst hop; exact ⟨hsrc, hsigned⟩
    | move pl =>
      simp only [copyOp, Operand.copy.injEq] at hop; subst hop
      exact ⟨by simpa [MirSemantics.operandTy] using hsrc,
        by simpa [MirSemantics.operandIsSigned, MirSemantics.operandTy] using hsigned⟩
    | constant c => simp [copyOp] at hop
  have hA0 := (evalStmt_assign_withExposed_op s body.localDecls body.layouts i u op targetTy span
    hop hi hbor_i hprot hbad hsrc hsigned hptr8).1 ⟨fullAddr, 8⟩ (.ptr pv 8)
    hsync.toExposedLocalRel.slot_eq rfl hsync.toExposedLocalRel.addr_lt
    (hsync.toExposedLocalRel.recover_eq _ hop_agree) hnd
  have hstep := hprov.withExposed_step (targetTy := targetTy) (span := span)
    hsync.toExposedLocalRel hi hbor_i hprot hnd hsrc_copy.1 hsrc_copy.2
    hplace harg hmeta honly hstore hjump hbad hptr8
  rcases hstep with ⟨_, hint, hM, hipc, hshape, hprov_copy⟩
  exact ⟨hA0, hint, hM, hipc, hshape,
    ⟨hprov_copy.nodup, hprov_copy.anneal_exposed, hprov_copy.sound, hprov_copy.complete⟩⟩

/-- Composed 2-step round-trip simulation (`ProvenanceRel.expose_then_withExposed_step`):
starting from a single-expose state (`m.intptrcast.exposed.elems = []`), executing
`PointerExposeProvenance` (`s -> s1`, `m -> m4`) followed by
`PointerWithExposedProvenance` (`s1 -> s2`, `m4 -> m8`) succeeds on both Anneal
and MiniRust, automatically discharging:
1. the intermediate Anneal slot invariant (`ExposedLocalSynced`),
2. the existence of a valid MiniRust `.Load (.Local (localName i))` evaluation at `m4`
   (`∃ m6, evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6)`), and
3. the uniqueness of the angelic candidate (`honly`) at `m4`. -/
theorem ProvenanceRel.expose_then_withExposed_step {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m m1 m2 m3 m4 : Mach}
    {i p d fullAddr : Nat} {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String} {nb1 nb2 : Gen.BbName}
    {retPlace1 retPlace2 : Gen.Place BM} {argTy1 : Gen.Type} {retPtrTy2 : Gen.PtrType}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hprov : ProvenanceRel body ctx s m [])
    (hempty : m.intptrcast.exposed.elems = [])
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hbor_p : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ p)
    (hprot : s.memory.activeProtectors = [])
    (hnd_i : s.frame.locals[i]? ≠ some .dead)
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hoff0 : pv.offsetBytes = 0)
    (hart : AnnealExposeRoundTripOk body s pv fullAddr)
    (hsrc1 : MirSemantics.isExposePtrSourceTy
      (MirSemantics.operandTy body.localDecls body.layouts op1) = true)
    (htgt : ExposedTargetAtAddr body ctx s m.mem.memory.allocations pv.tag tAddr tProv)
    (hplace1 : evalPlace m (.Local (localName i)) = .ok ((retPlace1, .Int usizeIt), m1))
    (harg1 : evalValue m1 (.Load (.Local (localName p))) =
      .ok ((.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩, argTy1), m2))
    (hstore1 : placeStore
        { m2 with intptrcast :=
            (IntPtrCast.expose m2.intptrcast { addr := tAddr, provenance := some tProv }) }
        retPlace1 (.Int tAddr) (.Int usizeIt) = .ok m3)
    (hjump1 : jumpToBlock m3 nb1 = .ok m4)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hd : d < s.frame.locals.length)
    (hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d)
    (hnd_d : ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩)))[d]? ≠ some .dead)
    (hsrc2 : MirSemantics.isExposeIntSourceTy 8
      (MirSemantics.operandTy body.localDecls body.layouts op2) = true)
    (hsigned2 : MirSemantics.operandIsSigned body.localDecls op2 body.layouts = false)
    (hplace2 : evalPlace m4 (.Local (localName d)) = .ok ((retPlace2, .Ptr retPtrTy2), m4))
    (hmeta2 : PtrType.meta_kind retPtrTy2 = .None)
    (hstore_jump2 : ∀ m6,
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) →
      ∃ m7 m8,
        placeStore m6 retPlace2
          (.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩)
          (.Ptr retPtrTy2) = .ok m7 ∧
        jumpToBlock m7 nb2 = .ok m8)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl)
    (hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 := by rfl) :
    let locals1 := (opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))
    let s1 := advanceStmt s locals1 (exposeMem s.memory pv.allocId)
    let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
    let s2 := advanceStmt s1 locals2 s1.memory
    evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
        body.localDecls body.layouts = .tau (.running s1) ∧
    Interp.evalTerminator m
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some nb1)) = .ok m4 ∧
    evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
        body.localDecls body.layouts = .tau (.running s2) ∧
    ∃ m8,
      Interp.evalTerminator m4
          (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
            (.Local (localName d)) (some nb2)) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 [pv.tag] := by
  obtain ⟨hA1, hM1, hipc1, hshape1, hprov1, hsync1⟩ :=
    hprov.expose_step_synced hop1 hi hbor_i hbor_p hprot hnd_i hp hoff0 hart hsrc1 htgt
      hplace1 harg1 hstore1 hjump1 hty1 hptr8
  rcases hsync1.load_ok with ⟨m6, harg2⟩
  obtain ⟨m7, m8, hstore2, hjump2⟩ := hstore_jump2 m6 harg2
  have honly : ∀ q ∈ int2ptrCandidates m4.mem.memory.allocations m4.intptrcast.exposed tAddr,
      q = tProv := by
    intro q hq
    have hexp : setContains m4.intptrcast.exposed q = true := int2ptrCandidates_exposed hq
    rw [hipc1, setContains_expose_some_iff] at hexp
    rcases hexp with rfl | hold
    · rfl
    · rw [setContains_iff_mem, hempty] at hold
      cases hold
  have hd1 : d < ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))).length := by
    simp [opPost_length, hd]
  obtain ⟨hA2, _, hM2, _, hshape2, hprov2⟩ :=
    hprov1.withExposed_step_synced hop2 hsync1 hd1 hbor_d hbor_i hprot hnd_d hsrc2 hsigned2
      hplace2 harg2 hmeta2 honly hstore2 hjump2 hbad2 hptr8
  exact ⟨hA1, hM1, hA2, m8, hM2, hshape1.trans hshape2, hprov2⟩

/-- `int2ptrCandidates` transports backwards along `AllocShapeEq`. -/
theorem int2ptrCandidates_shape_back {as bs : List Gen.Allocation} {exposed : Set Prov}
    {addr : Int} {q : Prov} (hs : AllocShapeEq as bs)
    (hq : q ∈ int2ptrCandidates bs exposed addr) :
    q ∈ int2ptrCandidates as exposed addr := by
  obtain ⟨i0, b, hb, hlive, hlo, hhi, hexp, hpe⟩ := mem_int2ptrCandidates hq
  have hi0 : i0 < as.length := by
    rw [hs.1]; exact (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨a, ha⟩ : ∃ a, as[i0]? = some a := ⟨_, List.getElem?_eq_getElem hi0⟩
  obtain ⟨b', hb', hb1, hb2, hb3⟩ := hs.2 i0 a ha
  rw [hb] at hb'
  cases hb'
  rw [hpe]
  refine int2ptrCandidates_mem_of ha (hb2 ▸ hlive) (hb1 ▸ hlo) ?_ hexp
  have : (Allocation.size b).bytes = (Allocation.size a).bytes := by
    simp [Allocation.size, hb3]
  rw [← hb1, ← this]
  exact hhi

/-- **Round trip with prior exposures (MR-3.3 B4).** Generalizes
`ProvenanceRel.expose_then_withExposed_step` from an empty exposed set to any
`ProvenanceRel` state in which no *other* live exposed allocation contains the
exposed address (`hnoadj`, e.g. non-adjacent allocations), and exposes the
angelic resolution: the MiniRust `PointerWithExposedProvenance` reloads exactly
`tAddr` from the exposed-address local and `IntPtrCast.int2ptr` reconstructs
exactly the pointer `{ addr := tAddr, provenance := some tProv }` that was loaded
from `_p` before the exposure, while Anneal's destination receives exactly the
`pv` that `_p` held. -/
theorem ProvenanceRel.expose_then_withExposed_reconstructs {body : CapturedMir} {ctx : Ctx}
    {s : MachineState} {m m1 m2 m3 m4 : Mach} {exposedTags : List Nat}
    {i p d fullAddr : Nat} {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String} {nb1 nb2 : Gen.BbName}
    {retPlace1 retPlace2 : Gen.Place BM} {argTy1 : Gen.Type} {retPtrTy2 : Gen.PtrType}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hnoadj : ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed tAddr,
      q = tProv)
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hi : i < s.frame.locals.length)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hbor_p : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ p)
    (hprot : s.memory.activeProtectors = [])
    (hnd_i : s.frame.locals[i]? ≠ some .dead)
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hoff0 : pv.offsetBytes = 0)
    (hart : AnnealExposeRoundTripOk body s pv fullAddr)
    (hsrc1 : MirSemantics.isExposePtrSourceTy
      (MirSemantics.operandTy body.localDecls body.layouts op1) = true)
    (htgt : ExposedTargetAtAddr body ctx s m.mem.memory.allocations pv.tag tAddr tProv)
    (hplace1 : evalPlace m (.Local (localName i)) = .ok ((retPlace1, .Int usizeIt), m1))
    (harg1 : evalValue m1 (.Load (.Local (localName p))) =
      .ok ((.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩, argTy1), m2))
    (hstore1 : placeStore
        { m2 with intptrcast :=
            (IntPtrCast.expose m2.intptrcast { addr := tAddr, provenance := some tProv }) }
        retPlace1 (.Int tAddr) (.Int usizeIt) = .ok m3)
    (hjump1 : jumpToBlock m3 nb1 = .ok m4)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hd : d < s.frame.locals.length)
    (hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d)
    (hnd_d : ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩)))[d]? ≠ some .dead)
    (hsrc2 : MirSemantics.isExposeIntSourceTy 8
      (MirSemantics.operandTy body.localDecls body.layouts op2) = true)
    (hsigned2 : MirSemantics.operandIsSigned body.localDecls op2 body.layouts = false)
    (hplace2 : evalPlace m4 (.Local (localName d)) = .ok ((retPlace2, .Ptr retPtrTy2), m4))
    (hmeta2 : PtrType.meta_kind retPtrTy2 = .None)
    (hstore_jump2 : ∀ m6,
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) →
      ∃ m7 m8,
        placeStore m6 retPlace2
          (.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩)
          (.Ptr retPtrTy2) = .ok m7 ∧
        jumpToBlock m7 nb2 = .ok m8)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl)
    (hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 := by rfl) :
    let locals1 := (opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))
    let s1 := advanceStmt s locals1 (exposeMem s.memory pv.allocId)
    let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
    let s2 := advanceStmt s1 locals2 s1.memory
    evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
        body.localDecls body.layouts = .tau (.running s1) ∧
    Interp.evalTerminator m
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some nb1)) = .ok m4 ∧
    evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
        body.localDecls body.layouts = .tau (.running s2) ∧
    s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
    ∃ m6 m8,
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
          (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
            (.Local (localName d)) (some nb2)) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 (pv.tag :: exposedTags) := by
  obtain ⟨hA1, hM1, hipc1, hshape1, hprov1, hsync1⟩ :=
    hprov.expose_step_synced hop1 hi hbor_i hbor_p hprot hnd_i hp hoff0 hart hsrc1 htgt
      hplace1 harg1 hstore1 hjump1 hty1 hptr8
  rcases hsync1.load_ok with ⟨m6, harg2⟩
  obtain ⟨m7, m8, hstore2, hjump2⟩ := hstore_jump2 m6 harg2
  have honly : ∀ q ∈ int2ptrCandidates m4.mem.memory.allocations m4.intptrcast.exposed tAddr,
      q = tProv := by
    intro q hq
    have hexp : setContains m4.intptrcast.exposed q = true := int2ptrCandidates_exposed hq
    rw [hipc1, setContains_expose_some_iff] at hexp
    rcases hexp with rfl | hold
    · rfl
    · apply hnoadj
      have hq' := int2ptrCandidates_shape_back hshape1 hq
      obtain ⟨i0, a, ha, hlive, hlo, hhi, _, hpe⟩ := mem_int2ptrCandidates hq'
      rw [hpe] at hold ⊢
      exact int2ptrCandidates_mem_of ha hlive hlo hhi hold
  have hd1 : d < ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))).length := by
    simp [opPost_length, hd]
  obtain ⟨hA2, hint, hM2, _, hshape2, hprov2⟩ :=
    hprov1.withExposed_step_synced hop2 hsync1 hd1 hbor_d hbor_i hprot hnd_d hsrc2 hsigned2
      hplace2 harg2 hmeta2 honly hstore2 hjump2 hbad2 hptr8
  refine ⟨hA1, hM1, hA2, ?_, m6, m8, harg2, hint, hM2, hshape1.trans hshape2, hprov2⟩
  have hd2 : d < (opPost ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))) op2).length := by
    simp [opPost_length, hd]
  exact List.getElem?_set_self hd2

/-- Explicit proof that `BorrowsOk.target_ptrs` is vacuously satisfied whenever
`hasProvCast body = true`, because its definition in `Pointers.lean` is guarded
by `inFragment body = true → ...` and `inFragment_not_hasProvCast` proves
`inFragment body = true → hasProvCast body = false`. -/
theorem BorrowsOk.target_ptrs_vacuous_of_hasProvCast {body : CapturedMir}
    (hhas : hasProvCast body = true) :
    inFragment body = false := by
  cases hin : inFragment body
  · rfl
  · have := inFragment_not_hasProvCast hin
    rw [hhas] at this
    contradiction

/-- The facts `BorrowsOk.target_ptrs` provides on `inFragment` bodies, stated
without its `inFragment body = true` guard (which makes it vacuous on every
`inFragmentWithIntrinsics` body with a provenance cast): every address-taken
local `k ∈ bodyAddrTakenLocals body` is live in `view` and mapped in `lm` to
`localPtr ctx k` with a well-aligned in-bounds address. Established at entry on
`inFragmentWithIntrinsics` bodies by `AddrTakenTargetsOk.of_start` and preserved
across operand evaluation and local writes by `AddrTakenTargetsOk.opPost`,
`AddrTakenTargetsOk.set`, and `AddrTakenTargetsOk.set_init`. -/
def AddrTakenTargetsOk (body : CapturedMir) (ctx : Ctx) (view : List LocalSlot)
    (lm : Map Gen.LocalName Ptr) : Prop :=
  ∀ k ∈ bodyAddrTakenLocals body,
    view[k]? ≠ some .dead ∧
    mapGet lm (localName k) = some (localPtr ctx k) ∧
    (∀ d, body.localDecls[k]? = some d →
      isPtrTy d.ty = false ∧
      AddrOk (ctx.addrs.getD k 0) (itOf d body.layouts) ∧
      ctx.addrs.getD k 0 + (tyBytes (tyOf d body.layouts) : Int) < 2 ^ 64)

/-- Connecting `BorrowsOk` directly to `ExposedTargetAtAddr`: for any valid
pointer slot `view[p]? = some (.init (.ptr ptrVal 8))` in `BorrowsOk`, its borrow
tag `ptrVal.tag` resolves to an `entry` targeting an address-taken local
`entry.targetLocal ∈ bodyAddrTakenLocals body` with `ptrVal.offsetBytes = 0`,
and any live allocation `alloc` at `ctx.base.length + entry.targetLocal` with
`alloc.addr = ctx.addrs.getD entry.targetLocal 0` and sufficient size yields
`ExposedTargetAtAddr` at `ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)`. -/
theorem BorrowsOk.exposedTargetAtAddr_of_ptr_slot {body : CapturedMir}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {allocs : List Gen.Allocation}
    {p : Nat} {dp : LocalDecl} {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType}
    {ptrVal : ProvenancePtr}
    (hb : BorrowsOk body ctx view s lm)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (mutbl, pointeeIt))
    (hvp : view[p]? = some (.init (.ptr ptrVal 8)))
    (halloc_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows ptrVal.tag = some entry →
      entry.targetLocal ∈ bodyAddrTakenLocals body →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (pointeeIt, relOff) →
      ∃ alloc,
        allocs[ctx.base.length + entry.targetLocal]? = some alloc ∧
        alloc.live = true ∧
        alloc.addr = ctx.addrs.getD entry.targetLocal 0 ∧
        relOff + pointeeIt.size.bytes ≤ (Allocation.size alloc).bytes) :
    ptrVal.offsetBytes = 0 ∧
    ∃ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      ExposedTargetAtAddr body ctx s allocs ptrVal.tag
        (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int))
        (targetProv ctx entry.targetLocal) := by
  obtain ⟨entry, relOff, hoff0, hlk, hspec⟩ :=
    hb.ptr_slots p dp mutbl pointeeIt ptrVal hdp hp_ty hvp
  have hmem : entry ∈ s.memory.borrows := (lookupBorrow_mem_and_tag hlk).1
  obtain ⟨_, _, _, _, hk, _⟩ := hb.entries_ok entry hmem
  obtain ⟨alloc, halloc, hlive, haddr, hsz⟩ := halloc_ok entry relOff hlk hk hspec
  exact ⟨hoff0, entry, relOff, hlk,
    ExposedTargetAtAddr.of_target_offset hlk hk hspec halloc hlive haddr hsz⟩

/-! ### Pass A4: `FrameOkWithIntrinsics`, `inFragment`-free `evalPtrLoad_withIntrinsics`, and self-contained provenance-cast simulation steps -/

/-- `provCastAliasStmt` does not create or remove any direct borrow (`.rawPtr` or `.ref`). -/
theorem provCastAliasStmt_directBorrow (s : MirAst.Statement) :
    (match (provCastAliasStmt s).kind with
     | .assign _ rv => (directBorrowOf rv).map (fun (p : MirAst.Mutability × MirAst.Place) => p.2.local_)
     | _ => none) =
    (match s.kind with
     | .assign _ rv => (directBorrowOf rv).map (fun (p : MirAst.Mutability × MirAst.Place) => p.2.local_)
     | _ => none) := by
  unfold provCastAliasStmt
  rcases s with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck <;> rfl
    | _ => rfl
  | _ => rfl

/-- `provCastAliasView` preserves `bodyAddrTakenLocals` identically. -/
theorem bodyAddrTakenLocals_provCastAliasView (body : CapturedMir) :
    bodyAddrTakenLocals (provCastAliasView body) = bodyAddrTakenLocals body := by
  unfold provCastAliasView
  split
  · simp only [bodyAddrTakenLocals, List.flatMap_map, List.filterMap_map]
    congr 1
    funext bb
    congr 1
    funext s
    exact provCastAliasStmt_directBorrow s
  · rfl

/-- `provCastAliasStmt` preserves `stmtPreservesAddrTaken` identically. -/
theorem stmtPreservesAddrTaken_provCastAliasStmt (addrLocals : List Nat) (s : MirAst.Statement) :
    stmtPreservesAddrTaken addrLocals (provCastAliasStmt s) =
      stmtPreservesAddrTaken addrLocals s := by
  unfold provCastAliasStmt
  rcases s with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    cases rv with
    | cast ck op ty =>
      cases ck <;> rfl
    | _ => rfl
  | _ => rfl

/-- Every body in `inFragmentWithIntrinsics` satisfies the address-taken target
invariants of `ptrAliasingOk` on the original `body`: every address-taken local
is a non-pointer argument `1 ≤ k ≤ body.argCount`, and every statement and
terminator in `body` preserves `bodyAddrTakenLocals body`. -/
theorem inFragmentWithIntrinsics_addrTaken_spec {body : CapturedMir}
    (h : inFragmentWithIntrinsics body = true) :
    (∀ k ∈ bodyAddrTakenLocals body, 1 ≤ k ∧ k ≤ body.argCount) ∧
    (∀ bb ∈ body.basicBlocks,
      (∀ st ∈ bb.statements, stmtPreservesAddrTaken (bodyAddrTakenLocals body) st = true) ∧
      termPreservesAddrTaken (bodyAddrTakenLocals body) bb.terminator = true) ∧
    (∀ (i : Nat) d, 1 ≤ i → i ≤ body.argCount → body.localDecls[i]? = some d →
      isPtrTy d.ty = false) := by
  have hpa : ptrAliasingOk (provCastAliasView body) = true := by
    simp only [inFragmentWithIntrinsics, Bool.and_eq_true] at h
    exact h.1.2
  have hparams : ∀ d ∈ List.take body.argCount (List.drop 1 body.localDecls),
      isPtrTy d.ty = false := by
    simp only [inFragmentWithIntrinsics, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1.1.1.2
  obtain ⟨haddr0, hpres0, _⟩ := ptrAliasingOk_spec hpa
  have harg_eq : (provCastAliasView body).argCount = body.argCount := by
    unfold provCastAliasView; split <;> rfl
  rw [bodyAddrTakenLocals_provCastAliasView, harg_eq] at haddr0
  rw [bodyAddrTakenLocals_provCastAliasView] at hpres0
  refine ⟨haddr0, ?_, ?_⟩
  · intro bb hbb
    unfold provCastAliasView at hpres0
    split at hpres0
    · have hbb' : ({ bb with statements := bb.statements.map provCastAliasStmt } : BasicBlockData) ∈
          body.basicBlocks.map (fun b => { b with statements := b.statements.map provCastAliasStmt }) :=
        List.mem_map_of_mem hbb
      obtain ⟨hst', hterm'⟩ := hpres0 _ hbb'
      refine ⟨fun st hst => ?_, hterm'⟩
      have hst_map : provCastAliasStmt st ∈ bb.statements.map provCastAliasStmt :=
        List.mem_map_of_mem hst
      have := hst' _ hst_map
      rwa [stmtPreservesAddrTaken_provCastAliasStmt] at this
    · exact hpres0 bb hbb
  · intro i d hi1 hi2 hd
    apply hparams d
    have hget : (List.take body.argCount (List.drop 1 body.localDecls))[i - 1]? = some d := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
      rw [show 1 + (i - 1) = i by omega]
      exact hd
    exact List.mem_of_getElem? hget

/-- `AddrTakenTargetsOk` holds at function entry (`StartRel`) for every body in
`inFragmentWithIntrinsics`. -/
theorem AddrTakenTargetsOk.of_start {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {s : MachineState} {mInit : Mach} {lm : Map Gen.LocalName Ptr}
    (hfrag : inFragmentWithIntrinsics body = true)
    (hstart : StartRel body f ctx s mInit)
    (hlmP : ∀ k < body.argCount + 1, mapGet lm (localName k) = some (localPtr ctx k)) :
    AddrTakenTargetsOk body ctx s.frame.locals lm := by
  obtain ⟨haddrP, _, hnpP⟩ := inFragmentWithIntrinsics_addrTaken_spec hfrag
  intro k hk
  obtain ⟨hk1, hk2⟩ := haddrP k hk
  refine ⟨fun h => hstart.argsLive k .dead hk2 h rfl, hlmP k (by omega),
    fun d hd => ⟨hnpP k d hk1 hk2 hd, (hstart.addrs k d hk2 hd).1,
      Int.lt_trans (hstart.addrs k d hk2 hd).2 (by decide)⟩⟩

/-- Updating a local slot preserves `AddrTakenTargetsOk` whenever address-taken
locals remain non-`.dead`. -/
theorem AddrTakenTargetsOk.set {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hat : AddrTakenTargetsOk body ctx view lm)
    (i : Nat) (slot' : LocalSlot)
    (hdead : i ∈ bodyAddrTakenLocals body → slot' ≠ .dead) :
    AddrTakenTargetsOk body ctx (view.set i slot') lm := by
  intro k hk
  obtain ⟨hnd, hlm, hd⟩ := hat k hk
  refine ⟨?_, hlm, hd⟩
  by_cases hik : i = k
  · subst hik
    by_cases hlt : i < view.length
    · rw [List.getElem?_set_self hlt]
      intro h
      injection h with hs
      exact hdead hk hs
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp
  · rw [List.getElem?_set_ne hik]
    exact hnd

/-- Writing any initialized value `.init v` into local `i` preserves `AddrTakenTargetsOk`. -/
theorem AddrTakenTargetsOk.set_init {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hat : AddrTakenTargetsOk body ctx view lm)
    (i : Nat) (v : Value) :
    AddrTakenTargetsOk body ctx (view.set i (.init v)) lm :=
  hat.set i (.init v) (fun _ => by simp)

/-- Operand post-state `opPost` (which only ever replaces a moved root local with
`.uninit`) unconditionally preserves `AddrTakenTargetsOk`. -/
theorem AddrTakenTargetsOk.opPost {body : CapturedMir} {ctx : Ctx} {view : List LocalSlot}
    {lm : Map Gen.LocalName Ptr} (hat : AddrTakenTargetsOk body ctx view lm)
    (op : MirAst.Operand) :
    AddrTakenTargetsOk body ctx (opPost view op) lm := by
  unfold Correspondence.opPost
  split
  · next j _ =>
    split
    · exact hat
    · exact hat.set j .uninit (fun _ => by simp)
  · exact hat

/-- Any assignment statement satisfying `stmtPreservesAddrTaken` has a
destination local outside `addrLocals`. -/
theorem stmtPreservesAddrTaken_assign_dst_not_mem {addrLocals : List Nat}
    {dst : Place} {rv : Rvalue} {span : String}
    (h : stmtPreservesAddrTaken addrLocals ⟨.assign dst rv, span⟩ = true) :
    dst.local_ ∉ addrLocals := by
  simp only [stmtPreservesAddrTaken, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_mem] at h
  exact decide_eq_false_iff_not.mp h.1

/-- Combining `BorrowsOk` with `stmtPreservesAddrTaken`: no borrow entry targets
the destination local of an assignment that preserves address-taken locals. -/
theorem BorrowsOk.target_ne_of_stmtPreserves {body : CapturedMir} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    (hb : BorrowsOk body ctx view s lm)
    {dst : Place} {rv : Rvalue} {span : String}
    (hpres : stmtPreservesAddrTaken (bodyAddrTakenLocals body) ⟨.assign dst rv, span⟩ = true) :
    ∀ e ∈ s.memory.borrows, e.targetLocal ≠ dst.local_ :=
  hb.target_ne_of_not_addrTaken (stmtPreservesAddrTaken_assign_dst_not_mem hpres)

/-- Local-declaration specification of `translateFnWithIntrinsics`: identical to
the return-place and local-map parts of `translateFn_spec`. -/
theorem translateFnWithIntrinsics_locals {body : CapturedMir} {f : Gen.Function}
    (h : translateFnWithIntrinsics body = some f) :
    f.ret = localName 0 ∧
    ∀ (i : Nat) d, body.localDecls[i]? = some d →
      translateTy body.layouts d.ty = some (tyOf d body.layouts) ∧
        mapGet f.locals (localName i) = some (tyOf d body.layouts) := by
  simp only [translateFnWithIntrinsics, Option.bind_eq_bind] at h
  cases hL : translateLocals body.layouts 0 body.localDecls with
  | none => simp [hL] at h
  | some L =>
    cases hB : translateBlocksWithIntrinsics body.layouts body.localDecls 0
        body.basicBlocks.length body.basicBlocks with
    | none => simp [hL, hB] at h
    | some Bpair =>
      rcases Bpair with ⟨B, initIdx⟩
      cases hC : translateCallConv body.fnAbi.conv with
      | none => simp [hL, hB, hC] at h
      | some conv =>
        simp [hL, hB, hC] at h
        subst h
        refine ⟨rfl, fun i d hd => ?_⟩
        obtain ⟨T, hT, hget⟩ := translateLocals_get body.layouts 0 body.localDecls L hL i d hd
        rw [tyOf_of_translateTy hT]
        exact ⟨hT, by simpa using hget⟩

/-- The `translateFnWithIntrinsics` analogue of `FrameOk`: `f` is the
intrinsic-splitting translation of `body` (`translateFnWithIntrinsics body = some f`),
and the machine runs the callee at `(blk, stmt)` with locals map `lm` agreeing
with `locals` (`LocalsOk`). -/
structure FrameOkWithIntrinsics (body : CapturedMir) (f : Gen.Function) (ctx : Ctx)
    (locals : List LocalSlot) (lm : Map Gen.LocalName Ptr) (m : Mach) (blk stmt : Nat) : Prop where
  hf : translateFnWithIntrinsics body = some f
  shape : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] m.mem.memory.allocations
  locs : LocalsOk body ctx locals lm m.mem.memory.allocations
  declsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true
  nonScalar : NonScalarLive body locals lm

theorem FrameOkWithIntrinsics.mk' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (hf : translateFnWithIntrinsics body = some f)
    {A : List Gen.Allocation} (hs : Shape m ctx [ctx.caller, calleeFrameL f ctx lm blk stmt] A)
    (hlo : LocalsOk body ctx locals lm A)
    (hdeclsOk : ∀ d ∈ body.localDecls, localDeclOk body.layouts d = true)
    (hns : NonScalarLive body locals lm) :
    FrameOkWithIntrinsics body f ctx locals lm m blk stmt := by
  refine ⟨hf, ?_, ?_, hdeclsOk, hns⟩
  · rw [hs.allocs]; exact hs
  · rw [hs.allocs]; exact hlo

theorem FrameOkWithIntrinsics.of_FrameOk {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (hclean : ∀ bb ∈ body.basicBlocks, bb.isCleanup = false)
    (htr : translateFn body = some f)
    (h : FrameOk body f ctx locals lm m blk stmt) :
    FrameOkWithIntrinsics body f ctx locals lm m blk stmt :=
  ⟨translateFnWithIntrinsics_of_translateFn hclean htr, h.shape, h.locs, h.declsOk, h.nonScalar⟩

theorem FrameOkWithIntrinsics.nlocals {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f ctx locals lm m blk stmt) :
    locals.length = body.localDecls.length :=
  h.locs.nlocals

theorem FrameOkWithIntrinsics.slots {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f ctx locals lm m blk stmt) :
    ∀ (i : Nat) d slot, body.localDecls[i]? = some d → locals[i]? = some slot →
      DeclSlotOk d slot body.layouts :=
  h.locs.slots

theorem FrameOkWithIntrinsics.decl_localTy {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) :
    LocalTy (tyOf d body.layouts) (itOf d body.layouts) :=
  localTy_of_declOk (h.declsOk d (List.mem_of_getElem? hd))

theorem FrameOkWithIntrinsics.slot_exists {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f ctx locals lm m blk stmt)
    (i : Nat) (hi : i < body.localDecls.length) :
    ∃ d slot, body.localDecls[i]? = some d ∧ locals[i]? = some slot :=
  ⟨body.localDecls[i], locals[i]'(by rw [h.nlocals]; exact hi), by simp [hi], by simp⟩

theorem FrameOkWithIntrinsics.local_ty {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f ctx locals lm m blk stmt)
    (i : Nat) (d : LocalDecl) (hd : body.localDecls[i]? = some d) :
    mapGet f.locals (localName i) = some (tyOf d body.layouts) :=
  ((translateFnWithIntrinsics_locals h.hf).2 i d hd).2

/-- Pure alignment and `GoodSize` consequences of `ptrTargetSpec` given
well-formed local declarations (`localDeclOk`) and a well-aligned root local
address (`AddrOk`). -/
theorem ptrTargetSpec_aligned_and_good {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    (hdeclsOk : ∀ d ∈ decls, localDeclOk layouts d = true)
    {q : Place} {pointeeIt : Gen.IntType} {relOff : Nat}
    (hspec : ptrTargetSpec layouts decls q = some (pointeeIt, relOff))
    {d : LocalDecl} (hdk : decls[q.local_]? = some d)
    {baseAddr : Int} (haddrOk : AddrOk baseAddr (itOf d layouts)) :
    GoodSize pointeeIt.size.bytes ∧
    Align.is_aligned ⟨pointeeIt.size.bytes⟩ (baseAddr + (relOff : Int)) = true := by
  rcases q with ⟨k, projs⟩
  simp only [] at hdk
  cases projs with
  | nil =>
    simp only [ptrTargetSpec] at hspec
    split at hspec
    · simp only [hdk, Option.bind_eq_bind, Option.bind_some, Option.map_eq_some_iff] at hspec
      obtain ⟨it, hit, heq⟩ := hspec
      injection heq with hit_eq hrel0
      cases hit_eq.symm; cases hrel0.symm
      have hgood := intTypeOf_good hit
      obtain ⟨_, hitd⟩ := tyOf_int (layouts := layouts) hit
      rw [hitd] at haddrOk
      exact ⟨hgood, align_dvd_is_aligned hgood.pos (Nat.dvd_refl _) (Nat.dvd_zero _) haddrOk.1⟩
    · simp at hspec
  | cons p1 prest =>
    cases p1 with
    | constantIndex offset minLen fromEnd =>
      cases prest with
      | nil =>
        simp only [ptrTargetSpec] at hspec
        split at hspec
        · simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
          cases ha : arrayTypeOf d.ty with
          | none => simp [ha] at hspec
          | some apair =>
            obtain ⟨elemIt, count⟩ := apair
            simp only [ha] at hspec
            by_cases hc_bounds : minLen ≤ count ∧
                (if fromEnd then 1 ≤ offset ∧ offset ≤ count else offset < count)
            · simp [hc_bounds] at hspec
              obtain ⟨he1, he2⟩ := hspec
              subst elemIt; subst relOff
              have hgood := arrayTypeOf_good ha
              obtain ⟨_, hitd⟩ := tyOf_array (layouts := layouts) ha
              rw [hitd] at haddrOk
              let idx := if fromEnd then count - offset else offset
              have hdvd : pointeeIt.size.bytes ∣ idx * pointeeIt.size.bytes :=
                ⟨idx, Nat.mul_comm _ _⟩
              exact ⟨hgood, align_dvd_is_aligned hgood.pos (Nat.dvd_refl _) hdvd haddrOk.1⟩
            · simp [hc_bounds] at hspec
        · simp at hspec
      | cons _ _ => simp [ptrTargetSpec] at hspec
    | field idx fieldTy =>
      simp only [ptrTargetSpec] at hspec
      split at hspec
      · simp only [hdk, Option.bind_eq_bind, Option.bind_some] at hspec
        cases ht : tupleTypeOf layouts d.ty with
        | none => simp [ht] at hspec
        | some tpair =>
          obtain ⟨fields, size, align⟩ := tpair
          simp only [ht, Option.bind_some] at hspec
          cases hres : resolveFieldPath layouts (.tuple fields size align)
              (.field idx fieldTy :: prest) with
          | none => simp [hres] at hspec
          | some rpair =>
            obtain ⟨relOff', leafSpec⟩ := rpair
            cases leafSpec with
            | tuple _ _ _ => simp [hres] at hspec
            | scalar leafIt =>
              simp only [hres, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hspec
              obtain ⟨he1, he2⟩ := hspec
              cases he1.symm; cases he2.symm
              have hrootWf : (TupleSpec.tuple fields size align).wf = true := by
                simpa [localDeclOk, scalarTypeOf_none_of_tupleTypeOf ht,
                  arrayTypeOf_none_of_tupleTypeOf ht, ht, isPtrTy_false_of_tupleTypeOf ht] using
                  hdeclsOk d (List.mem_of_getElem? hdk)
              obtain ⟨hleafWf, _⟩ := resolveFieldPath_wf hrootWf hres
              have hgood : GoodSize pointeeIt.size.bytes :=
                (goodAlignBytes_iff pointeeIt.size.bytes).mp hleafWf
              obtain ⟨_, hitd⟩ := tyOf_tupleSpec ht
              rw [hitd] at haddrOk
              obtain ⟨halignDvd, hoffDvd⟩ := resolveFieldPath_align hrootWf hres
              exact ⟨hgood, align_dvd_is_aligned hgood.pos halignDvd hoffDvd haddrOk.1⟩
      · simp at hspec
    | _ => simp [ptrTargetSpec] at hspec

/-- Target-place validity, alignment, dereferenceability, and live stack
allocation witness on `FrameOkWithIntrinsics` and `AddrTakenTargetsOk`, without
an `inFragment body = true` guard. -/
theorem ptrTargetSpec_valid_withIntrinsics {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (q : Place) (pointeeIt : Gen.IntType) (relOff : Nat)
    (hspec : ptrTargetSpec body.layouts body.localDecls q = some (pointeeIt, relOff))
    (hk_addr : q.local_ ∈ bodyAddrTakenLocals body) :
    GoodSize pointeeIt.size.bytes ∧
    0 < (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat ∧
    (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat < 2 ^ 64 ∧
    ({ addr := ((ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat : Int),
       provenance := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()) } : Ptr) =
      offsetPtr (localPtr ctx q.local_) relOff ∧
    Align.is_aligned ⟨pointeeIt.size.bytes⟩ (offsetPtr (localPtr ctx q.local_) relOff).addr = true ∧
    CM.dereferenceable m.mem (offsetPtr (localPtr ctx q.local_) relOff) pointeeIt.size = .ok () ∧
    ∃ alloc,
      m.mem.memory.allocations[ctx.base.length + q.local_]? = some alloc ∧
      alloc.live = true ∧
      alloc.addr = ctx.addrs.getD q.local_ 0 ∧
      relOff + pointeeIt.size.bytes ≤ (Allocation.size alloc).bytes := by
  obtain ⟨d, hdk, hbound⟩ := ptrTargetSpec_bound h.declsOk hspec
  obtain ⟨_, hlm_k, hd_k⟩ := hat q.local_ hk_addr
  obtain ⟨_, haddrOk, haddrMax⟩ := hd_k d hdk
  have hpos_addr : 0 < ctx.addrs.getD q.local_ 0 := haddrOk.2.1
  obtain ⟨hgood, hal0⟩ := ptrTargetSpec_aligned_and_good h.declsOk hspec hdk haddrOk
  have hpos_sz := hgood.pos
  have hk_lt : q.local_ < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdk).1
  obtain ⟨_, slotk, hdk', hsk⟩ := h.slot_exists q.local_ hk_lt
  rw [hdk] at hdk'; cases hdk'
  obtain ⟨allocId, data, hpk, _, _, _, _, hlen, hAk⟩ :=
    h.locs.storage_any hdk hsk hlm_k (h.declsOk d (List.mem_of_getElem? hdk))
  have hid_eq : ctx.base.length + q.local_ = allocId := (prov_inj _ _).mp hpk
  have htpos : 0 < (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat := by omega
  have htlt : (ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat < 2 ^ 64 := by
    have : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by decide
    omega
  have hptrEq :
      ({ addr := ((ctx.addrs.getD q.local_ 0 + (relOff : Int)).toNat : Int),
         provenance := some (⟨((ctx.base.length + q.local_ : Nat) : Int)⟩, ()) } : Ptr) =
      offsetPtr (localPtr ctx q.local_) relOff := by
    simp only [offsetPtr, localPtr]
    rw [Int.toNat_of_nonneg (by omega)]
  have htderef : CM.dereferenceable m.mem (offsetPtr (localPtr ctx q.local_) relOff) pointeeIt.size =
      .ok () :=
    cm_dereferenceable_offsetPtr h.shape (localPtr ctx q.local_) allocId hpk
      (itOf d body.layouts) data hAk relOff pointeeIt.size (by omega)
  refine ⟨hgood, htpos, htlt, hptrEq, by simpa [offsetPtr, localPtr] using hal0, htderef,
    stackAlloc (localPtr ctx q.local_).addr (itOf d body.layouts) data, hid_eq ▸ hAk,
    rfl, rfl, ?_⟩
  simp [Allocation.size, stackAlloc, hlen, hbound]

/-- `evalPtrLoad` generalized to `FrameOkWithIntrinsics` and `AddrTakenTargetsOk`
without the `inFragment body = true` guard, additionally deriving
`ExposedTargetAtAddr` in the initialized pointer branch. -/
theorem evalPtrLoad_withIntrinsics {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (p : Nat) (dp : LocalDecl) (srcMutbl : MirAst.Mutability) (srcIt : Gen.IntType)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt)) :
    (∃ (ptrVal : ProvenancePtr) (entry : BorrowEntry) (relOff : Nat) (m1 : Mach),
      view[p]? = some (.init (.ptr ptrVal 8)) ∧
      ptrVal.offsetBytes = 0 ∧
      lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      ExposedTargetAtAddr body ctx s m.mem.memory.allocations ptrVal.tag
        (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int))
        (targetProv ctx entry.targetLocal) ∧
      evalValue m (.Load (.Local (localName p))) =
        .ok ((.Ptr { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff, metadata := none },
              declPtrTy dp.ty), m1) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m1 blk stmt) ∨
    ((view[p]? = some .uninit ∨ view[p]? = some .dead) ∧
      ∃ msg, evalValue m (.Load (.Local (localName p))) = .error (.ub msg)) := by
  have hp_lt : p < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdp).1
  have hisPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_ty]
  obtain ⟨hTdp, hitdp⟩ := tyOf_isPtrTy (layouts := body.layouts) hisPtr
  have hloc := h.local_ty p dp hdp
  rw [hTdp] at hloc
  obtain ⟨_, slotp, hdp', hsp⟩ := h.slot_exists p hp_lt
  rw [hdp] at hdp'; cases hdp'
  have hslotOk := h.slots p dp slotp hdp hsp
  cases slotp with
  | dead =>
    right
    refine ⟨.inr hsp, ?_⟩
    cases hlm_p : mapGet lm (localName p) with
    | none =>
      exact ⟨"access to a dead local",
        by simp [evalValue, evalPlace_local_none h.shape p (declPtrTy dp.ty) hloc hlm_p]⟩
    | some ptr_p =>
      obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .dead ptr_p hdp hsp hlm_p
      simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
      obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_p id hpid dp.ty hAp
      exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
        placeLoad, hmsg]⟩
  | uninit =>
    right
    refine ⟨.inl hsp, ?_⟩
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ := h.locs.storage p dp .uninit ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, declSlotData_of_isPtrTy hisPtr, hitdp] at hAp
    obtain ⟨msg, hmsg⟩ := typedLoad_ptr_declPtrTy_uninit h.shape ptr_p id hpid dp.ty hAp
    exact ⟨msg, by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
      placeLoad, hmsg]⟩
  | init v =>
    left
    obtain ⟨ptrVal, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtr (.init v)).mp hslotOk
    obtain ⟨entry, relOff, hoff0, hlookup, htspec⟩ :=
      hb.ptr_slots p dp srcMutbl srcIt ptrVal hdp hp_ty hsp
    obtain ⟨hentry_mem, _⟩ := lookupBorrow_mem_and_tag hlookup
    obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry hentry_mem
    obtain ⟨hgood, htpos, htlt, hptrEq, hal, htderef, alloc, halloc, hlive, haddr, hsz⟩ :=
      ptrTargetSpec_valid_withIntrinsics h hat ⟨entry.targetLocal, entry.targetProjection⟩
        srcIt relOff htspec hk_addr
    have htgt_at : ExposedTargetAtAddr body ctx s m.mem.memory.allocations ptrVal.tag
        (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int))
        (targetProv ctx entry.targetLocal) :=
      ExposedTargetAtAddr.of_target_offset hlookup hk_addr htspec halloc hlive haddr hsz
    obtain ⟨ptr_p, hlm_p⟩ := h.locs.some_of_live hsp (by simp)
    obtain ⟨id, hpid, _, _, _, _, hAp⟩ :=
      h.locs.storage p dp (.init (.ptr ptrVal 8)) ptr_p hdp hsp hlm_p
    simp only [hisPtr, ↓reduceIte, hitdp] at hAp
    obtain ⟨tAddr, tProv, htlt0, htgt, hAk⟩ := hAp
    have hbt : (ctxWithBorrows body ctx s.memory.borrows).ptrTargets ptrVal.allocId =
        some ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat,
              some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ())) := by
      simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
      simp [hlookup, htspec]
    obtain ⟨rfl, rfl⟩ := htgt _ _ hbt
    have htal : Align.is_aligned ⟨srcIt.size.bytes⟩
        (((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int)) = true := by
      rw [← hptrEq] at hal
      exact hal
    have htderef' : CM.dereferenceable m.mem
        { addr := ((ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)).toNat : Int),
          provenance := some (⟨((ctx.base.length + entry.targetLocal : Nat) : Int)⟩, ()) }
        srcIt.size = .ok () := by
      rw [← hptrEq] at htderef
      exact htderef
    obtain ⟨m1, hm1, hs1⟩ := typedLoad_ptr_declPtrTy h.shape ptr_p id hpid dp.ty srcMutbl srcIt
      hp_ty hgood _ htpos htlt0 _ htal htderef' hAk
    rw [hptrEq] at hm1
    refine ⟨ptrVal, entry, relOff, m1, hsp, hoff0, hlookup, hk_addr, htspec, htgt_at,
      by simp [evalValue, evalPlace_local_some h.shape p (declPtrTy dp.ty) hloc ptr_p hlm_p,
        placeLoad, hm1],
      FrameOkWithIntrinsics.mk' h.hf hs1 h.locs h.declsOk h.nonScalar⟩

/-- `placeLoad` preserves `active_thread`. -/
theorem placeLoad_active_thread {m m' : Mach} {pl : Gen.Place BM} {ty : Gen.Type} {v : Val}
    (h : placeLoad m pl ty = .ok (v, m')) :
    m'.active_thread = m.active_thread := by
  unfold placeLoad at h
  split at h
  · simp [ub] at h
  · unfold typedLoad at h
    obtain ⟨l, _, h⟩ := interpBind_ok h
    obtain ⟨size, _, h⟩ := interpBind_ok h
    obtain ⟨⟨bytes, cm⟩, _, h⟩ := interpBind_ok h
    obtain ⟨dv, _, h⟩ := interpBind_ok h
    cases dv with
    | none => simp [ub] at h
    | some val =>
      dsimp only at h
      obtain ⟨u, _, h⟩ := interpBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rfl

/-- `evalValue m (.Load (.Local name))` preserves `Shape` identically. -/
theorem evalValue_load_local_preserves_shape {m m' : Mach} {ctx : Ctx}
    {frames : List Frame} {allocs : List Gen.Allocation}
    {name : Gen.LocalName} {out : Val × Gen.Type}
    (hsh : Shape m ctx frames allocs)
    (h : evalValue m (.Load (.Local name)) = .ok (out, m')) :
    Shape m' ctx frames allocs := by
  obtain ⟨hmem, _, hthr⟩ := evalValue_load_local_eq h
  refine ⟨hthr.trans hsh.threads, ?_, ?_⟩
  · unfold evalValue at h
    cases hpl : evalPlace m (.Local name) with
    | error e => simp [hpl, bind, Except.bind] at h
    | ok r =>
      obtain ⟨⟨place, ty⟩, m1⟩ := r
      have hm1 := evalPlace_local_eq hpl
      simp only [hpl, bind, Except.bind] at h
      cases hld : placeLoad m1 place ty with
      | error e => simp [hld] at h
      | ok r2 =>
        obtain ⟨v, m2⟩ := r2
        simp only [hld] at h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        rw [placeLoad_active_thread hld, hm1, hsh.active]
  · rw [hmem, hsh.allocs]

/-- `PointerExposeProvenance` simulation step from `FrameOkWithIntrinsics`,
`BorrowsOk`, `AddrTakenTargetsOk`, and `ProvenanceRel`: derives BOTH the
Anneal-side `AnnealExposeRoundTripOk` at `fullAddr = canonicalLocalAddr
entry.targetLocal relOff` (from `ExposeTargetSlotOk` + `NoCompetingExposedBorrow`)
AND the MiniRust-side `evalPlace`, pointer load, `ExposedTargetAtAddr`,
`placeStore`, and `jumpToBlock` directly from the frame and borrow invariants,
preserving `FrameOkWithIntrinsics` and `AddrTakenTargetsOk`. -/
theorem ProvenanceRel.expose_step_from_frameOk {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat} {exposedTags : List Nat}
    {i p : Nat} {di dp : LocalDecl} {srcMutbl : MirAst.Mutability} {srcIt : Gen.IntType}
    {op : MirAst.Operand} {targetTy : MirAst.Ty} {span : String} {nb : Nat}
    {pv : ProvenancePtr}
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hop : copyOp op = .copy ⟨p, []⟩)
    (hs_len : s.frame.locals.length = body.localDecls.length)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = [])
    (hnd_i : s.frame.locals[i]? ≠ some .dead)
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hexp_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ExposeTargetSlotOk body s entry ∧
      NoCompetingExposedBorrow body s pv entry relOff)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty : MirSemantics.exposeTargetBytes? 8 targetTy = some 8 := by rfl) :
    ∃ (entry : BorrowEntry) (relOff : Nat) (m4 : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let locals' := (opPost s.frame.locals op).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let view' := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s' := advanceStmt s locals' (exposeMem s.memory pv.allocId)
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      AnnealExposeRoundTripOk body s pv fullAddr ∧
      0 < tAddr.toNat ∧ tAddr.toNat < 2 ^ 64 ∧ (tAddr.toNat : Int) = tAddr ∧
      ExposedTargetAtAddr body ctx s m.mem.memory.allocations pv.tag tAddr tProv ∧
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op targetTy), span⟩
          body.localDecls body.layouts = .tau (.running s') ∧
      Interp.evalTerminator m
          (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
            (.Local (localName i)) (some (bbName nb))) = .ok m4 ∧
      m4.intptrcast = IntPtrCast.expose m.intptrcast { addr := tAddr, provenance := some tProv } ∧
      AllocShapeEq m.mem.memory.allocations m4.mem.memory.allocations ∧
      ProvenanceRel body ctx s' m4 (pv.tag :: exposedTags) ∧
      ExposedLocalSynced body ctx locals' s' m4 i pv tAddr tProv fullAddr ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s'.memory.borrows) view' lm m4 nb 0 ∧
      AddrTakenTargetsOk body ctx view' lm := by
  have hp_pty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt) :=
    (ptrPointeeOf_of_rawPtrPointeeOf hp_ty).1
  have hp_isPtr : isPtrTy dp.ty = true := by simp [isPtrTy, hp_pty]
  have hp_not_addr : p ∉ bodyAddrTakenLocals body := fun hp_in => by
    have hf := ((hat p hp_in).2.2 dp hdp).1
    rw [hp_isPtr] at hf; cases hf
  have hbor_p : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ p :=
    hb.target_ne_of_not_addrTaken hp_not_addr
  have hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 :=
    layoutPointerBytes_of_localDeclOk_isPtrTy (hframe.declsOk dp (List.mem_of_getElem? hdp)) hp_isPtr
  have hsrc : MirSemantics.isExposePtrSourceTy
      (MirSemantics.operandTy body.localDecls body.layouts op) = true :=
    isExposePtrSourceTy_of_rawPtrPointeeOf hop hdp hp_ty
  rcases evalPtrLoad_withIntrinsics hframe hb hat p dp srcMutbl srcIt hdp hp_pty with
    ⟨ptrVal, entry, relOff, m2, hvp', hoff0, hlookup, hk_addr, htspec, htgt_at, harg, hframe2⟩ |
    ⟨hnot, _⟩
  · rw [hview_p] at hvp'
    injection hvp' with hinit_eq
    injection hinit_eq with hpv_val_eq
    injection hpv_val_eq with hpv_eq _
    subst ptrVal
    obtain ⟨hslot_ok, hnocomp⟩ := hexp_ok entry relOff hlookup htspec
    have hart : AnnealExposeRoundTripOk body s pv (canonicalLocalAddr entry.targetLocal relOff) :=
      AnnealExposeRoundTripOk.of_structural hb hframe.declsOk hs_len hlen_lt hoff0
        hlookup htspec hslot_ok hnocomp
    obtain ⟨_, htpos, htlt, _, _, _, _⟩ :=
      ptrTargetSpec_valid_withIntrinsics hframe hat ⟨entry.targetLocal, entry.targetProjection⟩
        srcIt relOff htspec hk_addr
    dsimp only at htpos htlt
    let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
    let tProv : Prov := targetProv ctx entry.targetLocal
    have htAddr_nn : 0 ≤ tAddr := by omega
    have htAddr_cast : (tAddr.toNat : Int) = tAddr := Int.toNat_of_nonneg htAddr_nn
    have hi_decl : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
    have hi : i < s.frame.locals.length := by rw [hs_len]; exact hi_decl
    obtain ⟨_, sloti, _, hsi⟩ := hframe.slot_exists i hi_decl
    obtain ⟨ptr_i, hpi⟩ := hframe.locs.some_of_live hsi (fun hc => hview_i (hc ▸ hsi))
    obtain ⟨hTi, hiti⟩ := tyOf_int (layouts := body.layouts) hit_i
    have hloc_i := hframe.local_ty i di hdi
    rw [hTi] at hloc_i
    have hplace : evalPlace m (.Local (localName i)) =
        .ok (({ ptr := { thin_pointer := ptr_i, metadata := none }, aligned := true },
              .Int usizeIt), m) :=
      evalPlace_local_some hframe.shape i (.Int usizeIt) hloc_i ptr_i hpi
    let m2_exp : Mach :=
      { m2 with intptrcast := IntPtrCast.expose m2.intptrcast { addr := tAddr, provenance := some tProv } }
    have hshape_exp : Shape m2_exp (ctxWithBorrows body ctx s.memory.borrows)
        [_, calleeFrameL f _ lm blk stmt] m2.mem.memory.allocations :=
      ⟨hframe2.shape.threads, hframe2.shape.active, hframe2.shape.allocs⟩
    obtain ⟨k, hpk, _⟩ := hframe2.locs.storage i di sloti ptr_i hdi hsi hpi
    have hnotPtr_i : isPtrTy di.ty = false := by
      cases htk : di.ty.kind <;> simp [intTypeOf, intTyBytes, isPtrTy, ptrPointeeOf, htk] at hit_i ⊢
    obtain ⟨_, _, _, _, hAi⟩ := hframe2.locs.storage_id hdi hsi hpi hpk hnotPtr_i
    have hFragUsize : FragTy (.Int usizeIt) usizeIt :=
      .int usizeIt (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hvb : ValidBits (.Int usizeIt) tAddr.toNat := htlt
    rw [hiti] at hAi
    have hlen_i : (declSlotData di sloti body.layouts).length = usizeIt.size.bytes := by
      have hFragDi : FragTy (tyOf di body.layouts) (itOf di body.layouts) := by
        rw [hTi, hiti]; exact hFragUsize
      rw [hFragDi.declSlotData, hiti]
      exact slotData_length _ _
    have hst := typedStore_ptr_frag hshape_exp ptr_i k hpk hFragUsize
      (declSlotData di sloti body.layouts) tAddr.toNat hvb hAi hlen_i
    have hval_eq : valOf (.Int usizeIt) tAddr.toNat = .Int tAddr := by
      simp [valOf, intFromBits, usizeIt, htAddr_cast]
    rw [hval_eq] at hst
    let m3 := withMem m2_exp
      (m2.mem.memory.allocations.set k (stackAlloc ptr_i.addr usizeIt (scalarBytes usizeIt tAddr.toNat)))
      ⟨.Store, .None, ptr_i.addr, usizeIt.size⟩
    have hstore : placeStore m2_exp
        { ptr := { thin_pointer := ptr_i, metadata := none }, aligned := true }
        (.Int tAddr) (.Int usizeIt) = .ok m3 := hst
    have hshape3 : Shape m3 (ctxWithBorrows body ctx s.memory.borrows)
        [_, calleeFrameL f _ lm blk stmt]
        (m2.mem.memory.allocations.set k (stackAlloc ptr_i.addr usizeIt (scalarBytes usizeIt tAddr.toNat))) :=
      withMem_shape hshape_exp _
    obtain ⟨m4, hjump, hshape4⟩ := jumpToBlock_callee hshape3 nb
    have harg' : evalValue m (.Load (.Local (localName p))) =
        .ok ((.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩, declPtrTy dp.ty), m2) :=
      harg
    obtain ⟨hA, hM, hipc, hshape_eq, hprov', hsync'⟩ :=
      hprov.expose_step_synced hop hi hbor_i hbor_p hprot hnd_i hp hoff0 hart hsrc htgt_at
        hplace harg' hstore hjump hty hptr8
    have hFragDi : FragTy (tyOf di body.layouts) (itOf di body.layouts) := by
      rw [hTi, hiti]; exact hFragUsize
    have hslot_ok' : DeclSlotOk di (.init (.scalar ⟨tAddr.toNat, 8⟩)) body.layouts := by
      rw [hFragDi.declSlotOk]
      refine ⟨by simp [hTi, tyBytes, usizeIt], ?_⟩
      rw [hTi]; exact hvb
    have hlo3 := hframe2.locs.store i di hdi sloti (.init (.scalar ⟨tAddr.toNat, 8⟩))
      hsi (by simp) hslot_ok' ptr_i hpi k hpk (.inl hnotPtr_i)
    rw [hFragDi.declSlotData, hiti] at hlo3
    have hframe4 : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
        (view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))) lm m4 nb 0 :=
      FrameOkWithIntrinsics.mk' hframe.hf hshape4 hlo3 hframe.declsOk
        (hframe.nonScalar.set_init i _)
    exact ⟨entry, relOff, m4, hlookup, htspec, hart, htpos, htlt, htAddr_cast, htgt_at,
      hA, hM, hipc, hshape_eq, hprov', hsync', hframe4, hat.set_init i _⟩
  · rcases hnot with hu | hd_dead
    · rw [hview_p] at hu; cases hu
    · rw [hview_p] at hd_dead; cases hd_dead

/-- Self-contained `PointerWithExposedProvenance` simulation step from
`FrameOkWithIntrinsics`, `AddrTakenTargetsOk`, `ProvenanceRel`, and
`ExposedLocalSynced`: derives `evalPlace` (`hplace`), the integer load (`harg`),
`placeStore` (`hstore`), and `jumpToBlock` (`hjump`) without external MiniRust
step hypotheses, and preserves `FrameOkWithIntrinsics` and `AddrTakenTargetsOk`. -/
theorem ProvenanceRel.withExposed_step_from_frameOk {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat} {exposedTags : List Nat}
    {d u fullAddr : Nat} {dd : LocalDecl} {dstMutbl : MirAst.Mutability} {dstIt : Gen.IntType}
    {op : MirAst.Operand} {targetTy : MirAst.Ty} {span : String} {nb : Nat}
    {pv : ProvenancePtr} {tAddr : Int} {tProv : Prov}
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hsync : ExposedLocalSynced body ctx s.frame.locals s m u pv tAddr tProv fullAddr)
    (hop : copyOp op = .copy ⟨u, []⟩)
    (hs_len : s.frame.locals.length = body.localDecls.length)
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d)
    (hbor_u : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ u)
    (hprot : s.memory.activeProtectors = [])
    (hnd_d : s.frame.locals[d]? ≠ some .dead)
    (hview_d : view[d]? ≠ some .dead)
    (hsrc_u : MirSemantics.isExposeIntSourceTy 8
      (MirSemantics.operandTy body.localDecls body.layouts op) = true)
    (hsigned_u : MirSemantics.operandIsSigned body.localDecls op body.layouts = false)
    (htAddr_nn : 0 ≤ tAddr)
    (htlt : tAddr.toNat < 2 ^ 64)
    (htgt_ctx : ∀ a pr,
      (ctxWithBorrows body ctx s.memory.borrows).ptrTargets pv.allocId = some (a, pr) →
      tAddr.toNat = a ∧ some tProv = pr)
    (honly : ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed tAddr,
      q = tProv)
    (hbad : MirSemantics.isBadWithExposedTargetTy targetTy = false := by rfl) :
    let locals' := (opPost s.frame.locals op).set d (.init (.ptr pv 8))
    let view' := view.set d (.init (.ptr pv 8))
    let s' := advanceStmt s locals' s.memory
    evalStmt s ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op targetTy), span⟩
        body.localDecls body.layouts = .tau (.running s') ∧
    ∃ m2 m4,
      evalValue m (.Load (.Local (localName u))) = .ok ((.Int tAddr, .Int usizeIt), m2) ∧
      IntPtrCast.int2ptr m2 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m
          (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName u))]
            (.Local (localName d)) (some (bbName nb))) = .ok m4 ∧
      m4.intptrcast = m.intptrcast ∧
      AllocShapeEq m.mem.memory.allocations m4.mem.memory.allocations ∧
      ProvenanceRel body ctx s' m4 exposedTags ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s'.memory.borrows) view' lm m4 nb 0 ∧
      AddrTakenTargetsOk body ctx view' lm := by
  have hd_decl : d < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdd).1
  have hd : d < s.frame.locals.length := by rw [hs_len]; exact hd_decl
  have hp_ty_d : isPtrTy dd.ty = true := by
    simp [isPtrTy, (ptrPointeeOf_of_rawPtrPointeeOf hd_ty).1]
  have hptr8 : MirSemantics.layoutPointerBytes body.layouts = 8 :=
    layoutPointerBytes_of_localDeclOk_isPtrTy (hframe.declsOk dd (List.mem_of_getElem? hdd)) hp_ty_d
  obtain ⟨hTd, hitd⟩ := tyOf_isPtrTy (layouts := body.layouts) hp_ty_d
  have hraw_d : declPtrTy dd.ty = thinRawPtrTy := declPtrTy_of_rawPtrPointeeOf hd_ty
  have hloc_d := hframe.local_ty d dd hdd
  rw [hTd, hraw_d] at hloc_d
  obtain ⟨_, slotd, _, hsd⟩ := hframe.slot_exists d hd_decl
  obtain ⟨ptr_d, hpd⟩ := hframe.locs.some_of_live hsd (fun hc => hview_d (hc ▸ hsd))
  have hplace : evalPlace m (.Local (localName d)) =
      .ok (({ ptr := { thin_pointer := ptr_d, metadata := none }, aligned := true },
            thinRawPtrTy), m) :=
    evalPlace_local_some hframe.shape d thinRawPtrTy hloc_d ptr_d hpd
  obtain ⟨m2, harg⟩ := hsync.load_ok
  have hshape2 : Shape m2 (ctxWithBorrows body ctx s.memory.borrows)
      [_, calleeFrameL f _ lm blk stmt] m.mem.memory.allocations :=
    evalValue_load_local_preserves_shape hframe.shape harg
  obtain ⟨k, data, hpk, _, _, _, _, hlen, hAd⟩ :=
    hframe.locs.storage_any hdd hsd hpd (hframe.declsOk dd (List.mem_of_getElem? hdd))
  rw [hTd, tyBytes_declPtrTy] at hlen
  rw [hitd] at hAd
  have hst := typedStore_ptr_thinRawPtr hshape2 ptr_d k hpk data tAddr.toNat htlt (some tProv) hAd hlen
  have htAddr_cast : (tAddr.toNat : Int) = tAddr := Int.toNat_of_nonneg htAddr_nn
  rw [htAddr_cast] at hst
  let m3 := withMem m2
    (m.mem.memory.allocations.set k (stackAlloc ptr_d.addr usizeIt (ptrBytes tAddr.toNat (some tProv))))
    ⟨.Store, .None, ptr_d.addr, ⟨8⟩⟩
  have hstore : placeStore m2
      { ptr := { thin_pointer := ptr_d, metadata := none }, aligned := true }
      (.Ptr ⟨{ addr := tAddr, provenance := some tProv }, none⟩)
      thinRawPtrTy = .ok m3 := hst
  have hshape3 : Shape m3 (ctxWithBorrows body ctx s.memory.borrows)
      [_, calleeFrameL f _ lm blk stmt]
      (m.mem.memory.allocations.set k (stackAlloc ptr_d.addr usizeIt (ptrBytes tAddr.toNat (some tProv)))) :=
    withMem_shape hshape2 _
  obtain ⟨m4, hjump, hshape4⟩ := jumpToBlock_callee hshape3 nb
  obtain ⟨hA, hint, hM, hipc, hshape_eq, hprov'⟩ :=
    hprov.withExposed_step_synced hop hsync hd hbor_d hbor_u hprot hnd_d hsrc_u hsigned_u
      hplace harg rfl honly hstore hjump hbad hptr8
  have hlo3 := hframe.locs.store_ptr d dd hdd hp_ty_d slotd hsd pv tAddr.toNat (some tProv)
    htlt htgt_ctx ptr_d hpd k hpk
  rw [hitd] at hlo3
  have hframe4 : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      (view.set d (.init (.ptr pv 8))) lm m4 nb 0 :=
    FrameOkWithIntrinsics.mk' hframe.hf hshape4 hlo3 hframe.declsOk
      (hframe.nonScalar.set_init d _)
  exact ⟨hA, m2, m4, harg, hint, hM, hipc, hshape_eq, hprov', hframe4, hat.set_init d _⟩

/-- Complete 2-step round-trip simulation (`ProvenanceRel.expose_then_withExposed_from_frameOk`):
composes `expose_step_from_frameOk` and `withExposed_step_from_frameOk` starting
from `FrameOkWithIntrinsics`, `BorrowsOk`, `AddrTakenTargetsOk`, and `ProvenanceRel`
with **zero** external MiniRust `evalPlace`, `evalValue`, `placeStore`, `jumpToBlock`,
or `ExposedTargetAtAddr` hypotheses and **zero** opaque `AnnealExposeRoundTripOk`
hypothesis (`hart` is derived structurally at
`fullAddr = canonicalLocalAddr entry.targetLocal relOff` from `ExposeTargetSlotOk`
and `NoCompetingExposedBorrow`), while establishing `FrameOkWithIntrinsics` and
`AddrTakenTargetsOk` in the post-state. -/
theorem ProvenanceRel.expose_then_withExposed_from_frameOk {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat} {exposedTags : List Nat}
    {i p d : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String} {nb1 nb2 : Nat}
    {pv : ProvenancePtr}
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hs_len : s.frame.locals.length = body.localDecls.length)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = [])
    (hnd_i : s.frame.locals[i]? ≠ some .dead)
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d)
    (hnd_d : s.frame.locals[d]? ≠ some .dead)
    (hview_d : view[d]? ≠ some .dead)
    (hexp_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ExposeTargetSlotOk body s entry ∧
      NoCompetingExposedBorrow body s pv entry relOff)
    (hnoadj : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed
          (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)),
        q = targetProv ctx entry.targetLocal)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl) :
    ∃ (entry : BorrowEntry) (relOff : Nat) (m4 m6 m8 : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let locals1 := (opPost s.frame.locals op1).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let view1 := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s1 := advanceStmt s locals1 (exposeMem s.memory pv.allocId)
      let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
      let view2 := view1.set d (.init (.ptr pv 8))
      let s2 := advanceStmt s1 locals2 s1.memory
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      AnnealExposeRoundTripOk body s pv fullAddr ∧
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
          body.localDecls body.layouts = .tau (.running s1) ∧
      Interp.evalTerminator m
          (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
            (.Local (localName i)) (some (bbName nb1))) = .ok m4 ∧
      evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
          body.localDecls body.layouts = .tau (.running s2) ∧
      s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
          (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
            (.Local (localName d)) (some (bbName nb2))) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 (pv.tag :: exposedTags) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm m8 nb2 0 ∧
      AddrTakenTargetsOk body ctx view2 lm := by
  obtain ⟨entry, relOff, m4, hlookup, htspec, hart, htpos, htlt, htAddr_cast, htgt_at,
      hA1, hM1, hipc1, hshape1, hprov1, hsync1, hframe1, hat1⟩ :=
    hprov.expose_step_from_frameOk (targetTy := targetTy1) (span := span1) (nb := nb1)
      hframe hb hat hop1 hs_len hdi hit_i hbor_i hprot hnd_i hview_i hdp hp_ty hp hview_p
      hexp_ok hlen_lt hty1
  let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
  let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
  let tProv : Prov := targetProv ctx entry.targetLocal
  have hnd1_d : ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩)))[d]? ≠ some .dead :=
    set_init_ne_dead i _ (opPost_ne_dead hnd_d)
  have htAddr_nn : 0 ≤ tAddr := by omega
  have hs1_len : ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))).length =
      body.localDecls.length := by
    simp [opPost_length, hs_len]
  have hview1_d : (view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩)))[d]? ≠ some .dead := by
    by_cases hid : i = d
    · subst hid
      by_cases hlt : i < view.length
      · simp [List.getElem?_set_self hlt]
      · rw [List.getElem?_eq_none (by simp; omega)]; simp
    · rwa [List.getElem?_set_ne hid]
  have htgt_ctx : ∀ a pr,
      (ctxWithBorrows body ctx s.memory.borrows).ptrTargets pv.allocId = some (a, pr) →
      tAddr.toNat = a ∧ some tProv = pr := by
    intro a pr hbt0
    have hbt : (ctxWithBorrows body ctx s.memory.borrows).ptrTargets pv.allocId =
        some (tAddr.toNat, some tProv) := by
      simp [ctxWithBorrows, borrowTargets, ProvenancePtr.tag] at hlookup ⊢
      simp [hlookup, htspec, tAddr, tProv, targetProv]
    rw [hbt] at hbt0
    injection hbt0 with hpair
    exact Prod.mk.inj hpair
  have honly : ∀ q ∈ int2ptrCandidates m4.mem.memory.allocations m4.intptrcast.exposed tAddr,
      q = tProv := by
    intro q hq
    have hexp : setContains m4.intptrcast.exposed q = true := int2ptrCandidates_exposed hq
    rw [hipc1, setContains_expose_some_iff] at hexp
    rcases hexp with rfl | hold
    · rfl
    · apply hnoadj entry relOff hlookup htspec
      have hq' := int2ptrCandidates_shape_back hshape1 hq
      obtain ⟨i0, a, ha, hlive, hlo, hhi, _, hpe⟩ := mem_int2ptrCandidates hq'
      rw [hpe] at hold ⊢
      exact int2ptrCandidates_mem_of ha hlive hlo hhi hold
  obtain ⟨hsrc_i, hsigned_i⟩ :=
    isExposeIntSourceTy_of_usize (layouts := body.layouts) hop2 hdi hit_i
  obtain ⟨hA2, m6, m8, harg2, hint, hM2, _, hshape2, hprov2, hframe2, hat2⟩ :=
    hprov1.withExposed_step_from_frameOk (targetTy := targetTy2) (span := span2) (nb := nb2)
      hframe1 hat1 hsync1 hop2 hs1_len hdd hd_ty hbor_d hbor_i hprot hnd1_d hview1_d
      hsrc_i hsigned_i htAddr_nn htlt htgt_ctx honly hbad2
  refine ⟨entry, relOff, m4, m6, m8, hlookup, htspec, hart, hA1, hM1, hA2, ?_,
    harg2, hint, hM2, hshape1.trans hshape2, hprov2, hframe2, hat2⟩
  have hd_decl : d < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdd).1
  have hd2 : d < (opPost ((opPost s.frame.locals op1).set i
      (.init (.scalar ⟨fullAddr, 8⟩))) op2).length := by
    simp [opPost_length, hs_len, hd_decl]
  exact List.getElem?_set_self hd2

/-- Every `FrameOkWithIntrinsics` frame satisfies `FrameOk` because
`translateFnWithIntrinsics_locals` provides `FnLocalsSpec`. -/
theorem FrameOkWithIntrinsics.toFrameOk {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {lm : Map Gen.LocalName Ptr} {m : Mach} {blk stmt : Nat}
    (h : FrameOkWithIntrinsics body f ctx locals lm m blk stmt) :
    FrameOk body f ctx locals lm m blk stmt :=
  ⟨translateFnWithIntrinsics_locals h.hf, h.shape, h.locs, h.declsOk, h.nonScalar⟩

private theorem evalPlace_operandOkB_derefFree {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {p : Place} {pe : Gen.PlaceExpr}
    (hokB : operandOkB layouts decls (.copy p) = true)
    (hpe : translatePlace decls p = some pe) :
    derefFreePlace pe = true := by
  refine translatePlace_derefFree hpe ?_
  rcases p with ⟨j, projs⟩
  rcases projs with _ | ⟨e, _ | _⟩
  · simp
  · cases e with
    | field idx fTy => simp
    | _ => simp [operandOkB] at hokB
  · simp [operandOkB] at hokB

private theorem translateOperand_const_shape {decls : List LocalDecl}
    {c : MirAst.ConstOperand} {op' : Gen.ValueExpr}
    (h : translateOperand decls (.constant c) = some op') :
    ∃ cst ty, op' = .Constant cst ty := by
  dsimp only [translateOperand] at h
  rcases c with ⟨ty, val⟩
  dsimp only at h
  cases hbool : isBoolTy ty <;> simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h
  · cases val with
    | scalar sv =>
      cases sv with
      | int sc =>
        rcases sc with ⟨bits, sz⟩
        cases hit : intTypeOf ty with
        | none => simp [hit] at h
        | some it =>
          simp only [hit] at h
          by_cases hcond : sz = it.size.bytes ∧ bits < 2 ^ (8 * sz)
          · simp [hcond] at h
            exact ⟨_, _, h.2.symm⟩
          · simp [hcond] at h
      | ptr => simp at h
    | _ => simp at h
  · cases val with
    | scalar sv =>
      cases sv with
      | int sc =>
        rcases sc with ⟨bits, sz⟩
        by_cases hcond : sz = 1 ∧ bits < 2
        · simp [hcond] at h
          exact ⟨_, _, h.symm⟩
        · simp [hcond] at h
      | ptr => simp at h
    | _ => simp at h

/-- Evaluating a translated `operandOkB` operand preserves `mem.memory` and
`intptrcast` on `.ok`. -/
private theorem evalValue_operandOkB_mem_eq {layouts : Layout.LayoutTable}
    {decls : List LocalDecl} {op : Operand} {op' : Gen.ValueExpr}
    {m m2 : Mach} {vt : Val × Gen.Type}
    (hokB : operandOkB layouts decls (copyOp op) = true)
    (hop : translateOperand decls op = some op')
    (hev : evalValue m op' = .ok (vt, m2)) :
    m2.mem.memory = m.mem.memory ∧ m2.intptrcast = m.intptrcast := by
  have hopCopy : translateOperand decls (copyOp op) = some op' := by
    rw [translateOperand_copyOp]; exact hop
  have hdf_or_const :
      (∃ pe, op' = .Load pe ∧ derefFreePlace pe = true) ∨
      (∃ cst ty, op' = .Constant cst ty) := by
    rcases op with ⟨p⟩ | ⟨p⟩ | c
    · simp only [copyOp, translateOperand, Option.map_eq_some_iff] at hokB hopCopy
      obtain ⟨pe, hpe, rfl⟩ := hopCopy
      exact .inl ⟨pe, rfl, evalPlace_operandOkB_derefFree hokB hpe⟩
    · simp only [copyOp, translateOperand, Option.map_eq_some_iff] at hokB hopCopy
      obtain ⟨pe, hpe, rfl⟩ := hopCopy
      exact .inl ⟨pe, rfl, evalPlace_operandOkB_derefFree hokB hpe⟩
    · simp only [copyOp] at hopCopy
      exact .inr (translateOperand_const_shape hopCopy)
  rcases hdf_or_const with ⟨pe, rfl, hdf⟩ | ⟨cst, ty, rfl⟩
  · unfold evalValue at hev
    obtain ⟨⟨⟨pl, pty⟩, m1⟩, hep, hev⟩ := interpBind_ok hev
    obtain ⟨⟨v, m2'⟩, hld, hev⟩ := interpBind_ok hev
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨_, rfl⟩ := hev
    have hm1 := evalPlace_derefFree_mach pe hdf m _ _ hep
    subst hm1
    exact ⟨(placeLoad_mem_eq hld).1, (placeLoad_mem_eq hld).2.1⟩
  · unfold evalValue at hev
    obtain ⟨v, _, hev⟩ := interpBind_ok hev
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨_, rfl⟩ := hev
    exact ⟨rfl, rfl⟩

/-- Self-contained `Intrinsic(Assume(op))` simulation step on `FrameOkWithIntrinsics`
in a borrow-enabled context `ctxWithBorrows body ctx s.memory.borrows`:
- when `opBits view (copyOp op) = none` (uninitialized/dead condition), both Anneal
  and MiniRust raise UB;
- when `opBits view (copyOp op) = some 0` (`false` condition), both Anneal and
  MiniRust raise UB (`"`Assume` intrinsic called on condition that is violated"`);
- when `opBits view (copyOp op) = some 1` (`true` condition), Anneal steps to
  `advanceStmt s (opPost s.frame.locals op)` and MiniRust steps to segment
  `(nextSeg, 0)` while preserving `FrameOkWithIntrinsics`, `AddrTakenTargetsOk`,
  `m4.mem.memory = m.mem.memory`, and `m4.intptrcast = m.intptrcast`. -/
theorem FrameOkWithIntrinsics.assume_step {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {curSeg segStmt nextSeg : Nat} {op : Operand} {op' : Gen.ValueExpr}
    {span : String}
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      view lm m curSeg segStmt)
    (hat : AddrTakenTargetsOk body ctx s.frame.locals lm)
    (hstale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hreads : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) [op] = true)
    (hokB : operandOkB body.layouts body.localDecls (copyOp op) = true)
    (hop : translateOperand body.localDecls op = some op') :
    (opBits view (copyOp op) = none →
      evalStmt s ⟨.intrinsic (.assume op), span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub ∧
      ∃ msg, Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) = .error (.ub msg)) ∧
    (opBits view (copyOp op) = some 0 →
      evalStmt s ⟨.intrinsic (.assume op), span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub ∧
      Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) =
        .error (.ub "`Assume` intrinsic called on condition that is violated")) ∧
    (opBits view (copyOp op) = some 1 →
      evalStmt s ⟨.intrinsic (.assume op), span⟩ body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (opPost s.frame.locals op)) ∧
      AddrTakenTargetsOk body ctx (opPost s.frame.locals op) lm ∧
      ∃ m4,
        Interp.evalTerminator m
          (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) = .ok m4 ∧
        m4.mem.memory = m.mem.memory ∧
        m4.intptrcast = m.intptrcast ∧
        FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
          view lm m4 nextSeg 0) := by
  let ctx' := ctxWithBorrows body ctx s.memory.borrows
  have hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals :=
    hstale.slots hframe.locs.slots
  have hnA : s.frame.locals.length = body.localDecls.length :=
    hstale.1.trans hframe.locs.nlocals
  have hsimple : simpleOp op = true := (readsOk_spec hreads op (by simp)).1
  have hbitsEq : opBits s.frame.locals (copyOp op) = opBits view (copyOp op) :=
    opBits_frame _ (by
      rw [opLocals_copyOp]
      exact fun j hj => hstale.agree ((readsOk_spec hreads op (by simp)).2 j hj))
  obtain ⟨hAnone, hA0, hA1⟩ :=
    evalStmt_assume_anneal s body.localDecls body.layouts op span hslotsA hnA hsimple hokB
  have hopCopy : translateOperand body.localDecls (copyOp op) = some op' := by
    rw [translateOperand_copyOp]; exact hop
  obtain ⟨hMok, hMnone⟩ :=
    evalValue_operandT hframe.toFrameOk (.bool : FragTy .Bool u8Ty) (copyOp op)
      (operandOkB_T hokB) op' hopCopy
  refine ⟨fun hnone => ⟨hAnone (hbitsEq.trans hnone), ?_⟩,
    fun h0 => ⟨hA0 (hbitsEq.trans h0), ?_⟩,
    fun h1 => ⟨hA1 (hbitsEq.trans h1), hat.opPost op, ?_⟩⟩
  · obtain ⟨msg, hmsg⟩ := hMnone hnone
    exact ⟨msg, by simp [Interp.evalTerminator, evalPlace_unitPlace, evalArgs, hmsg]⟩
  · obtain ⟨_, m3, hm3, _⟩ := hMok 0 h0
    simp [Interp.evalTerminator, evalPlace_unitPlace, evalArgs, hm3, valOf,
      evalIntrinsic, Interp.unitType, ub]
  · obtain ⟨_, m3, hm3, h3⟩ := hMok 1 h1
    obtain ⟨hmem3, hipc3⟩ := evalValue_operandOkB_mem_eq hokB hop hm3
    have hev : evalIntrinsic m3 .Assume [(valOf .Bool 1, .Bool)] Interp.unitType =
        .ok (Interp.unitValue, m3) := rfl
    let mSt : Mach := withMem m3 m3.mem.memory.allocations ⟨.Store, .None, 1, ⟨0⟩⟩
    have hshSt : Shape mSt ctx'
        ([ctx'.caller] ++ [calleeFrameL f ctx' lm curSeg segStmt])
        m3.mem.memory.allocations := ⟨h3.shape.threads, h3.shape.active, rfl⟩
    have hjmp := jumpToBlock_append hshSt nextSeg
    have hm4 : Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) =
        .ok (rethread mSt ctx' ([ctx'.caller] ++ [calleeFrameL f ctx' lm nextSeg 0])) := by
      simp only [Interp.evalTerminator, evalPlace_unitPlace, ok_bind,
        evalArgs, hm3, pure_ok]
      rw [hev, ok_bind, placeStore_unitValue, ok_bind]
      exact hjmp
    have hwm : mSt.mem.memory = m3.mem.memory := rfl
    refine ⟨rethread mSt ctx' ([ctx'.caller] ++ [calleeFrameL f ctx' lm nextSeg 0]),
      hm4, by dsimp [rethread]; rw [hwm, hmem3], by dsimp [rethread, mSt, withMem]; exact hipc3,
      ⟨hframe.hf, ⟨rfl, h3.shape.active, rfl⟩, h3.locs, hframe.declsOk, hframe.nonScalar⟩⟩

/-- `AddrTakenTargetsOk` transfers from `view` to `actual` along `StaleOk`
because `StaleOk` never turns a non-`.dead` view slot into `.dead`. -/
theorem AddrTakenTargetsOk.of_stale {body : CapturedMir} {ctx : Ctx}
    {actual view : List LocalSlot} {lm : Map Gen.LocalName Ptr} {blk stmt : Nat}
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hstale : StaleOk body actual view blk stmt) :
    AddrTakenTargetsOk body ctx actual lm := by
  intro k hk
  obtain ⟨hview_nd, hlm, hd⟩ := hat k hk
  refine ⟨?_, hlm, hd⟩
  by_cases heq : actual[k]? = view[k]?
  · rwa [heq]
  · rw [(hstale.2 k heq).2.1]; simp

/-- Full cross-feature simulation step for `Intrinsic(Assume(op))` preserving
`FrameOkWithIntrinsics`, `StaleOk`, `BorrowsOk` (active borrow tags and
reborrowing permissions), `AddrTakenTargetsOk`, `m4.mem.memory = m.mem.memory`,
`m4.intptrcast = m.intptrcast`, and `ProvenanceRel` (exposed provenances in
`IntPtrCast`). -/
theorem ProvenanceRel.assume_step_from_frameOk {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {exposedTags : List Nat} {curSeg segStmt nextSeg : Nat}
    {bb : BasicBlockData} {st : Statement} {op : Operand} {op' : Gen.ValueExpr}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      view lm m curSeg segStmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx s.frame.locals lm)
    (hstale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hst : bb.statements[s.frame.stmtIdx]? = some st)
    (hk : st.kind = .intrinsic (.assume op))
    (hreads : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) [op] = true)
    (hokB : operandOkB body.layouts body.localDecls (copyOp op) = true)
    (hop : translateOperand body.localDecls op = some op') :
    (opBits view (copyOp op) = none →
      evalStmt s st body.localDecls body.layouts = MirStepNode.fail .ub ∧
      ∃ msg, Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) = .error (.ub msg)) ∧
    (opBits view (copyOp op) = some 0 →
      evalStmt s st body.localDecls body.layouts = MirStepNode.fail .ub ∧
      Interp.evalTerminator m
        (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) =
        .error (.ub "`Assume` intrinsic called on condition that is violated")) ∧
    (opBits view (copyOp op) = some 1 →
      let s' := advanceStmt s (opPost s.frame.locals op)
      evalStmt s st body.localDecls body.layouts = MirStepNode.step s' ∧
      StaleOk body s'.frame.locals view s'.frame.blockIdx s'.frame.stmtIdx ∧
      BorrowsOk body ctx view s' lm ∧
      AddrTakenTargetsOk body ctx s'.frame.locals lm ∧
      ∃ m4,
        Interp.evalTerminator m
          (.Intrinsic .Assume [op'] unitPlace (some (bbName nextSeg))) = .ok m4 ∧
        m4.mem.memory = m.mem.memory ∧
        m4.intptrcast = m.intptrcast ∧
        ProvenanceRel body ctx s' m4 exposedTags ∧
        FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s'.memory.borrows)
          view lm m4 nextSeg 0) := by
  obtain ⟨stKind, stSpan⟩ := st
  dsimp only at hk
  subst hk
  obtain ⟨hnone, h0, h1⟩ :=
    hframe.assume_step (nextSeg := nextSeg) (span := stSpan) hat hstale hreads hokB hop
  refine ⟨hnone, h0, fun hbits1 => ?_⟩
  obtain ⟨hA1, hat1, m4, hm4, hmem4, hipc4, hframe4⟩ := h1 hbits1
  have hstale1 : StaleOk body (opPost s.frame.locals op) view
      s.frame.blockIdx (s.frame.stmtIdx + 1) :=
    hstale.assume hbb hst rfl
  have hb1 : BorrowsOk body ctx view (advanceStmt s (opPost s.frame.locals op)) lm :=
    hb.advance_keep hbb hst (by simp [ptrStmtStep])
  have hprov1 : ProvenanceRel body ctx (advanceStmt s (opPost s.frame.locals op)) m4 exposedTags :=
    (hprov.of_shape hipc4 (by rw [← hmem4]; exact AllocShapeEq.refl _)).of_advanceStmt _
  exact ⟨hA1, hstale1, hb1, hat1, m4, hm4, hmem4, hipc4, hprov1, hframe4⟩

/-- Complete 3-segment simulation (`Assume` -> `PointerExposeProvenance` ->
`PointerWithExposedProvenance`) composing `ProvenanceRel.assume_step_from_frameOk`
with `ProvenanceRel.expose_then_withExposed_from_frameOk` across three MiniRust
segments (`curSeg -> nb1 -> nb2 -> nb3`), deriving BOTH `AnnealExposeRoundTripOk`
at `fullAddr = canonicalLocalAddr entry.targetLocal relOff` AND destination
liveness (`hnd_d`) internally from `StaleOk` + `AddrTakenTargetsOk` +
`NoCompetingExposedBorrow`, while preserving `FrameOkWithIntrinsics`,
`ProvenanceRel`, and `AddrTakenTargetsOk`. -/
theorem ProvenanceRel.assume_then_expose_then_withExposed_from_frameOk
    {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {exposedTags : List Nat} {curSeg segStmt nb1 nb2 nb3 : Nat}
    {bb : BasicBlockData} {stA : Statement} {opA : Operand} {opA' : Gen.ValueExpr}
    {i p d : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String}
    {pv : ProvenancePtr}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      view lm m curSeg segStmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hstale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstA : bb.statements[s.frame.stmtIdx]? = some stA)
    (hkA : stA.kind = .intrinsic (.assume opA))
    (hreadsA : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) [opA] = true)
    (hokBA : operandOkB body.layouts body.localDecls (copyOp opA) = true)
    (hopA : translateOperand body.localDecls opA = some opA')
    (hbits1 : opBits view (copyOp opA) = some 1)
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = [])
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d)
    (hview_d : view[d]? ≠ some .dead)
    (hexp_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      (entry.targetProjection ≠ [] →
        ptrDeclLayoutsOk body = true ∧
        ∃ dk v,
          body.localDecls[entry.targetLocal]? = some dk ∧
          s.frame.locals[entry.targetLocal]? = some (.init v) ∧
          DeclSlotOk dk (.init v) body.layouts) ∧
      NoCompetingExposedBorrow body s pv entry relOff)
    (hnoadj : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed
          (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)),
        q = targetProv ctx entry.targetLocal)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl) :
    let s0 := advanceStmt s (opPost s.frame.locals opA)
    ∃ (entry : BorrowEntry) (relOff : Nat) (mA m4 m6 m8 : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let locals1 := (opPost s0.frame.locals op1).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let view1 := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s1 := advanceStmt s0 locals1 (exposeMem s0.memory pv.allocId)
      let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
      let view2 := view1.set d (.init (.ptr pv 8))
      let s2 := advanceStmt s1 locals2 s1.memory
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      AnnealExposeRoundTripOk body s0 pv fullAddr ∧
      evalStmt s stA body.localDecls body.layouts = MirStepNode.step s0 ∧
      Interp.evalTerminator m
        (.Intrinsic .Assume [opA'] unitPlace (some (bbName nb1))) = .ok mA ∧
      evalStmt s0 ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
        body.localDecls body.layouts = .tau (.running s1) ∧
      Interp.evalTerminator mA
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some (bbName nb2))) = .ok m4 ∧
      evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
        body.localDecls body.layouts = .tau (.running s2) ∧
      s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
        (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
          (.Local (localName d)) (some (bbName nb3))) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 (pv.tag :: exposedTags) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm m8 nb3 0 ∧
      AddrTakenTargetsOk body ctx view2 lm := by
  have hat_s : AddrTakenTargetsOk body ctx s.frame.locals lm := hat.of_stale hstale
  obtain ⟨_, _, h1⟩ :=
    hprov.assume_step_from_frameOk (nextSeg := nb1)
      hframe hb hat_s hstale hbb hstA hkA hreadsA hokBA hopA
  obtain ⟨hA0, hstale0, hb0, hat0, mA, hmA, hmemA, hipcA, hprov0, hframe0⟩ := h1 hbits1
  let s0 := advanceStmt s (opPost s.frame.locals opA)
  have hs0_len : s0.frame.locals.length = body.localDecls.length :=
    hstale0.1.trans hframe.locs.nlocals
  have hnd0_i : s0.frame.locals[i]? ≠ some .dead := by
    by_cases heq : s0.frame.locals[i]? = view[i]?
    · rwa [heq]
    · rw [(hstale0.2 i heq).2.1]; simp
  have hnd0_d : s0.frame.locals[d]? ≠ some .dead := by
    by_cases heq : s0.frame.locals[d]? = view[d]?
    · rwa [heq]
    · rw [(hstale0.2 d heq).2.1]; simp
  have hp_not_bool : isBoolTy dp.ty = false := by
    cases hb_p : isBoolTy dp.ty with
    | false => rfl
    | true =>
      unfold isBoolTy at hb_p
      rcases dp with ⟨_, ⟨k, _⟩, _⟩
      cases k <;> simp [rawPtrPointeeOf] at hb_p hp_ty
  have hp0 : s0.frame.locals[p]? = some (.init (.ptr pv 8)) :=
    (opPost_bool_eq_of_nonbool_decl hokBA hdp hp_not_bool).trans hp
  have hbor_opA_eq : ∀ b ∈ s.memory.borrows,
      s0.frame.locals[b.targetLocal]? = s.frame.locals[b.targetLocal]? := by
    intro b hb_mem
    obtain ⟨_, bIt, bOff, _, _, hts_b⟩ := hb.entries_ok b hb_mem
    obtain ⟨dk_b, hdk_b, hnb_b⟩ := isBoolTy_false_of_ptrTargetSpec hframe.declsOk hts_b
    exact opPost_bool_eq_of_nonbool_decl hokBA hdk_b hnb_b
  have hexp0_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s0.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ExposeTargetSlotOk body s0 entry ∧
      NoCompetingExposedBorrow body s0 pv entry relOff := by
    intro entry relOff hlk hsp
    have hmem_e : entry ∈ s.memory.borrows := (lookupBorrow_mem_and_tag hlk).1
    obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry hmem_e
    obtain ⟨hsub_e, hnocomp_e⟩ := hexp_ok entry relOff hlk hsp
    refine ⟨⟨(hat0 entry.targetLocal hk_addr).1, fun hne => ?_⟩, ?_⟩
    · obtain ⟨hdlo, dk, v, hdk, hsv, hdslot⟩ := hsub_e hne
      exact ⟨hdlo, dk, v, hdk, (hbor_opA_eq entry hmem_e).trans hsv, hdslot⟩
    · intro b hb_mem hexp_b hne_b
      rcases hnocomp_e b hb_mem hexp_b hne_b with h1 | h2 | ⟨h3a, h3b⟩
      · exact .inl h1
      · exact .inr (.inl h2)
      · exact .inr (.inr ⟨h3a, fun localsPost hloc =>
          h3b localsPost (hloc.trans (hbor_opA_eq b hb_mem))⟩)
  have hnoadj0 : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s0.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ∀ q ∈ int2ptrCandidates mA.mem.memory.allocations mA.intptrcast.exposed
          (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)),
        q = targetProv ctx entry.targetLocal := by
    intro entry relOff hlk hsp q hq
    rw [hmemA, hipcA] at hq
    exact hnoadj entry relOff hlk hsp q hq
  obtain ⟨entry, relOff, m4, m6, m8, hlk, hsp, hart0, hA1, hM1, hA2, hsd, harg2, hint, hM2,
      hshape08, hprov2, hframe2, hat2⟩ :=
    hprov0.expose_then_withExposed_from_frameOk (targetTy1 := targetTy1) (targetTy2 := targetTy2)
      (span1 := span1) (span2 := span2) (nb1 := nb2) (nb2 := nb3)
      hframe0 hb0 hat hop1 hop2 hs0_len hdi hit_i hbor_i hprot hnd0_i hview_i
      hdp hp_ty hp0 hview_p hdd hd_ty hbor_d hnd0_d hview_d hexp0_ok hnoadj0 hlen_lt hty1 hbad2
  have hshape_mA : AllocShapeEq m.mem.memory.allocations mA.mem.memory.allocations := by
    rw [hmemA]; exact AllocShapeEq.refl _
  exact ⟨entry, relOff, mA, m4, m6, m8, hlk, hsp, hart0, hA0, hmA, hA1, hM1, hA2, hsd,
    harg2, hint, hM2, hshape_mA.trans hshape08, hprov2, hframe2, hat2⟩

/-- Every single-body `inFragmentWithIntrinsics` program (intra-frame pointers,
references, reborrows, `Transmute`, `Assume`, `PointerExposeProvenance`, and
`PointerWithExposedProvenance`) embeds unconditionally into the unified
multi-function fragment `progInFragmentWithIntrinsics body []`. -/
theorem inFragmentWithIntrinsics_implies_progInFragmentWithIntrinsics
    {body : CapturedMir} (h : inFragmentWithIntrinsics body = true) :
    progInFragmentWithIntrinsics body [] = true := by
  simp only [inFragmentWithIntrinsics, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    hflow⟩, hptr⟩, htr⟩ := h
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp htr
  have hterm : ∀ bb ∈ body.basicBlocks,
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true :=
    fun bb hbb => (h9 bb hbb).2
  have hnoCalls_view : ∀ bb ∈ (provCastAliasView body).basicBlocks,
      isNonDivergingCall bb.terminator = false := by
    intro bb hbb
    unfold provCastAliasView at hbb
    split at hbb
    · simp only [List.mem_map] at hbb
      obtain ⟨bb0, hbb0, rfl⟩ := hbb
      exact (terminatorOk_not_call (hterm bb0 hbb0)).1
    · exact (terminatorOk_not_call (hterm bb hbb)).1
  have hptrProg : ptrAliasingProgOk (provCastAliasView body) = true := by
    rw [ptrAliasingProgOk_eq_of_no_calls _ hnoCalls_view]
    exact hptr
  have hargLe : body.argCount ≤ body.localDecls.length := by
    simp only [decide_eq_true_eq] at h2; omega
  have hlv := livenessOk_eq_true (body := body) hargLe
  have hti := tupleInitOk_eq_true body
  have hfnSome := translateFnInProgWithIntrinsics_isSome_of_translateFnWithIntrinsics
    (fnNameMap body []) hterm hf
  obtain ⟨fProg, hfProg⟩ := Option.isSome_iff_exists.mp hfnSome
  have hbbs' : ∀ blk ∈ List.range body.basicBlocks.length,
      (match body.basicBlocks[blk]? with
       | some bb =>
         !bb.isCleanup &&
         bb.statements.all (statementOkWithIntrinsics body.localDecls · body.layouts) &&
         terminatorInProgOk [] body blk bb.terminator
       | none => true) = true := by
    intro blk _
    cases hget : body.basicBlocks[blk]? with
    | none => rfl
    | some bb =>
      obtain ⟨⟨hc, hss⟩, htm⟩ := h9 bb (List.mem_of_getElem? hget)
      simp only [Bool.and_eq_true, List.all_eq_true]
      exact ⟨⟨hc, hss⟩, by simp [terminatorInProgOk, htm]⟩
  have hbodyOk : bodyInProgFragmentWithIntrinsics (fnNameMap body []) [] body = true := by
    simp only [bodyInProgFragmentWithIntrinsics, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, hbbs'⟩,
      h10⟩, h11⟩, h12⟩, hlv⟩, hti⟩, hflow⟩, hptrProg⟩, hfnSome⟩
  have hstack : maxStackLocals body [] = some body.localDecls.length := by
    simp [maxStackLocals, maxStackLocalsAux, callCalleesOf_eq_nil_of_terminatorOk hterm]
  have hprogSome : (translateProgWithIntrinsics body []).isSome = true := by
    simp [translateProgWithIntrinsics, translateProgFnsWithIntrinsics, hfProg]
  have hnodup : ((body :: ([] : List CapturedMir)).map (·.defPath)).Nodup := by simp
  simp only [progInFragmentWithIntrinsics, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, hstack, hprogSome, Bool.and_true]
  refine ⟨⟨hnodup, ?_⟩, ?_⟩
  · intro b hb
    rcases List.mem_singleton.mp hb with rfl
    exact hbodyOk
  · simpa [decide_eq_true_eq] using h3

/-- Every single-body `inFragment` program embeds into
`progInFragmentWithIntrinsics body []`. -/
theorem inFragment_implies_progInFragmentWithIntrinsics
    {body : CapturedMir} (h : inFragment body = true) :
    progInFragmentWithIntrinsics body [] = true :=
  inFragmentWithIntrinsics_implies_progInFragmentWithIntrinsics
    (inFragment_implies_inFragmentWithIntrinsics h)

theorem exposeSourceCompatible_iff {dstMutbl srcMutbl : MirAst.Mutability}
    {dstIt srcIt : Gen.IntType} :
    exposeSourceCompatible dstMutbl dstIt (some (srcMutbl, srcIt)) = true ↔
      srcIt = dstIt ∧ (srcMutbl = .mut ∨ dstMutbl = .not) := by
  simp [exposeSourceCompatible, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

/-- Preservation of `BorrowsOk.ptr_slots` and reconstructed-pointer usability
across a 2-step `PointerExposeProvenance` (`_i = _p as usize`) +
`PointerWithExposedProvenance` (`_d = _i as *const/*mut T`) round-trip under
`exposeSourceCompatible`: every pointer slot in `view2` (including the newly
reconstructed pointer local `d`) resolves in `s.memory.borrows` to an
address-taken target local with valid `ptrTargetSpec` and mutability-compatible
permission, and when `_p` is non-`.disabled` in `ptrEnvBefore`, the reconstructed
pointer `_d` is non-`.disabled` (and `.active ∨ .reserved` when `dstMutbl = .mut`). -/
theorem BorrowsOk.ptr_slots_after_expose_withExposed {body : CapturedMir}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {i p d addrBits : Nat} { dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {pv : ProvenancePtr}
    (hb : BorrowsOk body ctx view s lm)
    (hlen : view.length = body.localDecls.length)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hcompat : exposeSourceCompatible dstMutbl dstIt (some (srcMutbl, srcIt)) = true) :
    let view1 := view.set i (.init (.scalar ⟨addrBits, 8⟩))
    let view2 := view1.set d (.init (.ptr pv 8))
    view2[d]? = some (.init (.ptr pv 8)) ∧
    srcIt = dstIt ∧
    (∀ (q : Nat) (dq : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
        (ptrVal : ProvenancePtr),
      body.localDecls[q]? = some dq →
      ptrPointeeOf dq.ty = some (mutbl, pointeeIt) →
      view2[q]? = some (.init (.ptr ptrVal 8)) →
      ∃ (entry : BorrowEntry) (relOff : Nat),
        ptrVal.offsetBytes = 0 ∧
        lookupBorrow s.memory.borrows ptrVal.tag = some entry ∧
        entry.targetLocal ∈ bodyAddrTakenLocals body ∧
        ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
          some (pointeeIt, relOff)) ∧
    ((ptrEnvBefore body s.frame.blockIdx s.frame.stmtIdx).getD p .disabled ≠ .disabled →
      ∀ (entry : BorrowEntry),
        lookupBorrow s.memory.borrows pv.tag = some entry →
        entry.perm ≠ .disabled ∧
          (dstMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved)) := by
  obtain ⟨hit_eq, hmut_compat⟩ := exposeSourceCompatible_iff.mp hcompat
  have hd_decl : d < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdd).1
  have hd_v1 : d < (view.set i (.init (.scalar ⟨addrBits, 8⟩))).length := by
    simp [hlen, hd_decl]
  have hview2_d : ((view.set i (.init (.scalar ⟨addrBits, 8⟩))).set d (.init (.ptr pv 8)))[d]? =
      some (.init (.ptr pv 8)) :=
    List.getElem?_set_self hd_v1
  refine ⟨hview2_d, hit_eq, ?_, ?_⟩
  · intro q dq mutbl pointeeIt ptrVal hdq hpt hv
    by_cases hdq_eq : d = q
    · subst hdq_eq
      rw [hview2_d] at hv
      injection hv with hinit
      injection hinit with hval
      injection hval with hpv_eq _
      subst hpv_eq
      rw [hdd] at hdq
      injection hdq with hdd_eq
      subst hdd_eq
      have hpt_d : ptrPointeeOf dd.ty = some (dstMutbl, dstIt) :=
        (ptrPointeeOf_of_rawPtrPointeeOf hd_ty).1
      rw [hpt_d] at hpt
      injection hpt with hpair
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      obtain ⟨entry, relOff, hoff0, hlk, hspec⟩ :=
        hb.ptr_slots p dp srcMutbl srcIt pv hdp hp_ty hview_p
      obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry (lookupBorrow_mem_and_tag hlk).1
      exact ⟨entry, relOff, hoff0, hlk, hk_addr, hit_eq ▸ hspec⟩
    · rw [List.getElem?_set_ne hdq_eq] at hv
      by_cases hiq : i = q
      · subst hiq
        by_cases hlt : i < view.length
        · rw [List.getElem?_set_self hlt] at hv
          cases hv
        · rw [List.getElem?_eq_none (by simp; omega)] at hv
          cases hv
      · rw [List.getElem?_set_ne hiq] at hv
        obtain ⟨entry, relOff, hoff0, hlk, hspec⟩ :=
          hb.ptr_slots q dq mutbl pointeeIt ptrVal hdq hpt hv
        obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry (lookupBorrow_mem_and_tag hlk).1
        exact ⟨entry, relOff, hoff0, hlk, hk_addr, hspec⟩
  · intro hndis entry hlk
    obtain ⟨hperm_nd, hmut_act⟩ := hb.usable_of_not_disabled hndis hdp hp_ty hview_p hlk
    refine ⟨hperm_nd, fun hdm => ?_⟩
    rcases hmut_compat with hsm | hdn
    · exact hmut_act hsm
    · rw [hdn] at hdm; cases hdm

/-- Strengthened 3-segment simulation (`Assume` -> `PointerExposeProvenance` ->
`PointerWithExposedProvenance`) deriving `hbor_i`, `hbor_d`, `hnd_d`, and
`AnnealExposeRoundTripOk` (`fullAddr = canonicalLocalAddr entry.targetLocal relOff`)
from `BorrowsOk`, `StaleOk`, `NoCompetingExposedBorrow`, and
`i, d ∉ bodyAddrTakenLocals body`, and establishing post-state `view2[d]?`,
`s2.memory = exposeMem s.memory pv.allocId`, `BorrowsOk.ptr_slots` across all
pointer locals in `view2` (including the reconstructed pointer local `d`), and
post-state dereference usability of `d` in `s2.memory.borrows`. -/
theorem ProvenanceRel.assume_then_expose_then_withExposed_usable_from_frameOk
    {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {exposedTags : List Nat} {curSeg segStmt nb1 nb2 nb3 : Nat}
    {bb : BasicBlockData} {stA : Statement} {opA : Operand} {opA' : Gen.ValueExpr}
    {i p d : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String}
    {pv : ProvenancePtr}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      view lm m curSeg segStmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hstale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstA : bb.statements[s.frame.stmtIdx]? = some stA)
    (hkA : stA.kind = .intrinsic (.assume opA))
    (hreadsA : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) [opA] = true)
    (hokBA : operandOkB body.layouts body.localDecls (copyOp opA) = true)
    (hopA : translateOperand body.localDecls opA = some opA')
    (hbits1 : opBits view (copyOp opA) = some 1)
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hprot : s.memory.activeProtectors = [])
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hd_addr : d ∉ bodyAddrTakenLocals body)
    (hcompat : exposeSourceCompatible dstMutbl dstIt (some (srcMutbl, srcIt)) = true)
    (hview_d : view[d]? ≠ some .dead)
    (hexp_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      (entry.targetProjection ≠ [] →
        ptrDeclLayoutsOk body = true ∧
        ∃ dk v,
          body.localDecls[entry.targetLocal]? = some dk ∧
          s.frame.locals[entry.targetLocal]? = some (.init v) ∧
          DeclSlotOk dk (.init v) body.layouts) ∧
      NoCompetingExposedBorrow body s pv entry relOff)
    (hnoadj : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed
          (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)),
        q = targetProv ctx entry.targetLocal)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl) :
    let s0 := advanceStmt s (opPost s.frame.locals opA)
    ∃ (entry : BorrowEntry) (relOff : Nat) (mA m4 m6 m8 : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let locals1 := (opPost s0.frame.locals op1).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let view1 := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s1 := advanceStmt s0 locals1 (exposeMem s0.memory pv.allocId)
      let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
      let view2 := view1.set d (.init (.ptr pv 8))
      let s2 := advanceStmt s1 locals2 s1.memory
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (dstIt, relOff) ∧
      AnnealExposeRoundTripOk body s0 pv fullAddr ∧
      srcIt = dstIt ∧
      pv.offsetBytes = 0 ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      evalStmt s stA body.localDecls body.layouts = MirStepNode.step s0 ∧
      Interp.evalTerminator m
        (.Intrinsic .Assume [opA'] unitPlace (some (bbName nb1))) = .ok mA ∧
      evalStmt s0 ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
        body.localDecls body.layouts = .tau (.running s1) ∧
      Interp.evalTerminator mA
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some (bbName nb2))) = .ok m4 ∧
      evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
        body.localDecls body.layouts = .tau (.running s2) ∧
      s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
      view2[d]? = some (.init (.ptr pv 8)) ∧
      s2.memory = exposeMem s.memory pv.allocId ∧
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
        (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
          (.Local (localName d)) (some (bbName nb3))) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 (pv.tag :: exposedTags) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm m8 nb3 0 ∧
      AddrTakenTargetsOk body ctx view2 lm ∧
      (∀ (q : Nat) (dq : LocalDecl) (mutbl : MirAst.Mutability) (pointeeIt : Gen.IntType)
          (ptrVal : ProvenancePtr),
        body.localDecls[q]? = some dq →
        ptrPointeeOf dq.ty = some (mutbl, pointeeIt) →
        view2[q]? = some (.init (.ptr ptrVal 8)) →
        ∃ (entry' : BorrowEntry) (relOff' : Nat),
          ptrVal.offsetBytes = 0 ∧
          lookupBorrow s2.memory.borrows ptrVal.tag = some entry' ∧
          entry'.targetLocal ∈ bodyAddrTakenLocals body ∧
          ptrTargetSpec body.layouts body.localDecls ⟨entry'.targetLocal, entry'.targetProjection⟩ =
            some (pointeeIt, relOff')) ∧
      ((ptrEnvBefore body s.frame.blockIdx (s.frame.stmtIdx + 1)).getD p .disabled ≠ .disabled →
        entry.perm ≠ .disabled ∧
          (dstMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved)) := by
  have hp_pty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt) :=
    (ptrPointeeOf_of_rawPtrPointeeOf hp_ty).1
  have hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i :=
    hb.target_ne_of_not_addrTaken hi_addr
  have hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d :=
    hb.target_ne_of_not_addrTaken hd_addr
  obtain ⟨entry, relOff, mA, m4, m6, m8, hlk, hsp, hart0, hA0, hmA, hA1, hM1, hA2, hsd,
      harg2, hint, hM2, hshape, hprov2, hframe2, hat2⟩ :=
    hprov.assume_then_expose_then_withExposed_from_frameOk
      (nb1 := nb1) (nb2 := nb2) (nb3 := nb3) (targetTy1 := targetTy1) (targetTy2 := targetTy2)
      (span1 := span1) (span2 := span2)
      hframe hb hat hstale hbb hstA hkA hreadsA hokBA hopA hbits1
      hop1 hop2 hdi hit_i hbor_i hprot hview_i hdp hp_ty hp hview_p
      hdd hd_ty hbor_d hview_d hexp_ok hnoadj hlen_lt hty1 hbad2
  let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
  have hb0 : BorrowsOk body ctx view (advanceStmt s (opPost s.frame.locals opA)) lm :=
    hb.advance_keep hbb hstA (by simp [ptrStmtStep, hkA])
  obtain ⟨hview2_d, hit_eq, hslots2, husable2⟩ :=
    hb0.ptr_slots_after_expose_withExposed (i := i) (addrBits := tAddr.toNat)
      hframe.locs.nlocals hdp hp_pty hview_p hdd hd_ty hcompat
  obtain ⟨entry0, _, hoff0, hlk0, _⟩ :=
    hb.ptr_slots p dp srcMutbl srcIt pv hdp hp_pty hview_p
  rw [hlk] at hlk0
  injection hlk0 with hent_eq
  subst hent_eq
  obtain ⟨_, _, _, _, hk_addr, _⟩ := hb.entries_ok entry (lookupBorrow_mem_and_tag hlk).1
  exact ⟨entry, relOff, mA, m4, m6, m8, hlk, hit_eq ▸ hsp, hart0, hit_eq, hoff0, hk_addr,
    hA0, hmA, hA1, hM1, hA2, hsd, hview2_d, rfl, harg2, hint, hM2, hshape, hprov2,
    hframe2, hat2, hslots2, fun hndis => husable2 hndis entry hlk⟩

/-- Single-body `inFragmentWithIntrinsics` + `singleExposeSiteOk` embeds into
both `progInFragmentWithIntrinsics body []` and `progSingleExposeSiteOk body []`
(MR-4.3 Pass A4). -/
theorem inFragmentWithIntrinsics_and_singleExpose_implies_prog
    {body : CapturedMir}
    (hfrag : inFragmentWithIntrinsics body = true)
    (hse : singleExposeSiteOk body = true) :
    progInFragmentWithIntrinsics body [] = true ∧
      progSingleExposeSiteOk body [] = true :=
  ⟨inFragmentWithIntrinsics_implies_progInFragmentWithIntrinsics hfrag,
   by rwa [progSingleExposeSiteOk_nil]⟩

private theorem ptrEnvOk_setPtrLocal_disabled {body : CapturedMir} {view : List LocalSlot}
    {borrows : List BorrowEntry} {env : List PtrLocalState}
    (hok : PtrEnvOk body view borrows env) (d : Nat) (slot' : LocalSlot) :
    PtrEnvOk body (view.set d slot') borrows
      (setPtrLocal body.localDecls.length env d .disabled) := by
  intro q hq
  rw [setPtrLocal, getD_map_range _ _ _ hq]
  by_cases hqd : q == d
  · simp only [hqd, ↓reduceIte]; trivial
  · simp only [hqd, Bool.false_eq_true, ↓reduceIte]
    have hneq : d ≠ q := by
      intro h; subst h; simp at hqd
    have hq_ok := hok q hq
    cases hst : env.getD q .disabled with
    | empty =>
      rw [hst] at hq_ok
      dsimp only [removePeerFromState, PtrLocalOk]
      intro dq pv hdq hpty hv
      rw [List.getElem?_set_ne hneq] at hv
      exact hq_ok dq pv hdq hpty hv
    | disabled => trivial
    | live target ps =>
      rw [hst] at hq_ok
      dsimp only [removePeerFromState, PtrLocalOk]
      intro dq pv hdq hpty hv
      rw [List.getElem?_set_ne hneq] at hv
      obtain ⟨hent, hpeers⟩ := hq_ok dq pv hdq hpty hv
      refine ⟨hent, fun r hr dr pv_r hdr hptr hvr => ?_⟩
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hr
      have hdr_ne : d ≠ r := fun h => hr.2 h.symm
      rw [List.getElem?_set_ne hdr_ne] at hvr
      exact hpeers r hr.1 dr pv_r hdr hptr hvr

/-- Full `BorrowsOk` inductive closure across a 2-statement
`PointerExposeProvenance` (`_i = _p as usize`) + `PointerWithExposedProvenance`
(`_d = _i as *const/*mut T`) sequence in `bb.statements` under
`exposeSourceCompatible` (MR-4.3 Pass A4). Unlike
`BorrowsOk.ptr_slots_after_expose_withExposed` (which projected only the raw
`ptr_slots` universal quantifier), this theorem establishes the complete bundled
`BorrowsOk body ctx view2 s2 lm` structure — including `tags_lt`, `entries_ok`,
`target_ptrs`, and `alias_ok` across `ptrStmtStep` for both provenance-cast
statements — so downstream lemmas (`evalPtrLoad_withIntrinsics`, subsequent
`assume_step_from_frameOk` / `expose_then_withExposed_from_frameOk`) compose
inductively without breaking `BorrowsOk`. -/
theorem BorrowsOk.after_expose_withExposed {body : CapturedMir}
    {ctx : Ctx} {view : List LocalSlot} {s0 : MachineState} {lm : Map Gen.LocalName Ptr}
    {bb : BasicBlockData} {i p d addrBits : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String} {locals1 locals2 : List LocalSlot}
    {pv : ProvenancePtr}
    (hb0 : BorrowsOk body ctx view s0 lm)
    (hlen : view.length = body.localDecls.length)
    (hbb : body.basicBlocks[s0.frame.blockIdx]? = some bb)
    (hst1 : bb.statements[s0.frame.stmtIdx]? =
      some ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩)
    (hst2 : bb.statements[s0.frame.stmtIdx + 1]? =
      some ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hd_addr : d ∉ bodyAddrTakenLocals body)
    (hcompat : exposeSourceCompatible dstMutbl dstIt (some (srcMutbl, srcIt)) = true) :
    let view1 := view.set i (.init (.scalar ⟨addrBits, 8⟩))
    let s1 := advanceStmt s0 locals1 (exposeMem s0.memory pv.allocId)
    let view2 := view1.set d (.init (.ptr pv 8))
    let s2 := advanceStmt s1 locals2 s1.memory
    BorrowsOk body ctx view2 s2 lm ∧
    ((ptrEnvBefore body s0.frame.blockIdx s0.frame.stmtIdx).getD p .disabled ≠ .disabled →
      ∀ (entry : BorrowEntry),
        lookupBorrow s0.memory.borrows pv.tag = some entry →
        entry.perm ≠ .disabled ∧
          (dstMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved)) := by
  have hi_not_ptr : isDeclPtrLocal body.localDecls i = false := by
    unfold isDeclPtrLocal
    rw [hdi]
    exact isPtrTy_false_of_scalarTypeOf (scalarTypeOf_int hit_i)
  have hstep1 : ptrStmtStep body.localDecls
      (ptrEnvBefore body s0.frame.blockIdx s0.frame.stmtIdx)
      ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩ =
      (List.range body.localDecls.length).map
        (fun q => (ptrEnvBefore body s0.frame.blockIdx s0.frame.stmtIdx).getD q .disabled) := by
    simp [ptrStmtStep, hi_not_ptr, ptrDerefReadSrc, copyRv]
  have hb1 : BorrowsOk body ctx (view.set i (.init (.scalar ⟨addrBits, 8⟩)))
      (advanceStmt s0 locals1 s0.memory) lm :=
    hb0.advance_set_nonptr (locals' := locals1) hbb hst1 hstep1 i
      (.init (.scalar ⟨addrBits, 8⟩))
      (fun hk => False.elim (hi_addr hk))
      (fun _ _ _ _ h => by cases h)
  obtain ⟨_, _, hslots2, husable2⟩ :=
    hb0.ptr_slots_after_expose_withExposed (i := i) (addrBits := addrBits)
      hlen hdp hp_ty hview_p hdd hd_ty hcompat
  have hd_is_ptr : isDeclPtrLocal body.localDecls d = true := by
    unfold isDeclPtrLocal
    rw [hdd]
    simp [isPtrTy, (ptrPointeeOf_of_rawPtrPointeeOf hd_ty).1]
  have hstep2 : ptrStmtStep body.localDecls
      (ptrEnvBefore body s0.frame.blockIdx (s0.frame.stmtIdx + 1))
      ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩ =
      setPtrLocal body.localDecls.length
        (ptrEnvBefore body s0.frame.blockIdx (s0.frame.stmtIdx + 1)) d .disabled := by
    simp [ptrStmtStep, hd_is_ptr, directBorrowOf, reborrowParentOf, ptrCopySrcOf, copyRv]
  refine ⟨{
    nextTag_pos := hb1.nextTag_pos
    tags_pos := hb1.tags_pos
    tags_lt := hb1.tags_lt
    tags_nodup := hb1.tags_nodup
    entries_ok := hb1.entries_ok
    entries_place := hb1.entries_place
    target_init := fun hfrag k hk => by
      have hdk : d ≠ k := fun h => hd_addr (h ▸ hk)
      rw [List.getElem?_set_ne hdk]
      exact hb1.target_init hfrag k hk
    target_ptrs := fun hfrag k hk => by
      obtain ⟨hnd, hlm, hd_ok⟩ := hb1.target_ptrs hfrag k hk
      have hdk : d ≠ k := fun h => hd_addr (h ▸ hk)
      refine ⟨?_, hlm, hd_ok⟩
      rw [List.getElem?_set_ne hdk]
      exact hnd
    alias_ok := by
      have hal1 := hb1.alias_ok
      dsimp only [advanceStmt, exposeMem] at hal1 ⊢
      rw [Nat.add_eq, ptrEnvBefore_succ hbb hst2, hstep2]
      exact ptrEnvOk_setPtrLocal_disabled hal1 d (.init (.ptr pv 8))
    ptr_slots := fun q dq mutbl pointeeIt ptrVal hdq hpt hv => by
      obtain ⟨entry, relOff, hoff0, hlk, _, hspec⟩ :=
        hslots2 q dq mutbl pointeeIt ptrVal hdq hpt hv
      exact ⟨entry, relOff, hoff0, hlk, hspec⟩
  }, husable2⟩

/-- Closed-invariant 3-segment simulation (`Assume` -> `PointerExposeProvenance`
-> `PointerWithExposedProvenance`) deriving `AnnealExposeRoundTripOk` at
`fullAddr = canonicalLocalAddr entry.targetLocal relOff` structurally (no `hart`
or `hnd_d` hypothesis), plus post-state MiniRust pointer load of the
reconstructed raw pointer `_d` (MR-4.3 Pass A4): restores the complete closed
inductive invariant tuple `(ProvenanceRel, FrameOkWithIntrinsics, BorrowsOk,
AddrTakenTargetsOk)` at `(s2, m8, view2, nb3, 0)` and evaluates
`evalValue m8 (.Load (.Local (localName d)))` via `evalPtrLoad_withIntrinsics`
to the exact target pointer `offsetPtr (localPtr ctx entry.targetLocal) relOff`
while preserving `FrameOkWithIntrinsics` on `mLoad` and establishing post-state
dereference usability of `_d` in `s2.memory.borrows`. -/
theorem ProvenanceRel.assume_then_expose_then_withExposed_closed_from_frameOk
    {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {exposedTags : List Nat} {curSeg segStmt nb1 nb2 nb3 : Nat}
    {bb : BasicBlockData} {stA : Statement} {opA : Operand} {opA' : Gen.ValueExpr}
    {i p d : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String}
    {pv : ProvenancePtr}
    (hprov : ProvenanceRel body ctx s m exposedTags)
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      view lm m curSeg segStmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hstale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstA : bb.statements[s.frame.stmtIdx]? = some stA)
    (hkA : stA.kind = .intrinsic (.assume opA))
    (hst1 : bb.statements[s.frame.stmtIdx + 1]? =
      some ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩)
    (hst2 : bb.statements[s.frame.stmtIdx + 2]? =
      some ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩)
    (hreadsA : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) [opA] = true)
    (hokBA : operandOkB body.layouts body.localDecls (copyOp opA) = true)
    (hopA : translateOperand body.localDecls opA = some opA')
    (hbits1 : opBits view (copyOp opA) = some 1)
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hprot : s.memory.activeProtectors = [])
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hd_addr : d ∉ bodyAddrTakenLocals body)
    (hcompat : exposeSourceCompatible dstMutbl dstIt (some (srcMutbl, srcIt)) = true)
    (hview_d : view[d]? ≠ some .dead)
    (hexp_ok : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      (entry.targetProjection ≠ [] →
        ptrDeclLayoutsOk body = true ∧
        ∃ dk v,
          body.localDecls[entry.targetLocal]? = some dk ∧
          s.frame.locals[entry.targetLocal]? = some (.init v) ∧
          DeclSlotOk dk (.init v) body.layouts) ∧
      NoCompetingExposedBorrow body s pv entry relOff)
    (hnoadj : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed
          (ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)),
        q = targetProv ctx entry.targetLocal)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl) :
    let s0 := advanceStmt s (opPost s.frame.locals opA)
    ∃ (entry : BorrowEntry) (relOff : Nat) (mA m4 m6 m8 mLoad : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let locals1 := (opPost s0.frame.locals op1).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let view1 := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s1 := advanceStmt s0 locals1 (exposeMem s0.memory pv.allocId)
      let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
      let view2 := view1.set d (.init (.ptr pv 8))
      let s2 := advanceStmt s1 locals2 s1.memory
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (dstIt, relOff) ∧
      AnnealExposeRoundTripOk body s0 pv fullAddr ∧
      srcIt = dstIt ∧
      pv.offsetBytes = 0 ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      evalStmt s stA body.localDecls body.layouts = MirStepNode.step s0 ∧
      Interp.evalTerminator m
        (.Intrinsic .Assume [opA'] unitPlace (some (bbName nb1))) = .ok mA ∧
      evalStmt s0 ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
        body.localDecls body.layouts = .tau (.running s1) ∧
      Interp.evalTerminator mA
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some (bbName nb2))) = .ok m4 ∧
      evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
        body.localDecls body.layouts = .tau (.running s2) ∧
      s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
      view2[d]? = some (.init (.ptr pv 8)) ∧
      s2.memory = exposeMem s.memory pv.allocId ∧
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
        (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
          (.Local (localName d)) (some (bbName nb3))) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 (pv.tag :: exposedTags) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm m8 nb3 0 ∧
      BorrowsOk body ctx view2 s2 lm ∧
      AddrTakenTargetsOk body ctx view2 lm ∧
      evalValue m8 (.Load (.Local (localName d))) =
        .ok ((.Ptr { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff, metadata := none },
              declPtrTy dd.ty), mLoad) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm mLoad nb3 0 ∧
      ((ptrEnvBefore body s.frame.blockIdx (s.frame.stmtIdx + 1)).getD p .disabled ≠ .disabled →
        entry.perm ≠ .disabled ∧
          (dstMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved)) := by
  have hp_pty : ptrPointeeOf dp.ty = some (srcMutbl, srcIt) :=
    (ptrPointeeOf_of_rawPtrPointeeOf hp_ty).1
  obtain ⟨entry, relOff, mA, m4, m6, m8, hlk, hsp, hart0, hit_eq, hoff0, hk_addr,
      hA0, hmA, hA1, hM1, hA2, hsd, hview2_d, hmem_eq, harg2, hint, hM2, hshape, hprov2,
      hframe2, hat2, _, husable⟩ :=
    hprov.assume_then_expose_then_withExposed_usable_from_frameOk
      (nb1 := nb1) (nb2 := nb2) (nb3 := nb3) (targetTy1 := targetTy1) (targetTy2 := targetTy2)
      (span1 := span1) (span2 := span2)
      hframe hb hat hstale hbb hstA hkA hreadsA hokBA hopA hbits1
      hop1 hop2 hdi hit_i hi_addr hprot hview_i hdp hp_ty hp hview_p
      hdd hd_ty hd_addr hcompat hview_d hexp_ok hnoadj hlen_lt hty1 hbad2
  let s0 := advanceStmt s (opPost s.frame.locals opA)
  let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
  let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
  let locals1 := (opPost s0.frame.locals op1).set i
    (.init (.scalar ⟨fullAddr, 8⟩))
  let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
  have hb0 : BorrowsOk body ctx view s0 lm :=
    hb.advance_keep hbb hstA (by simp [ptrStmtStep, hkA])
  obtain ⟨hb2, _⟩ :=
    hb0.after_expose_withExposed (addrBits := tAddr.toNat)
      (locals1 := locals1) (locals2 := locals2)
      hframe.locs.nlocals hbb hst1 hst2 hdi hit_i hi_addr
      hdp hp_pty hview_p hdd hd_ty hd_addr hcompat
  have hd_pty : ptrPointeeOf dd.ty = some (dstMutbl, dstIt) :=
    (ptrPointeeOf_of_rawPtrPointeeOf hd_ty).1
  rcases evalPtrLoad_withIntrinsics hframe2 hb2 hat2 d dd dstMutbl dstIt hdd hd_pty with
    ⟨ptrVal, entry', relOff', mLoad, hv_d, _, hlk', _, hsp', _, hevLoad, hframeLoad⟩ |
    ⟨hbad, _⟩
  · rw [hview2_d] at hv_d
    injection hv_d with hinit
    injection hinit with hval
    injection hval with hpv_eq _
    subst hpv_eq
    rw [hmem_eq] at hlk'
    dsimp only [exposeMem] at hlk'
    rw [hlk] at hlk'
    injection hlk' with hent_eq
    subst hent_eq
    rw [hsp] at hsp'
    injection hsp' with hpair
    obtain ⟨_, rfl⟩ := Prod.mk.inj hpair
    exact ⟨entry, relOff, mA, m4, m6, m8, mLoad, hlk, hsp, hart0, hit_eq, hoff0, hk_addr,
      hA0, hmA, hA1, hM1, hA2, hsd, hview2_d, hmem_eq, harg2, hint, hM2, hshape, hprov2,
      hframe2, hb2, hat2, hevLoad, hframeLoad, husable⟩
  · rcases hbad with hbad | hbad <;> (rw [hview2_d] at hbad; cases hbad)

/-- Completely non-interference-free specialization of
`ProvenanceRel.expose_then_withExposed_from_frameOk` at the initial unexposed
state (`exposedTags = []`, covering every `singleExposeSiteOk` body): both
`NoCompetingExposedBorrow` (on the Anneal side) and `hnoadj` (on the MiniRust
side) vanish identically from `ProvenanceRel body ctx s m []`. -/
theorem ProvenanceRel.expose_then_withExposed_unexposed_from_frameOk
    {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {blk stmt : Nat}
    {i p d : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String} {nb1 nb2 : Nat}
    {pv : ProvenancePtr}
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows) view lm m blk stmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hprov : ProvenanceRel body ctx s m [])
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hs_len : s.frame.locals.length = body.localDecls.length)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hbor_i : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ i)
    (hprot : s.memory.activeProtectors = [])
    (hnd_i : s.frame.locals[i]? ≠ some .dead)
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hbor_d : ∀ e ∈ s.memory.borrows, e.targetLocal ≠ d)
    (hnd_d : s.frame.locals[d]? ≠ some .dead)
    (hview_d : view[d]? ≠ some .dead)
    (htgt_slot : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      ExposeTargetSlotOk body s entry)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl) :
    ∃ (entry : BorrowEntry) (relOff : Nat) (m4 m6 m8 : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let locals1 := (opPost s.frame.locals op1).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let view1 := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s1 := advanceStmt s locals1 (exposeMem s.memory pv.allocId)
      let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
      let view2 := view1.set d (.init (.ptr pv 8))
      let s2 := advanceStmt s1 locals2 s1.memory
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) ∧
      AnnealExposeRoundTripOk body s pv fullAddr ∧
      evalStmt s ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
          body.localDecls body.layouts = .tau (.running s1) ∧
      Interp.evalTerminator m
          (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
            (.Local (localName i)) (some (bbName nb1))) = .ok m4 ∧
      evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
          body.localDecls body.layouts = .tau (.running s2) ∧
      s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
          (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
            (.Local (localName d)) (some (bbName nb2))) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 [pv.tag] ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm m8 nb2 0 ∧
      AddrTakenTargetsOk body ctx view2 lm := by
  refine hprov.expose_then_withExposed_from_frameOk hframe hb hat hop1 hop2 hs_len
    hdi hit_i hbor_i hprot hnd_i hview_i hdp hp_ty hp hview_p hdd hd_ty hbor_d hnd_d hview_d
    (fun entry relOff hlk hsp =>
      ⟨htgt_slot entry relOff hlk hsp, NoCompetingExposedBorrow.of_unexposed hprov pv entry relOff⟩)
    (fun _ _ _ _ q hq => by
      obtain ⟨_, hmem_nil, _⟩ := hprov.sound q (int2ptrCandidates_exposed hq)
      cases hmem_nil)
    hlen_lt hty1 hbad2

/-- Completely hypothesis-free closed 3-segment simulation (`Assume` ->
`PointerExposeProvenance` -> `PointerWithExposedProvenance`) at `exposedTags = []`:
neither `AnnealExposeRoundTripOk`, nor `NoCompetingExposedBorrow`, nor `hnoadj`,
nor `hnd_d` appears in the hypotheses; for whole-local borrows (`entry.targetProjection
= []`), `hsub_slot` is vacuously true. -/
theorem ProvenanceRel.assume_then_expose_then_withExposed_closed_unexposed_from_frameOk
    {body : CapturedMir} {f : Gen.Function}
    {ctx : Ctx} {view : List LocalSlot} {s : MachineState} {lm : Map Gen.LocalName Ptr}
    {m : Mach} {curSeg segStmt nb1 nb2 nb3 : Nat}
    {bb : BasicBlockData} {stA : Statement} {opA : Operand} {opA' : Gen.ValueExpr}
    {i p d : Nat} {di dp dd : LocalDecl}
    {srcMutbl dstMutbl : MirAst.Mutability} {srcIt dstIt : Gen.IntType}
    {op1 op2 : MirAst.Operand} {targetTy1 targetTy2 : MirAst.Ty}
    {span1 span2 : String}
    {pv : ProvenancePtr}
    (hprov : ProvenanceRel body ctx s m [])
    (hframe : FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s.memory.borrows)
      view lm m curSeg segStmt)
    (hb : BorrowsOk body ctx view s lm)
    (hat : AddrTakenTargetsOk body ctx view lm)
    (hstale : StaleOk body s.frame.locals view s.frame.blockIdx s.frame.stmtIdx)
    (hbb : body.basicBlocks[s.frame.blockIdx]? = some bb)
    (hstA : bb.statements[s.frame.stmtIdx]? = some stA)
    (hkA : stA.kind = .intrinsic (.assume opA))
    (hst1 : bb.statements[s.frame.stmtIdx + 1]? =
      some ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩)
    (hst2 : bb.statements[s.frame.stmtIdx + 2]? =
      some ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩)
    (hreadsA : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) [opA] = true)
    (hokBA : operandOkB body.layouts body.localDecls (copyOp opA) = true)
    (hopA : translateOperand body.localDecls opA = some opA')
    (hbits1 : opBits view (copyOp opA) = some 1)
    (hop1 : copyOp op1 = .copy ⟨p, []⟩)
    (hop2 : copyOp op2 = .copy ⟨i, []⟩)
    (hdi : body.localDecls[i]? = some di)
    (hit_i : intTypeOf di.ty = some usizeIt)
    (hi_addr : i ∉ bodyAddrTakenLocals body)
    (hprot : s.memory.activeProtectors = [])
    (hview_i : view[i]? ≠ some .dead)
    (hdp : body.localDecls[p]? = some dp)
    (hp_ty : rawPtrPointeeOf dp.ty = some (srcMutbl, srcIt))
    (hp : s.frame.locals[p]? = some (.init (.ptr pv 8)))
    (hview_p : view[p]? = some (.init (.ptr pv 8)))
    (hdd : body.localDecls[d]? = some dd)
    (hd_ty : rawPtrPointeeOf dd.ty = some (dstMutbl, dstIt))
    (hd_addr : d ∉ bodyAddrTakenLocals body)
    (hcompat : exposeSourceCompatible dstMutbl dstIt (some (srcMutbl, srcIt)) = true)
    (hview_d : view[d]? ≠ some .dead)
    (hsub_slot : ∀ (entry : BorrowEntry) (relOff : Nat),
      lookupBorrow s.memory.borrows pv.tag = some entry →
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (srcIt, relOff) →
      entry.targetProjection ≠ [] →
      ptrDeclLayoutsOk body = true ∧
      ∃ dk v,
        body.localDecls[entry.targetLocal]? = some dk ∧
        s.frame.locals[entry.targetLocal]? = some (.init v) ∧
        DeclSlotOk dk (.init v) body.layouts)
    (hlen_lt : body.localDecls.length < 2 ^ 31 := by decide)
    (hty1 : MirSemantics.exposeTargetBytes? 8 targetTy1 = some 8 := by rfl)
    (hbad2 : MirSemantics.isBadWithExposedTargetTy targetTy2 = false := by rfl) :
    let s0 := advanceStmt s (opPost s.frame.locals opA)
    ∃ (entry : BorrowEntry) (relOff : Nat) (mA m4 m6 m8 mLoad : Mach),
      let fullAddr : Nat := canonicalLocalAddr entry.targetLocal relOff
      let locals1 := (opPost s0.frame.locals op1).set i
        (.init (.scalar ⟨fullAddr, 8⟩))
      let tAddr : Int := ctx.addrs.getD entry.targetLocal 0 + (relOff : Int)
      let tProv : Prov := targetProv ctx entry.targetLocal
      let view1 := view.set i (.init (.scalar ⟨tAddr.toNat, 8⟩))
      let s1 := advanceStmt s0 locals1 (exposeMem s0.memory pv.allocId)
      let locals2 := (opPost locals1 op2).set d (.init (.ptr pv 8))
      let view2 := view1.set d (.init (.ptr pv 8))
      let s2 := advanceStmt s1 locals2 s1.memory
      lookupBorrow s.memory.borrows pv.tag = some entry ∧
      ptrTargetSpec body.layouts body.localDecls ⟨entry.targetLocal, entry.targetProjection⟩ =
        some (dstIt, relOff) ∧
      AnnealExposeRoundTripOk body s0 pv fullAddr ∧
      srcIt = dstIt ∧
      pv.offsetBytes = 0 ∧
      entry.targetLocal ∈ bodyAddrTakenLocals body ∧
      evalStmt s stA body.localDecls body.layouts = MirStepNode.step s0 ∧
      Interp.evalTerminator m
        (.Intrinsic .Assume [opA'] unitPlace (some (bbName nb1))) = .ok mA ∧
      evalStmt s0 ⟨.assign ⟨i, []⟩ (.cast .pointerExposeProvenance op1 targetTy1), span1⟩
        body.localDecls body.layouts = .tau (.running s1) ∧
      Interp.evalTerminator mA
        (.Intrinsic .PointerExposeProvenance [.Load (.Local (localName p))]
          (.Local (localName i)) (some (bbName nb2))) = .ok m4 ∧
      evalStmt s1 ⟨.assign ⟨d, []⟩ (.cast .pointerWithExposedProvenance op2 targetTy2), span2⟩
        body.localDecls body.layouts = .tau (.running s2) ∧
      s2.frame.locals[d]? = some (.init (.ptr pv 8)) ∧
      view2[d]? = some (.init (.ptr pv 8)) ∧
      s2.memory = exposeMem s.memory pv.allocId ∧
      evalValue m4 (.Load (.Local (localName i))) = .ok ((.Int tAddr, .Int usizeIt), m6) ∧
      IntPtrCast.int2ptr m6 tAddr = .ok { addr := tAddr, provenance := some tProv } ∧
      Interp.evalTerminator m4
        (.Intrinsic .PointerWithExposedProvenance [.Load (.Local (localName i))]
          (.Local (localName d)) (some (bbName nb3))) = .ok m8 ∧
      AllocShapeEq m.mem.memory.allocations m8.mem.memory.allocations ∧
      ProvenanceRel body ctx s2 m8 [pv.tag] ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm m8 nb3 0 ∧
      BorrowsOk body ctx view2 s2 lm ∧
      AddrTakenTargetsOk body ctx view2 lm ∧
      evalValue m8 (.Load (.Local (localName d))) =
        .ok ((.Ptr { thin_pointer := offsetPtr (localPtr ctx entry.targetLocal) relOff, metadata := none },
              declPtrTy dd.ty), mLoad) ∧
      FrameOkWithIntrinsics body f (ctxWithBorrows body ctx s2.memory.borrows) view2 lm mLoad nb3 0 ∧
      ((ptrEnvBefore body s.frame.blockIdx (s.frame.stmtIdx + 1)).getD p .disabled ≠ .disabled →
        entry.perm ≠ .disabled ∧
          (dstMutbl = .mut → entry.perm = .active ∨ entry.perm = .reserved)) := by
  exact hprov.assume_then_expose_then_withExposed_closed_from_frameOk
    hframe hb hat hstale hbb hstA hkA hst1 hst2 hreadsA hokBA hopA hbits1
    hop1 hop2 hdi hit_i hi_addr hprot hview_i hdp hp_ty hp hview_p
    hdd hd_ty hd_addr hcompat hview_d
    (fun entry relOff hlk hsp =>
      ⟨hsub_slot entry relOff hlk hsp, NoCompetingExposedBorrow.of_unexposed hprov pv entry relOff⟩)
    (fun _ _ _ _ q hq => by
      obtain ⟨_, hmem_nil, _⟩ := hprov.sound q (int2ptrCandidates_exposed hq)
      cases hmem_nil)
    hlen_lt hty1 hbad2

end MiniRustSpec.Correspondence
