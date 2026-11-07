/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointerStep

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
which adds what array, `TupleSpec`, and raw pointer locals need:
`NonScalarLive`; `BorrowsOk` (every entry of Anneal's borrow table is the
`rawPtrEntry` of an admissible borrow target, a parameter that stays live at
its caller-allocated address, and every initialized raw pointer local holds
the tag of such an entry at offset `0`, `Active` for a `*mut` local); and
`LocalsOk` at `ctxWithBorrows` (the MiniRust bytes of every initialized raw
pointer local encode the address and provenance of its tag's target).
`step_correspondence` is the all-scalar special case. The raw pointer
statements rest on `MiniRustSpec.Correspondence.PointerStep`.
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
  | .len p, hop_mem, _ =>
    simp [rvOperands] at hop_mem; subst hop_mem; simp [opMoved] at hop_mv
  | .copyForDeref _, hop_mem, _ | .ref _ _, hop_mem, _
  | .rawPtr _ _, hop_mem, _ | .discriminant _, hop_mem, _
  | .threadLocalRef _, hop_mem, _ | .nullaryOp _ _, hop_mem, _
  | .shallowInitBox _ _, hop_mem, _ | .wrapUnsafeBinder _ _, hop_mem, _ =>
    simp [rvOperands] at hop_mem

/-- The operands of a pointer-copying fragment rvalue move out of declared
locals only. -/
private theorem ptrRvalueOk_moved_lt {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {mutbl : MirAst.Mutability} {pointeeIt : Gen.IntType} {rv : Rvalue}
    (h : ptrRvalueOk layouts decls mutbl pointeeIt (copyRv rv) = true) {j : Nat}
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
    cases k <;> simp only [copyRv, copyOp, ptrRvalueOk, Bool.and_eq_true, decide_eq_true_eq] at h <;>
      first | exact h.1.1 | exact h.1 | cases h
  | binaryOp bop a b =>
    simp only [rvOperands, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · cases b <;> cases bop <;> simp_all [copyRv, copyOp, ptrRvalueOk]
    · cases a <;> cases bop <;> simp_all [copyRv, copyOp, ptrRvalueOk]
  | _ => simp_all [rvOperands, copyRv, ptrRvalueOk]

/-- A raw pointer dereference read moves out of no local. -/
private theorem ptrDerefReadOk_noMove {decls : List LocalDecl} {it : Gen.IntType} {rv : Rvalue}
    (h : ptrDerefReadOk decls it (copyRv rv) = true) : (rvOperands rv).filterMap opMoved = [] := by
  cases rv with
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
            cases mutbl <;> simp only [hpt] at hs <;> try cases hs
            rw [foldl_moveOut_of_noMove (rvalueOk_noMove hs).2] at hj
            exact .inl hj
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
  | .placeMention _, _, hj | .setDiscriminant _ _, _, hj | .retag _ _, _, hj
  | .intrinsic _, _, hj | .coverage, _, hj | .constEvalCounter, _, hj
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
  | goto _ | unreachable | return_ | unwindResume | unwindTerminate | drop _ _ _
  | call _ _ _ _ _ | tailCall _ _ | assert _ _ _ _ | inlineAsm _ _ _ =>
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
  | goto _ | unreachable | return_ | unwindResume | unwindTerminate | drop _ _ _
  | call _ _ _ _ _ | tailCall _ _ | assert _ _ _ _ | inlineAsm _ _ _ =>
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
      | _ => exact readsOk_mono hsub h
    | cons _ _ =>
      simp only [stmtReadsOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
      refine ⟨readsOk_mono hsub h.1, fun j hj => ?_⟩
      have h2 := h.2 j hj
      simp only [Bool.not_eq_true', Bool.eq_false_iff, Ne, List.contains_iff_mem] at h2 ⊢
      intro hm
      apply h2
      apply (foldl_moveOut_mem (rvOperands rv) mo' j).mpr
      rcases (foldl_moveOut_mem (rvOperands rv) mo j).mp hm with hmo | hmv
      · exact .inl (hsub j hmo)
      · exact .inr hmv
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
  | goto _ | unreachable | unwindResume | unwindTerminate | drop _ _ _
  | call _ _ _ _ _ | tailCall _ _ | assert _ _ _ _ | inlineAsm _ _ _ => rfl

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
  have hspec := translateFn_spec body f h.hf
  have hloc0 := (hspec.2.1 0 d hd).2
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
    (∃ p pe, st.kind = .deinit p ∧ translatePlace decls p = some pe ∧ st' = .Deinit pe) := by
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
    | some pe => simp [hpe] at h; exact .inr (.inr (.inr (.inr ⟨p, pe, rfl, hpe, h.symm⟩)))
  | .storageLive i, h => simp at h; exact .inr (.inr (.inl ⟨i, rfl, h.symm⟩))
  | .storageDead i, h => simp at h; exact .inr (.inr (.inr (.inl ⟨i, rfl, h.symm⟩)))
  | .retag _ _, h => simp at h
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
    obtain ⟨_, _, _, _, hmem, _, _⟩ := hb.entries_ok e he
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
    ⟨hf, resetPick_shape hshape, hlo, hdeclsOk, hns⟩
  have hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals := hrel.stale.slots hlo.slots
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
    have hpresSt := stmtPreservesAddrTaken_not_target ((hpresAll bb hbbmem).1 st hstmem)
    rcases translateStatement_some hst' with
      ⟨dst, rv, pe, e, hkind, hpe, he, rfl⟩ |
      ⟨p, pe, hkind, hpe, rfl⟩ |
      ⟨i, hkind, rfl⟩ |
      ⟨i, hkind, rfl⟩ |
      ⟨p, pe, hkind, hpe, rfl⟩
    · ------------------------------------------------------------ assign
      have hdst_addr : dst.local_ ∉ bodyAddrTakenLocals body := hpresSt.1 dst rv hkind
      rcases dst with ⟨i, projs⟩
      simp only at hdst_addr
      have hbor_i := hbo.target_ne_of_not_addrTaken hdst_addr
      -- Storing a non-pointer slot into the local `_i` keeps `BorrowsOk`.
      have hBset : ∀ (d : LocalDecl), body.localDecls[i]? = some d → isPtrTy d.ty = false →
          ∀ (x : LocalSlot) (locals' : List LocalSlot),
            BorrowsOk body ctx (view.set i x) (advanceStmt s locals' s.memory) lm :=
        fun d hd hnp x _ => hbo.advance_set_nonptr i x (fun hk => absurd hk hdst_addr)
          (fun dp pv hdp hpty => by
            rw [hd] at hdp; cases hdp; rw [hnp] at hpty; cases hpty)
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
            obtain ⟨pointeeIt, relOff, hpt, htspec⟩ := statementOk_rawPtr_spec hdi hok
            have hp_ty : isPtrTy d.ty = true := by simp [isPtrTy, hpt]
            have hq_addr : q.local_ ∈ bodyAddrTakenLocals body :=
              mem_bodyAddrTakenLocals hbbmem hstmem rfl
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
            obtain ⟨hA1, hA2⟩ := evalStmt_assign_rawPtr s body.localDecls body.layouts i mutbl q span
              hnd hni _ hsq hliveq hi hbor_i hqi hrel.protectors
            by_cases hdead : s.frame.locals[i]? = some .dead
            · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
              obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal e
              rw [hA2 hdead]
              exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
            · have hlive : view[i]? ≠ some .dead := fun h => hdead ((hrel.stale.dead_iff i).mpr h)
              rw [hA1 hdead]
              obtain ⟨m3, hm3, h3⟩ := evalStatement_assign_rawPtr_mr hframe hbo hns hfrag i d hdi
                hp_ty hlive mutbl q pointeeIt relOff htspec hq_addr e he
              obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
              refine StepRelN.tau' m4
                (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
              have hstale := hrel.stale.assign hbb hst rfl (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8))
              exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init (.ptr ⟨s.memory.nextTag, 0⟩ 8)))
                _ lm m4 h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar hstale
                (retLive_set hrel.retLive i (by simp))
                (hbo.rawPtr hpa hbb hst rfl pointeeIt relOff htspec
                  (fun dp hdp => by rw [hdi] at hdp; cases hdp; exact hpt) hdst_addr _)
                rfl rfl rfl rfl
          · by_cases hder : ∃ p rest, copyRv rv = .use (.copy ⟨p, .deref :: rest⟩)
            · ---------------------------------------------------- `_i = copy (*_p)` / `move (*_p)`
              obtain ⟨p, rest, hcrv⟩ := hder
              obtain ⟨rfl, it, dp, srcMutbl, hit, hdp, hpt⟩ := statementOk_derefRead hdi hcrv hok
              have hitd : itOf d body.layouts = it := (tyOf_int hit).2
              have hint : intTypeOf d.ty = some (itOf d body.layouts) := by rw [hitd]; exact hit
              have hnpd : isPtrTy d.ty = false := Bool.eq_false_iff.mpr fun hp => by
                rw [(not_other_of_isPtrTy (layouts := body.layouts) hp).2.2.2.1] at hit; cases hit
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
              obtain ⟨res, hMok, hMnone, hAok, hAnone⟩ : ∃ res : Option Value,
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
                      .ok v s.frame.locals s.memory) ∧
                  (res = none →
                    evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts = .ub) := by
                rcases evalPlace_deref hframe hbo hns hfrag p dp srcMutbl it hdp hpt with
                  ⟨ptrVal, entry, relOff, m1, hvp, hlookup, _, hk_addr, htspec, hderef, h1, htgt⟩ |
                  ⟨hnot, msg, hmsg⟩
                · obtain ⟨hni, hnd, _⟩ := evalTargetPlace hframe hbo hns hfrag
                    ⟨entry.targetLocal, entry.targetProjection⟩ it relOff htspec hk_addr
                  have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                  have hk_lt := (ptrTargetSpec_cases hdeclsOk htspec).1
                  obtain ⟨slotk, hsk⟩ : ∃ slot, s.frame.locals[entry.targetLocal]? = some slot :=
                    ⟨_, List.getElem?_eq_getElem (by rw [hnA]; exact hk_lt)⟩
                  have hmem := (lookupBorrow_mem_and_tag hlookup).1
                  have hEq := evalRvalue_derefRead_eq s.frame.locals hcrv s.memory body.localDecls
                    body.layouts ptrVal 8 (hpAgree.trans hvp) entry hlookup
                    (hbo.perm_ne_disabled hmem) hnd slotk hsk
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
                  have hfr : rvBits body.localDecls s.frame.locals (itOf d body.layouts) body.layouts
                      (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) =
                      rvBits body.localDecls view (itOf d body.layouts) body.layouts
                        (.use (.copy ⟨entry.targetLocal, entry.targetProjection⟩)) :=
                    rvBits_frame_raw hagq
                  obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA
                    (itOf d body.layouts) hgood _ hokq (hns.opsInit_of_readsAgree hagq) s.memory
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
                      (fun r => .scalar ⟨r, (itOf d body.layouts).size.bytes⟩), ?_, ?_, ?_, ?_⟩
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
                    rw [hEq]
                    exact hA1 r (hfr.trans hr)
                  · intro hv
                    rw [hEq]
                    exact hA2 (hfr.trans (Option.map_eq_none_iff.mp hv))
                · refine ⟨none, fun _ h => (by cases h), fun _ hlive => ?_, fun _ h => (by cases h),
                    fun _ => ?_⟩
                  · obtain ⟨_, slot, _, hs⟩ := hframe.slot_exists i hi_decl
                    obtain ⟨pi, hpi⟩ := hframe.locs.some_of_live hs (fun hc => hlive (hc ▸ hs))
                    exact ⟨msg, evalStatement_assign_load_ub
                      (evalPlace_local_some hframe.shape i _ hspecF.2 pi hpi) hmsg⟩
                  · exact evalRvalue_derefRead_ub s.frame.locals hcrv s.memory body.localDecls
                      body.layouts (by rw [hpAgree]; exact hnot)
              obtain ⟨hA1, hA2⟩ := evalStmt_assign_val s body.localDecls body.layouts i rv span hi
                hbor_i hrel.protectors
              by_cases hdead : s.frame.locals[i]? = some .dead
              · have hvd : view[i]? = some .dead := (hrel.stale.dead_iff i).mp hdead
                obtain ⟨msg, hmsg⟩ := evalStatement_assign_dead hframe i d hdi hvd hal
                  (.Load (.Deref (.Load (.Local (localName p))) (.Int it)))
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
                  have hstale := hrel.stale.assign hbb hst rfl (.init v)
                  rw [rvPost_derefRead hcrv] at hstale
                  exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init v)) _ lm m4 h4.threads
                    h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar hstale
                    (retLive_set hrel.retLive i (by simp)) (hBset d hdi hnpd _ _) rfl rfl rfl rfl
            · ---------------------------------------------------- any other rvalue
              have hnder : ∀ p rest, copyRv rv ≠ .use (.copy ⟨p, .deref :: rest⟩) :=
                fun p rest h => hder ⟨p, rest, h⟩
              have hnraw : ∀ m q, rv ≠ .rawPtr m q := fun m q h => hraw ⟨m, q, h⟩
              have hreadsMo : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx)
                  (rvOperands rv) = true := by
                rw [← stmtReadsOk_root_of_not_deref (span := span) (i := i) hnder]; exact hreads
              have hr0 : readsOk [] (rvOperands rv) = true :=
                readsOk_mono (fun _ h => by simp at h) hreadsMo
              have hagree := hrel.stale.readsAgree hreadsMo
              simp only [statementOk] at hok
              obtain ⟨res, hk, hMok, hMnone, hAok, hAnone, hBok⟩ : ∃ res : Option Value,
                  moveKind rv = true ∧
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
                    moveKind_of_rvalueOkB hokB, ?_, ?_, ?_, ?_, fun v l _ => hBset d hdi hnp _ l⟩
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
                      moveKind_of_rvalueOkO hokO, ?_, ?_, ?_, ?_, fun v l _ => hBset d hdi hnp _ l⟩
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
                        moveKind_of_rvalueOkTuple hokT, ?_, ?_, ?_, ?_,
                        fun v l _ => hBset d hdi hnp _ l⟩
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
                          moveKind_of_rvalueOk hok', ?_, ?_, ?_, ?_, fun v l _ => hBset d hdi hnp _ l⟩
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
                            moveKind_of_arrayRvalueOk hok, ?_, ?_, ?_, ?_,
                            fun v l _ => hBset d hdi hnp _ l⟩
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
                                  (copyRv rv) = true := by
                                simpa [hdi, hb, ho, htup, hit, ha, ht, hpt] using hok
                              have hnrawC : ∀ m q, copyRv rv ≠ .rawPtr m q := by
                                intro m q h
                                cases rv with
                                | rawPtr m' q' => exact hnraw m' q' rfl
                                | _ => simp [copyRv] at h
                              obtain ⟨pE, hpmemE, hMptr, hMub⟩ :=
                                evalStatement_assign_ptrRvalue_mr hframe hbo hns hfrag i d hdi hpt
                                  hokP hnrawC e he
                              obtain ⟨pA, _, hpmemA, ⟨srcMutbl, hsrc, _⟩, hAev⟩ :=
                                evalRvalue_ptrRvalue hokP hnrawC
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
                              have hk := moveKind_of_ptrRvalueOk hokP hnraw
                              cases slotp with
                              | init v =>
                                obtain ⟨pv, rfl⟩ := (DeclSlotOk_of_isPtrTy hisPtrP (.init v)).mp hslotOk
                                obtain ⟨hMok', entry, relOff, hoff0, hlookup, hact, htspec⟩ :=
                                  hMptr pv hsp
                                refine ⟨some (.ptr pv 8), hk, fun v hv hlive => ?_, fun hv => (by cases hv),
                                  fun v hv => ?_, fun hv => (by cases hv), fun v locals' hv => ?_⟩
                                · cases hv; exact hMok' hlive
                                · cases hv
                                  exact (hAev s.frame.locals s.memory).1 pv 8 (hpAgree.trans hsp)
                                · cases hv
                                  exact hbo.advance_set_ptr i pv hdst_addr
                                    (fun dp' mutbl' pointeeIt' hdp' hpt' => by
                                      rw [hdi] at hdp'; cases hdp'; rw [hpt] at hpt'; cases hpt'
                                      exact ⟨entry, relOff, hoff0, hlookup, hact, htspec⟩)
                              | uninit =>
                                refine ⟨none, hk, fun v hv => (by cases hv),
                                  fun _ hlive => hMub (.inl hsp) hlive, fun v hv => (by cases hv),
                                  fun _ => (hAev s.frame.locals s.memory).2 (.inl (hpAgree.trans hsp)),
                                  fun v _ hv => (by cases hv)⟩
                              | dead =>
                                refine ⟨none, hk, fun v hv => (by cases hv),
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
                              moveKind_of_tupleRvalueOk hok, ?_, ?_, ?_, ?_,
                              fun v l _ => hBset d hdi hnp _ l⟩
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
                hi hbor_i hrel.protectors
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
        have hreads' : readsOk (movedBefore body s.frame.blockIdx s.frame.stmtIdx) (rvOperands rv) =
            true ∧
            ∀ j ∈ placeLocals ⟨i, proj :: rest⟩,
              j ∉ (rvOperands rv).foldl moveOut
                (movedBefore body s.frame.blockIdx s.frame.stmtIdx) := by
          simpa [stmtReadsOk, hkind, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
            using hreads
        have hreadsMo := hreads'.1
        have hagree := hrel.stale.readsAgree hreadsMo
        have hplAgree : ∀ j ∈ placeLocals ⟨i, proj :: rest⟩, s.frame.locals[j]? = view[j]? :=
          fun j hj => hrel.stale.agree fun hmo =>
            hreads'.2 j hj ((foldl_moveOut_mem _ _ j).mpr (.inl hmo))
        have hiAgree : s.frame.locals[i]? = view[i]? :=
          hplAgree i (local_mem_placeLocals ⟨i, proj :: rest⟩)
        obtain ⟨kind, span⟩ := st
        simp only at hkind
        subst hkind
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
                      obtain ⟨newRootVal, m3, _, hwsem, hm3, h3⟩ := hMok r hr
                      rw [hAok r newRootVal (hfr.trans hr) hwsem]
                      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                      refine StepRelN.tau' m4
                        (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                      exact hrel.advanceN hfrag hbb hlt _ (view.set i (.init newRootVal)) _ lm m4
                        h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar
                        (hrel.stale.setBothKeep hbb hst
                          (by simp [stmtMoved, foldl_moveOut_of_noMove hnoMv]) (.init newRootVal))
                        (retLive_set hrel.retLive i (by simp)) (hBset d hdi hnp _ _)
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
                    (retLive_set hrel.retLive i (by simp)) (hBset d hdi hnp _ _) rfl rfl rfl rfl
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
                have hrvok : rvalueOk body.layouts body.localDecls pointeeIt rv = true := by
                  simpa [hpt] using hok
                obtain ⟨hcrv, hnoMv⟩ := rvalueOk_noMove hrvok
                rw [hcrv] at he
                rw [translatePlace_deref hdi hpt, Option.some.injEq] at hpe
                subst hpe
                have hgoodP : GoodSize pointeeIt.size.bytes := ptrPointeeOf_good hpt
                have hnsOps : OpsNonScalarInit body.localDecls s.frame.locals (rvOperands rv) :=
                  hns.opsInit_of_readsAgree hagree
                obtain ⟨hAok, hAwub, hAub⟩ := evalStmt_assign_derefWrite s body.localDecls
                  body.layouts i rv span hrel.protectors hrel.callerLocals
                rcases evalPlace_deref hframe hbo hns hfrag i dp .mut pointeeIt hdi hpt with
                  ⟨ptrVal, entry, relOff, m1, hvp, hlookup, hact, hk_addr, htspec, hderef, h1, htgt⟩ |
                  ⟨hnot, msg, hmsg⟩
                · have hact' : entry.perm = .active := hact rfl
                  have hpA : s.frame.locals[i]? = some (.init (.ptr ptrVal 8)) := hiAgree.trans hvp
                  have hkAgree := hrel.stale.addrTaken_eq hpa hk_addr
                  obtain ⟨hnd_k, _, hd_k⟩ := hbo.target_ptrs hfrag entry.targetLocal hk_addr
                  have hopok := ptrTargetSpec_operandOk hdeclsOk htspec
                  obtain ⟨targetPe, htpe⟩ : ∃ pe, translatePlace body.localDecls
                      ⟨entry.targetLocal, entry.targetProjection⟩ = some pe := by
                    simp only [operandOk, Bool.and_eq_true, translateOperand,
                      Option.isSome_map] at hopok
                    exact Option.isSome_iff_exists.mp hopok.2
                  obtain ⟨res, hRok, hRnone⟩ := derefWrite_target h1 hbo hfrag hslotsA hnA _ pointeeIt
                    relOff htspec hk_addr hkAgree rv hrvok hagree e he targetPe htpe
                  have hMeq := evalStatement_assign_place_eq e hderef (htgt targetPe htpe)
                  have hinv := hbo.invalidateDeref_noop s.frame.locals i ptrVal entry hpA hlookup hact'
                  cases hres : res with
                  | none =>
                    obtain ⟨⟨msg, hmsg⟩, hAu⟩ := hRnone hres
                    rw [hAub hAu]
                    exact StepRelN.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hMeq, hmsg])
                  | some w =>
                    obtain ⟨⟨m3, hm3, h3⟩, v, hv, hwshape⟩ := hRok w hres
                    have hw : writePlaceValue s.frame.locals s.memory.borrows ⟨i, [.deref]⟩ v =
                        .ok (s.frame.locals.set entry.targetLocal (.init w)) := by
                      rcases hwshape with ⟨hproj, rfl⟩ | ⟨ph, pt, rootVal, hproj, hroot, hwp⟩
                      · have hk_lt := (ptrTargetSpec_cases hdeclsOk htspec).1
                        obtain ⟨slotk, hsk⟩ : ∃ slot, s.frame.locals[entry.targetLocal]? = some slot :=
                          ⟨_, List.getElem?_eq_getElem (by rw [hnA]; exact hk_lt)⟩
                        exact writePlaceValue_deref_root s.frame.locals s.memory.borrows i w ptrVal 8 hpA
                          entry hlookup hact' hproj slotk hsk
                          (fun hc => hnd_k (by rw [← hkAgree, hsk, hc]))
                      · exact writePlaceValue_deref_proj s.frame.locals s.memory.borrows i v ptrVal hpA
                          entry hlookup hact' ph pt hproj rootVal w hroot hwp
                    rw [hAok v _ hv hw hinv]
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    refine StepRelN.tau' m4
                      (by simp [hne, listIndex_nat _ _ _ htst, hMeq, hm3, hm4, check_after h4]) ?_
                    exact hrel.advanceN hfrag hbb hlt _ (view.set entry.targetLocal (.init w)) _ lm m4
                      h4.threads h4.active (by rw [h4.allocs]; exact h3.locs) h3.nonScalar
                      (hrel.stale.setBothKeep hbb hst
                        (by simp [stmtMoved, foldl_moveOut_of_noMove hnoMv]) (.init w))
                      (retLive_set hrel.retLive _ (by simp))
                      (hbo.advance_set_nonptr _ (.init w) (fun _ => by simp)
                        (fun dp' pv hdp' hpty => absurd hpty (by rw [(hd_k dp' hdp').1]; simp)))
                      rfl rfl rfl rfl
                · ---------------------------------------- through an uninitialized pointer: UB
                  have hnotA : s.frame.locals[i]? = some .uninit ∨ s.frame.locals[i]? = some .dead := by
                    rw [hiAgree]; exact hnot
                  obtain ⟨hA1, hA2⟩ := evalRvalue_frag body.localDecls s.frame.locals hslotsA hnA
                    pointeeIt hgoodP rv hrvok hnsOps s.memory
                  have hA : evalStmt s ⟨.assign ⟨i, [.deref]⟩ rv, span⟩ body.localDecls body.layouts =
                      MirStepNode.fail .ub := by
                    cases hr : rvBits body.localDecls s.frame.locals pointeeIt body.layouts rv with
                    | none => exact hAub (hA2 hr)
                    | some r =>
                      exact hAwub _ (hA1 r hr)
                        (writePlaceValue_deref_not_init s.frame.locals s.memory.borrows i _ hnotA)
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
                          (retLive_set hrel.retLive i (by simp)) (hBset d hdi hnp _ _)
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
          hbo.advance_keep rfl rfl rfl rfl
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
      rw [evalStmt_storageLive s body.localDecls body.layouts i span hi]
      obtain ⟨m3, lm3, hm3, h3, hlm3⟩ := evalStatement_storageLive hframe i d hd hal hscalar
        hrel.baseLow hn31
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
      refine StepRelN.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
      exact hrel.advanceN hfrag hbb hlt _ (view.set i .uninit) _ lm3 m4 h4.threads h4.active
        (by rw [h4.allocs]; exact h3.locs) h3.nonScalar (hrel.stale.setBoth hbb hst rfl .uninit)
        (retLive_set hrel.retLive i (by simp))
        (hbo.advance_storage i .uninit hi_addr (fun _ _ _ _ => by simp)
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
      rw [evalStmt_storageDead s body.localDecls body.layouts i span hi]
      obtain ⟨m3, hm3, h3⟩ := evalStatement_storageDead hframe i d hd hal hscalar
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
      refine StepRelN.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
      exact hrel.advanceN hfrag hbb hlt _ (view.set i .dead) _ _ m4 h4.threads h4.active
        (by rw [h4.allocs]; exact h3.locs) h3.nonScalar (hrel.stale.setBoth hbb hst rfl .dead)
        (by rw [List.getElem?_set_ne (by omega)]; exact hrel.retLive)
        (hbo.advance_storage i .dead hi_addr (fun _ _ _ _ => by simp)
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
            (hbo.advance_storage i .uninit hi_addr (fun _ _ _ _ => by simp) (fun _ _ => rfl))
            rfl rfl rfl rfl
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
          (hstale_end.toBlock hsub) (hbo.jump hpa hbb t (by simp [termTargets, hk]) _))
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
      have hmove := evalOperand_move s.frame.locals discr hsimple s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals
      cases hb : opBits view (copyOp discr) with
      | none =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk, hmove, hAnone (hbitsEq.trans hb), opWithLocals]
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
          simp [MirSemantics.evalTerminator, hk, hmove, hAok bits (hbitsEq.trans hb), opWithLocals,
            jumpState]
        rw [hA]
        have hM : evalTerminator (resetPick m) tb.terminator = .ok m4 := by
          rw [htt]
          simp only [Interp.evalTerminator, hm3, ok_bind]
          rw [hlookup]
          exact hm4
        exact StepRelN.emit' _ m4 rfl (by simp [hM, check_after h4])
          (hrel.jumpN hfrag lm _ htgt _ h4.threads h4.active (by rw [h4.allocs]; exact h3.locs)
            h3.nonScalar (hstale_end.toBlockMove discr hsub) (hbo.jump hpa hbb _ htgtMem _))
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
    | some d, some slot => (scalarTypeOf d.ty).isSome || slotIsInit slot
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
    simp only [hd, hs, hnone, Option.isSome_none, Bool.false_or] at hchk
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

/-- **Init block (`StateRelN`).** From `StartRel` (Anneal at `(0, 0)` and
MiniRust at `f.start`), `initLen body` MiniRust steps execute `minimize`'s init
block (`StorageLive` of each temporary of `alwaysStorageLiveLocals`, then
`Goto(bb0)`) and land in `StateRelN`. -/
theorem step_start_N {body : CapturedMir} {f : Gen.Function} (hfrag : inFragment body = true)
    (hf : translateFn body = some f) {ctx : Ctx} {s : MachineState} {mInit : Mach}
    (hstart : StartRel body f ctx s mInit)
    (hns : nonScalarSlotsInit body s.frame.locals = true := by decide) :
    ∃ m0, Interp.steps (initLen body) mInit = .ok m0 ∧ StateRelN body f ctx s m0 := by
  obtain ⟨_, hargs, hn31, _, hdeclsOk, htemps, _, _, _, _⟩ := inFragment_spec body hfrag
  obtain ⟨hfstart, hinit⟩ := translateFn_start body f hf
  have hAnd := alwaysStorageLiveLocals_nodup body
  have hlenS : (initBlock body).statements.length = (alwaysStorageLiveLocals body).length := by
    simp [initBlock]
  have key : ∀ k, k ≤ (alwaysStorageLiveLocals body).length → ∃ m lm,
      Interp.steps k mInit = .ok m ∧
      Shape m ctx [ctx.caller, calleeFrameL f ctx lm body.basicBlocks.length k]
        m.mem.memory.allocations ∧
      LocalsOkA body ctx ((alwaysStorageLiveLocals body).take k) s.frame.locals lm
        m.mem.memory.allocations ∧
      NonScalarLive body s.frame.locals lm ∧
      (∀ j, j < body.argCount + 1 → mapGet lm (localName j) = some (localPtr ctx j)) := by
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
      obtain ⟨m3, lm3, hm3, hsh3, hlo3, hns3, hlm3⟩ := evalStatement_storageLive_init hf
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
  obtain ⟨m, lm, hm, hsh, hlo, hnsL, hlmP⟩ := key _ (Nat.le_refl _)
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
    refine BorrowsOk.start hstart.borrows (fun _ k hk => ?_) hnoPtr
    obtain ⟨hk1, hk2⟩ := haddrP k hk
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
          rw [hT] at hv
          exfalso
          revert hv
          unfold argOk
          split <;> simp [validBits, thinRawPtrTy, tupleIntOfTy]
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
      simp [hdecls, hinit, h0sc]
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

end MiniRustSpec.Correspondence
