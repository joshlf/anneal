/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.Memory.ProvenanceMap
import Miri.Memory.Identity
import Miri.Memory.CtfeProvenance
import Miri.Memory.Validity
import Miri.Memory.Allocation
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_08_01.MirSemantics.Statements
import Trusted.Rustc.V2026_08_01.MirSemantics.Terminators

/-!
# Episode 2 Dual-Authority Correspondence (`LeanMiriSpec` Authority):
# pointer-byte fragment coherence (`UCG#558` / `rust#148259`) against unmodified vendored
# `Miri.Memory.ProvenanceMap`, and read-time validity (`Kani#5205`)

Correspondence between the pointer-byte codec of `Trusted.Rustc.V2026_{06,08}_01.MirSemantics`
(`encodePtrBytes`, `abstractBytesCoherentPtrProv?`, `decodePtrBytesNoForge`,
`decodeTypedValueFromBytes`, `validateValueForTy?`, `writeBytesAction`, `evalOperand`) and the
**unmodified vendored** `Miri.Memory.ProvenanceMap` (`PointerFrag`, `ProvenanceMap.fromParts`,
`ProvenanceMap.fromPresortedPtrs`, `ProvenanceMap.readPtr`, `ProvenanceMap.getByte`,
`ProvenanceMap.clear`, `ProvenanceMap.prepareCopy`, `ProvenanceMap.applyCopy`, and the
`private` `inspectFragments`, reached by name resolution only through `delta_miri_private`),
`Miri.Memory.{Provenance, AllocId, CtfeProvenance}`, `Miri.Memory.Allocation`, and
`Miri.Memory.Validity.checkPrimitive`.
No vendored definition is copied or restated.

## The translation

`mkFrag pv f` maps a `Trusted` `PtrByteFrag { allocId, tag, byteIdx, origOffset, ptrBytes }` to
the vendored `PointerFrag { idx := UInt8.ofNat byteIdx, prov := pv allocId tag,
bytes := ptrImage ptrBytes origOffset }`, where `ptrImage` is the zero-padded little-endian
8-byte image that vendored `ptrFragments` builds. `trEntries pv bytes` places one such fragment at
the offset of every fragment-carrying byte, giving the state
`ProvenanceMap.fromParts #[] (some (trEntries pv bytes))`. The embeddings are `pvRt` (Miri runtime
`Provenance.concrete`, `offsetIsAddr = true`, injective on `(allocId, tag)` for `< 2^64 - 1`,
wildcard available) and `pvCt` (CTFE `AllocId`, `offsetIsAddr = false`, tag-free, no wildcard).

## Theorem surface (`V06` and `V08` generated identically)

1. **Byte-vector injectivity** (`ptrImage_inj`, `normOffset_image_inj`): for every width
   `0 < ptrBytes ≤ 8` (in particular `4` and `8`), two normalized offsets have equal vendored
   `PointerFrag.bytes` iff they are equal.
2. **Vendored `readPtr`, `clear`, `prepareCopy`, and `applyCopy`** (`readPtr8_runtime`,
   `readPtr8_ctfe`, `readPtr4_runtime`, `readPtr4_ctfe`, `mem_qsort`, `clear_partial_mid_strips_8`,
   `clear_partial_mid_strips_4`, `clear_partial_7bytes_strips_8`, `prepareCopy_applyCopy_intact_8`,
   `prepareCopy_applyCopy_splice_p_p256`): kernel-checked closed forms of the unmodified vendored
   `readPtr` / `inspectFragments` on symbolic fragments, PLUS propositional membership invariance
   of Lean 4's `Array.qsort` (`mem_qsort`), directly proving partial-overwrite splitting through
   vendored `ProvenanceMap.clear` and end-to-end bytewise copy / `p`+`p+256` splicing through
   vendored `ProvenanceMap.prepareCopy` + `applyCopy` + `readPtr`!
3. **Universal `Trusted` ↔ vendored `readPtr` correspondence over ALL byte streams** (`coh_iff8`,
   `coh_iff4`, `readPtr8_runtime_corr`, `readPtr8_ctfe_corr`, `readPtr4_runtime_corr`,
   `readPtr4_ctfe_corr`, AND the unrestricted all-bytes theorems `readPtr8_allBytes_runtime_corr`,
   `readPtr8_allBytes_ctfe_corr`, `readPtr4_allBytes_runtime_corr`, `readPtr4_allBytes_ctfe_corr`
   with explicit `↔` biconditionals): for **every** 8-byte (resp. 4-byte) `Trusted` stream —
   whether fully fragmented, partially plain, all-plain, or containing `.uninit` bytes — the
   vendored read of the translated state returns `.ok (some (pv allocId tag))` iff
   `abstractBytesCoherentPtrProv? bytes = some _`, `.ok none` in runtime mode (and in CTFE mode
   when fragment-free), and `.error (.readPartialPointer 0)` in CTFE mode whenever fragments are
   present but incoherent.
4. **Universal intact round-trips & wide pointers** (`intact_roundtrip_8`, `intact_roundtrip_4`,
   `rawCarrier_ptr_roundtrip_8`, `rawCarrier_ptr_roundtrip_4`, `w_lm_wide_slice_and_str`,
   `w_lm_wide_dyn`): thin 64-bit & 32-bit, union raw-byte carrier, and wide `&[u8]` / `*const [u8]`
   / `&str` / `&dyn Trait` round-trips and adversarial stripping.
5. **Three-way witnesses** (`w_lm_*`), each instantiating the universal theorems for both Miri
   provenance kinds: intact round trip, all-zero reversal, reversal, swap, duplication, rotation,
   `p` / `p + 4` and `p` / `p + 256` splices, mixed allocation, 32-bit intact / reversal /
   splice, missing provenance and uninitialized bytes, misaligned cross-relocation reads and
   32-bit non-bleed (`w_lm_misaligned`), wildcard behaviour (`w_lm_wildcard`), CTFE tag-blindness
   (`w_lm_ctfe_tag_blind`), and `Kani#5205` (`miri_checkPrimitive_bool_iff`,
   `miri_checkPrimitive_char_iff`, `kani5205_bool_validity_iff`, `kani5205_char_validity_iff`,
   `w_lm_kani5205_trusted`, `w_lm_kani5205_miri`, `w_lm_kani5205_alloc_e2e`, `w_lm_kani5205_e2e`).
6. **Lockstep parity** (`lm_lockstep_parity`) and the audit `#assert_ptr_byte_coherence_lm_audit`.

## Scoped divergences and scope

* `DIV-LM-WILDCARD` (`w_lm_wildcard`): vendored `inspectFragments` skips wildcard fragments, so a
  wildcard byte next to seven coherent bytes still reads the concrete provenance. `Trusted` has no
  wildcard (exposed) provenance and the translation never produces one; a wildcard does not rescue
  an offset splice in either authority.
* `DIV-LM-CTFE-TAG` (`w_lm_ctfe_tag_blind`): CTFE provenance (`AllocId`) carries no Tree Borrows
  tag (`pvCt a t` ignores `t`), so splicing two pointers into the same allocation under distinct
  borrow tags is stripped by `Trusted` and Miri runtime (`pvRt`, `Provenance.concrete`) while
  tag-free CTFE `AllocId` retains the allocation ID.
* `DIV-LM-CROSS-WIDTH`: vendored `PointerFrag` carries no pointer width, so a 4-byte read of the
  first half of an 8-byte pointer's fragments is accepted by `readPtr` while `Trusted` requires
  `frag.ptrBytes = ptrBytes`. A single Miri allocation never mixes pointer widths (`pointerSize`
  is the target's); the correspondence is stated for well-formed fragments (`WF`) of the target
  width, where the two agree exactly.

## Correspondence-gap postmortem (`mir-correspondence-postmortem.md`)

Why the pre-Episode-1 `LeanMiriSpec` (and `MiniRustSpec`) suites did not catch the soundness bugs
closed in Episode 1:

* **`UCG#558` W1 (byte permutation) and W2 (offset splices).** The `LeanMiriSpec` memory
  correspondence (`PtrLM3_1`, `CopyLM4_2`, `UnionLM2_4`, `MemoryLemmas`) related `Trusted`
  pointers only to whole-pointer `ProvenanceMap.ptrs` entries of aligned, size-preserving copies;
  every proof went through `read_exact_pointer` / `clear_new` / `readPtr_new`, never through the
  fragment path (`byteFragments`, `inspectFragments`, partial `clear`, sub-pointer `prepareCopy` /
  `applyCopy`). A permuted or spliced byte image never arises from aligned whole-pointer copies, so
  the gap between `Trusted`'s old per-byte `(allocId, tag)` merge and Miri's fragment rule was
  outside the proven scope (`pm_w1_whole_pointer_path_only` exhibits the two paths). Vendored
  MiniRust additionally lacks the originating offset in `ProvenanceFrag`, so it accepts W2 splices
  (see `MiniRustSpec.PtrByteCoherenceMR`).
* **W3–W5** (32-bit `layoutPointerBytes = 4` vs. an 8-byte constant, `body.globals` relocations,
  wide-pointer bytewise copies, multi-variant enums, union `.ref` / `.fnPtr` punning, cross-frame
  foreign copies, `evalCopyMemory`): the suites fixed a 64-bit target and never instantiated the
  pointer width, never related global relocations or wide-pointer halves at byte level, and their
  union / copy theorems carried only integer payloads.
* **`Kani#5205`**: validity was related only at typed writes; no theorem wrote an invalid bit
  pattern through an untyped place (`[u8; 1]`, `MaybeUninit<bool>`, `Unaligned<bool>`) and then
  read it at the typed `bool` / `char`, which is where `Trusted` must fault.

What now prevents regression: `readPtr8_allBytes_{runtime,ctfe}_corr` and their 4-byte twins fix
`Trusted`'s coherence verdict to the unmodified vendored fragment rule for **every** 4- and 8-byte
stream (fragmented, plain, or uninit); `clear_partial_mid_strips_{8,4}` and
`prepareCopy_applyCopy_{intact_8,splice_p_p256}` verify unmodified vendored `clear`, `prepareCopy`,
and `applyCopy` directly via `mem_qsort`; `normOffset_image_inj` pins `origOffset` normalization to
the vendored byte image; `intact_roundtrip_{8,4}` / `rawCarrier_ptr_roundtrip_{8,4}` /
`w_lm_wide_*` pin thin, carrier, and wide round-trips; `kani5205_{bool,char}_validity_iff` and
`w_lm_kani5205_{e2e,alloc_e2e}` pin read-time validity universally and end-to-end;
`lm_lockstep_parity` pins `V2026_06_01 ↔ V2026_08_01`. Remaining scoped boundaries: `&dyn` vtable
allocation identity (no vtable table in the `Trusted` IR / `Memory`), the `VariantsShape.multiple`
per-variant `TypeLayout` schema, and the `Ptr2IntTransmutePolicy.strictUcg630Ub` write-time
pointer-to-integer pin.

This module imports no `MiniRustSpec.*` or `Anneal.*` module (verified by
`#assert_ptr_byte_coherence_lm_audit`).
-/

set_option Elab.async false

namespace LeanMiriSpec.PtrByteCoherenceLM

open Miri.ABI Miri.Memory

/-! ## Part 0. Vendored-`ProvenanceMap` evaluation tactics and version-independent laws -/

section Tactics
open Lean Elab Tactic Meta

/-- `delta_miri_private M [D₁, …]` delta-unfolds, in the goal, the declarations `Dᵢ` that the
vendored module `M` declares `private` (name resolution only: no axioms, no new definitions). -/
elab "delta_miri_private " mod:ident "[" decls:ident,* "]" : tactic => do
  for decl in decls.getElems do
    let n := Lean.mkPrivateNameCore mod.getId.eraseMacroScopes decl.getId.eraseMacroScopes
    unless (← getEnv).contains n do
      throwError "delta_miri_private: unknown private declaration {decl.getId} of {mod.getId}"
    let goal ← getMainGoal
    try
      let goal' ← goal.deltaTarget (· == n)
      replaceMainGoal [goal']
    catch _ => pure ()

/-- `simp_miri_private M D` rewrites with the equation lemmas of the declaration `D` that the
vendored module `M` declares `private`. -/
elab "simp_miri_private " mod:ident decl:ident : tactic => do
  let n := Lean.mkPrivateNameCore mod.getId.eraseMacroScopes decl.getId.eraseMacroScopes
  unless (← getEnv).contains n do
    throwError "simp_miri_private: unknown private declaration {decl.getId} of {mod.getId}"
  evalTactic (← `(tactic| simp only [$(mkCIdent n):ident]))

/-- Reference a private helper in `Init.Data.Array.QSort.Basic` (for `Array.qsort` membership
invariance proofs; name resolution only, zero new axioms or definitions). -/
elab "qsort_priv% " decl:ident : term => do
  let n := Lean.mkPrivateNameCore `Init.Data.Array.QSort.Basic decl.getId.eraseMacroScopes
  unless (← getEnv).contains n do
    throwError "qsort_priv%: unknown private declaration {decl.getId}"
  Term.elabTerm (← `(@$(mkCIdent n))) none

/-- Rewrite using the defining equation of a private helper in `Init.Data.Array.QSort.Basic`. -/
elab "unfold_qsort_priv " decl:ident : tactic => do
  let n := Lean.mkPrivateNameCore `Init.Data.Array.QSort.Basic decl.getId.eraseMacroScopes
  unless (← getEnv).contains n do
    throwError "unfold_qsort_priv: unknown private declaration {decl.getId}"
  evalTactic (← `(tactic| rw [$(mkCIdent n):ident]))

end Tactics

set_option linter.unusedSimpArgs false

theorem nat_beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  constructor
  · exact Nat.eq_of_beq_eq_true
  · intro h
    subst h
    induction a with
    | zero => rfl
    | succ n ih => exact ih

theorem u8_ofNat_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.toNat_ofNat']

theorem pow256_pos : ∀ n : Nat, 0 < 256 ^ n
  | 0 => by decide
  | n + 1 => by
      rw [Nat.pow_succ]
      exact Nat.mul_pos (pow256_pos n) (by decide)

/-- The zero-padded little-endian 8-byte image `PointerFrag.bytes` of a `pb`-byte pointer whose
address bytes are those of `o` — exactly the vector that vendored `ptrFragments` builds from the
`pb` data bytes of a pointer (`bytes[k] = data[k]` for `k < pb`, `0` otherwise). -/
def ptrImage (pb o : Nat) : Vector UInt8 8 :=
  Vector.ofFn fun k => if k.val < pb then UInt8.ofNat (o / 256 ^ k.val) else 0

theorem digits_mod_eq :
    ∀ (pb o o' : Nat), (∀ k, k < pb → o / 256 ^ k % 256 = o' / 256 ^ k % 256) →
      o % 256 ^ pb = o' % 256 ^ pb
  | 0, o, o', _ => by
      rw [Nat.pow_zero, Nat.mod_one, Nat.mod_one]
  | pb + 1, o, o', h => by
      rw [Nat.pow_succ, Nat.mod_mul, Nat.mod_mul,
        digits_mod_eq pb o o' (fun k hk => h k (by omega)), h pb (by omega)]

/-- **Byte-vector injectivity.** Two offsets below `256 ^ pb` (`pb ≤ 8`) have the same
zero-padded 8-byte image iff they are equal. -/
theorem ptrImage_inj (pb o o' : Nat) (hpb : pb ≤ 8) (ho : o < 256 ^ pb) (ho' : o' < 256 ^ pb) :
    ptrImage pb o = ptrImage pb o' ↔ o = o' := by
  constructor
  · intro h
    have hk : ∀ k, k < pb → o / 256 ^ k % 256 = o' / 256 ^ k % 256 := by
      intro k hk
      have h1 := congrArg (fun v : Vector UInt8 8 => v[k]'(by omega)) h
      simp only [ptrImage, Vector.getElem_ofFn, hk, ↓reduceIte] at h1
      have h2 := congrArg UInt8.toNat h1
      rw [u8_ofNat_toNat, u8_ofNat_toNat] at h2
      exact h2
    have := digits_mod_eq pb o o' hk
    rwa [Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt ho'] at this
  · intro h
    rw [h]

theorem fromParts_fields {Prov : Type} (ptrs : Array (Size × Prov))
    (frags : Option (Array (Size × PointerFrag Prov))) (pm : ProvenanceMap Prov)
    (h : ProvenanceMap.fromParts ptrs frags = .ok pm) :
    pm.ptrs = ptrs ∧ pm.byteFragments = frags := by
  unfold ProvenanceMap.fromParts at h
  split at h
  · injection h with h
    subst h
    exact ⟨rfl, rfl⟩
  · cases h

/-- Miri's in-order fragment agreement (`inspect_fragments` without wildcards): fragment `i` has
index `i`, and the provenance and pointer image of fragment `0`. -/
def miriCohAux {Prov : Type} [DecidableEq Prov] (p : Prov) (v : Vector UInt8 8) :
    Nat → List (PointerFrag Prov) → Bool
  | _, [] => true
  | idx, g :: rest =>
    g.idx.toNat == idx && (g.prov == p && (g.bytes == v && miriCohAux p v (idx + 1) rest))

/-- Miri's in-order fragment agreement on a non-empty fragment list. -/
def miriCoh {Prov : Type} [DecidableEq Prov] : List (PointerFrag Prov) → Bool
  | [] => false
  | g :: rest => g.idx.toNat == 0 && miriCohAux g.prov g.bytes 1 rest

/-- Read a pointer of `n` bytes at `off` from the vendored provenance map whose byte-fragment
state is `entries` (`ProvenanceMap.fromParts #[] (some entries)`, then `ProvenanceMap.readPtr`). -/
def trRead {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (entries : Array (Size × PointerFrag Prov)) (off n : UInt64) :
    Except ProvenanceMapError (Option Prov) :=
  match ProvenanceMap.fromParts #[] (some entries) with
  | .ok pm => pm.readPtr (Size.ofBytes off) (Size.ofBytes n)
  | .error e => .error e

/-- Read a pointer from the vendored provenance map whose whole-pointer state is `ptrs`. -/
def ptrsRead {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (ptrs : Array (Size × Prov)) (off n : UInt64) : Except ProvenanceMapError (Option Prov) :=
  match ProvenanceMap.fromPresortedPtrs ptrs with
  | .ok pm => pm.readPtr (Size.ofBytes off) (Size.ofBytes n)
  | .error e => .error e

/-- Overwrite `[start, start + size)` of the whole-pointer state `ptrs` with vendored
`ProvenanceMap.clear` (pointer size `ps`, data bytes `data`), then read a pointer. -/
def clearRead {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (ptrs : Array (Size × Prov)) (start size : UInt64) (data : Array UInt8) (ps off n : UInt64) :
    Except ProvenanceMapError (Option Prov) :=
  match ProvenanceMap.fromPresortedPtrs ptrs with
  | .error e => .error e
  | .ok pm =>
    match ProvenanceMap.clear ⟨Size.ofBytes start, Size.ofBytes size⟩ data (Size.ofBytes ps) pm with
    | .ok () pm' => pm'.readPtr (Size.ofBytes off) (Size.ofBytes n)
    | .error e _ => .error e

/-- Miri runtime provenance (`Miri.Memory.Provenance.concrete`) of a `Trusted` `(allocId, tag)`
pair: allocation `allocId + 1`, borrow tag `tag + 1` (both nonzero below `2 ^ 64 - 1`). -/
def pvRt (a t : Nat) : Provenance :=
  if ha : UInt64.ofNat (a + 1) = 0 then .wildcard
  else if ht : UInt64.ofNat (t + 1) = 0 then .wildcard
  else .concrete ⟨UInt64.ofNat (a + 1), ha⟩ ⟨UInt64.ofNat (t + 1), ht⟩

/-- CTFE provenance (`AllocId`, `offsetIsAddr = false`, no wildcard) of a `Trusted` pair. CTFE
provenance carries no borrow tag. -/
def pvCt (a _t : Nat) : AllocId :=
  if ha : UInt64.ofNat (a + 1) = 0 then ⟨1, by decide⟩ else ⟨UInt64.ofNat (a + 1), ha⟩


/-- The `4`-entry fragment state with one fragment per byte offset `0 .. 3`. -/
def fe4 {Prov : Type} (g0 g1 g2 g3 : PointerFrag Prov) : Array (Size × PointerFrag Prov) :=
  #[(Size.ofBytes 0, g0), (Size.ofBytes 1, g1), (Size.ofBytes 2, g2), (Size.ofBytes 3, g3)]

theorem fromParts_fe4 {Prov : Type} (g0 g1 g2 g3 : PointerFrag Prov) :
    ∃ pm, ProvenanceMap.fromParts #[] (some (fe4 g0 g1 g2 g3)) = .ok pm := by
  unfold ProvenanceMap.fromParts
  simp only [fe4, List.toList_toArray, Option.map, Option.getD]
  simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
  simp [Size.ofBytes]


set_option maxHeartbeats 8000000 in
/-- **Vendored `readPtr` on `4` symbolic fragments, runtime mode** (`offsetIsAddr = true`, no
wildcard fragment): the read retains the provenance of fragment `0` iff the fragments agree in
order (`miriCoh`), and otherwise returns no provenance. -/
theorem readPtr4_runtime {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (g0 g1 g2 g3 : PointerFrag Prov)
    (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (hw0 : ¬ some g0.prov = PointerProvenance.wildcard (Prov := Prov)) (hw1 : ¬ some g1.prov = PointerProvenance.wildcard (Prov := Prov)) (hw2 : ¬ some g2.prov = PointerProvenance.wildcard (Prov := Prov)) (hw3 : ¬ some g3.prov = PointerProvenance.wildcard (Prov := Prov)) :
    trRead (fe4 g0 g1 g2 g3) 0 4 =
      .ok (if miriCoh [g0, g1, g2, g3] then some g0.prov else none) := by
  obtain ⟨pm, hpm⟩ := fromParts_fe4 g0 g1 g2 g3
  obtain ⟨hp, hf⟩ := fromParts_fields _ _ pm hpm
  unfold trRead
  rw [hpm]
  dsimp only
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp, hf]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp [fe4, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes,
    Except.mapError, bind, Except.bind, pure, Except.pure, List.range', hw0, hw1, hw2, hw3, hoff,
    miriCoh, miriCohAux]
  by_cases h0 : g0.idx.toNat = 0
  case neg => simp [h0]
  by_cases h1 : g1.idx.toNat = 1
  case neg => simp [h0, h1]
  by_cases p1 : g1.prov = g0.prov
  case neg => simp [h0, h1, p1]
  by_cases b1 : g1.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1]
  by_cases h2 : g2.idx.toNat = 2
  case neg => simp [h0, h1, p1, b1, h2]
  by_cases p2 : g2.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2]
  by_cases b2 : g2.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2]
  by_cases h3 : g3.idx.toNat = 3
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3]
  by_cases p3 : g3.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3]
  by_cases b3 : g3.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3]
  simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3]

set_option maxHeartbeats 8000000 in
/-- **Vendored `readPtr` on `4` symbolic fragments, CTFE mode** (`offsetIsAddr = false`): an
in-order read retains the provenance of fragment `0`; every other read is the partial-pointer
error `readPartialPointer 0`. -/
theorem readPtr4_ctfe {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (g0 g1 g2 g3 : PointerFrag Prov)
    (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (hw0 : ¬ some g0.prov = PointerProvenance.wildcard (Prov := Prov)) (hw1 : ¬ some g1.prov = PointerProvenance.wildcard (Prov := Prov)) (hw2 : ¬ some g2.prov = PointerProvenance.wildcard (Prov := Prov)) (hw3 : ¬ some g3.prov = PointerProvenance.wildcard (Prov := Prov)) :
    trRead (fe4 g0 g1 g2 g3) 0 4 =
      (if miriCoh [g0, g1, g2, g3] then .ok (some g0.prov)
       else .error (.readPartialPointer (Size.ofBytes 0))) := by
  obtain ⟨pm, hpm⟩ := fromParts_fe4 g0 g1 g2 g3
  obtain ⟨hp, hf⟩ := fromParts_fields _ _ pm hpm
  unfold trRead
  rw [hpm]
  dsimp only
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp, hf]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp [fe4, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes,
    Except.mapError, bind, Except.bind, pure, Except.pure, List.range', hw0, hw1, hw2, hw3, hoff,
    miriCoh, miriCohAux, throw, throwThe, MonadExceptOf.throw]
  by_cases h0 : g0.idx.toNat = 0
  case neg => simp [h0]
  by_cases h1 : g1.idx.toNat = 1
  case neg => simp [h0, h1]
  by_cases p1 : g1.prov = g0.prov
  case neg => simp [h0, h1, p1]
  by_cases b1 : g1.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1]
  by_cases h2 : g2.idx.toNat = 2
  case neg => simp [h0, h1, p1, b1, h2]
  by_cases p2 : g2.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2]
  by_cases b2 : g2.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2]
  by_cases h3 : g3.idx.toNat = 3
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3]
  by_cases p3 : g3.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3]
  by_cases b3 : g3.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3]
  simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3]


/-- The `8`-entry fragment state with one fragment per byte offset `0 .. 7`. -/
def fe8 {Prov : Type} (g0 g1 g2 g3 g4 g5 g6 g7 : PointerFrag Prov) : Array (Size × PointerFrag Prov) :=
  #[(Size.ofBytes 0, g0), (Size.ofBytes 1, g1), (Size.ofBytes 2, g2), (Size.ofBytes 3, g3), (Size.ofBytes 4, g4), (Size.ofBytes 5, g5), (Size.ofBytes 6, g6), (Size.ofBytes 7, g7)]

theorem fromParts_fe8 {Prov : Type} (g0 g1 g2 g3 g4 g5 g6 g7 : PointerFrag Prov) :
    ∃ pm, ProvenanceMap.fromParts #[] (some (fe8 g0 g1 g2 g3 g4 g5 g6 g7)) = .ok pm := by
  unfold ProvenanceMap.fromParts
  simp only [fe8, List.toList_toArray, Option.map, Option.getD]
  simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
  simp [Size.ofBytes]


set_option maxHeartbeats 8000000 in
/-- **Vendored `readPtr` on `8` symbolic fragments, runtime mode** (`offsetIsAddr = true`, no
wildcard fragment): the read retains the provenance of fragment `0` iff the fragments agree in
order (`miriCoh`), and otherwise returns no provenance. -/
theorem readPtr8_runtime {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (g0 g1 g2 g3 g4 g5 g6 g7 : PointerFrag Prov)
    (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (hw0 : ¬ some g0.prov = PointerProvenance.wildcard (Prov := Prov)) (hw1 : ¬ some g1.prov = PointerProvenance.wildcard (Prov := Prov)) (hw2 : ¬ some g2.prov = PointerProvenance.wildcard (Prov := Prov)) (hw3 : ¬ some g3.prov = PointerProvenance.wildcard (Prov := Prov)) (hw4 : ¬ some g4.prov = PointerProvenance.wildcard (Prov := Prov)) (hw5 : ¬ some g5.prov = PointerProvenance.wildcard (Prov := Prov)) (hw6 : ¬ some g6.prov = PointerProvenance.wildcard (Prov := Prov)) (hw7 : ¬ some g7.prov = PointerProvenance.wildcard (Prov := Prov)) :
    trRead (fe8 g0 g1 g2 g3 g4 g5 g6 g7) 0 8 =
      .ok (if miriCoh [g0, g1, g2, g3, g4, g5, g6, g7] then some g0.prov else none) := by
  obtain ⟨pm, hpm⟩ := fromParts_fe8 g0 g1 g2 g3 g4 g5 g6 g7
  obtain ⟨hp, hf⟩ := fromParts_fields _ _ pm hpm
  unfold trRead
  rw [hpm]
  dsimp only
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp, hf]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp [fe8, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes,
    Except.mapError, bind, Except.bind, pure, Except.pure, List.range', hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hoff,
    miriCoh, miriCohAux]
  by_cases h0 : g0.idx.toNat = 0
  case neg => simp [h0]
  by_cases h1 : g1.idx.toNat = 1
  case neg => simp [h0, h1]
  by_cases p1 : g1.prov = g0.prov
  case neg => simp [h0, h1, p1]
  by_cases b1 : g1.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1]
  by_cases h2 : g2.idx.toNat = 2
  case neg => simp [h0, h1, p1, b1, h2]
  by_cases p2 : g2.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2]
  by_cases b2 : g2.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2]
  by_cases h3 : g3.idx.toNat = 3
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3]
  by_cases p3 : g3.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3]
  by_cases b3 : g3.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3]
  by_cases h4 : g4.idx.toNat = 4
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4]
  by_cases p4 : g4.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4]
  by_cases b4 : g4.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4]
  by_cases h5 : g5.idx.toNat = 5
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5]
  by_cases p5 : g5.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5]
  by_cases b5 : g5.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5]
  by_cases h6 : g6.idx.toNat = 6
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6]
  by_cases p6 : g6.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6]
  by_cases b6 : g6.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6]
  by_cases h7 : g7.idx.toNat = 7
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7]
  by_cases p7 : g7.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7, p7]
  by_cases b7 : g7.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7, p7, b7]
  simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7, p7, b7]

set_option maxHeartbeats 8000000 in
/-- **Vendored `readPtr` on `8` symbolic fragments, CTFE mode** (`offsetIsAddr = false`): an
in-order read retains the provenance of fragment `0`; every other read is the partial-pointer
error `readPartialPointer 0`. -/
theorem readPtr8_ctfe {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (g0 g1 g2 g3 g4 g5 g6 g7 : PointerFrag Prov)
    (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (hw0 : ¬ some g0.prov = PointerProvenance.wildcard (Prov := Prov)) (hw1 : ¬ some g1.prov = PointerProvenance.wildcard (Prov := Prov)) (hw2 : ¬ some g2.prov = PointerProvenance.wildcard (Prov := Prov)) (hw3 : ¬ some g3.prov = PointerProvenance.wildcard (Prov := Prov)) (hw4 : ¬ some g4.prov = PointerProvenance.wildcard (Prov := Prov)) (hw5 : ¬ some g5.prov = PointerProvenance.wildcard (Prov := Prov)) (hw6 : ¬ some g6.prov = PointerProvenance.wildcard (Prov := Prov)) (hw7 : ¬ some g7.prov = PointerProvenance.wildcard (Prov := Prov)) :
    trRead (fe8 g0 g1 g2 g3 g4 g5 g6 g7) 0 8 =
      (if miriCoh [g0, g1, g2, g3, g4, g5, g6, g7] then .ok (some g0.prov)
       else .error (.readPartialPointer (Size.ofBytes 0))) := by
  obtain ⟨pm, hpm⟩ := fromParts_fe8 g0 g1 g2 g3 g4 g5 g6 g7
  obtain ⟨hp, hf⟩ := fromParts_fields _ _ pm hpm
  unfold trRead
  rw [hpm]
  dsimp only
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp, hf]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp [fe8, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes,
    Except.mapError, bind, Except.bind, pure, Except.pure, List.range', hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hoff,
    miriCoh, miriCohAux, throw, throwThe, MonadExceptOf.throw]
  by_cases h0 : g0.idx.toNat = 0
  case neg => simp [h0]
  by_cases h1 : g1.idx.toNat = 1
  case neg => simp [h0, h1]
  by_cases p1 : g1.prov = g0.prov
  case neg => simp [h0, h1, p1]
  by_cases b1 : g1.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1]
  by_cases h2 : g2.idx.toNat = 2
  case neg => simp [h0, h1, p1, b1, h2]
  by_cases p2 : g2.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2]
  by_cases b2 : g2.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2]
  by_cases h3 : g3.idx.toNat = 3
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3]
  by_cases p3 : g3.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3]
  by_cases b3 : g3.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3]
  by_cases h4 : g4.idx.toNat = 4
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4]
  by_cases p4 : g4.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4]
  by_cases b4 : g4.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4]
  by_cases h5 : g5.idx.toNat = 5
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5]
  by_cases p5 : g5.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5]
  by_cases b5 : g5.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5]
  by_cases h6 : g6.idx.toNat = 6
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6]
  by_cases p6 : g6.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6]
  by_cases b6 : g6.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6]
  by_cases h7 : g7.idx.toNat = 7
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7]
  by_cases p7 : g7.prov = g0.prov
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7, p7]
  by_cases b7 : g7.bytes = g0.bytes
  case neg => simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7, p7, b7]
  simp [h0, h1, p1, b1, h2, p2, b2, h3, p3, b3, h4, p4, b4, h5, p5, b5, h6, p6, b6, h7, p7, b7]


/-- Open a vendored `readPtr` on a concrete state: unfold `readPtr`, the `private`
`inspectFragments`, and the range / byte lookups. -/
macro "lm_open" : tactic => `(tactic| (
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte]))

/-- Close an opened vendored `readPtr` on a concrete state by evaluation. -/
macro "lm_close" : tactic => `(tactic| (
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end,
    Size.add, Size.ofBytes, Except.mapError, bind, Except.bind, pure, Except.pure, List.range',
    pvRt, pvCt, ptrImage, PointerProvenance.wildcard, PointerProvenance.offsetIsAddr, throw,
    throwThe, MonadExceptOf.throw]))

/-- Build the concrete fragment state of `trRead`. -/
macro "lm_trread" : tactic => `(tactic| (
  unfold trRead ProvenanceMap.fromParts
  simp only [List.toList_toArray, Option.map, Option.getD]
  simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
  simp [Size.ofBytes]))

/-- Build the concrete whole-pointer state of `ptrsRead`. -/
macro "lm_ptrsread" : tactic => `(tactic| (
  unfold ptrsRead ProvenanceMap.fromPresortedPtrs
  simp only [List.toList_toArray]
  simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
  simp [Size.ofBytes]))

/-- `p = alloc 7 + 0x1000` with byte 1 plain (or uninitialized): the translated fragment state
(offsets `0, 2 .. 7`; shared by both dialects, see `w_lm_missing_and_uninit`). -/
def entriesMissing1 {Prov : Type} (pv : Nat → Nat → Prov) : Array (Size × PointerFrag Prov) :=
  #[(Size.ofBytes 0, ⟨0, pv 7 7, ptrImage 8 4096⟩), (Size.ofBytes 2, ⟨2, pv 7 7, ptrImage 8 4096⟩), (Size.ofBytes 3, ⟨3, pv 7 7, ptrImage 8 4096⟩), (Size.ofBytes 4, ⟨4, pv 7 7, ptrImage 8 4096⟩), (Size.ofBytes 5, ⟨5, pv 7 7, ptrImage 8 4096⟩), (Size.ofBytes 6, ⟨6, pv 7 7, ptrImage 8 4096⟩), (Size.ofBytes 7, ⟨7, pv 7 7, ptrImage 8 4096⟩)]

/-- Vendored `readPtr` on `entriesMissing1` (Miri runtime provenance): no provenance. -/
theorem w_lm_missing_miri_rt : trRead (entriesMissing1 pvRt) 0 8 = .ok none := by
  unfold entriesMissing1
  lm_trread
  lm_open
  lm_close

/-- Vendored `readPtr` on `entriesMissing1` (CTFE provenance): the partial-pointer error. -/
theorem w_lm_missing_miri_ct :
    trRead (entriesMissing1 pvCt) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) := by
  unfold entriesMissing1
  lm_trread
  lm_open
  lm_close

/-- **Misaligned cross-relocation reads and 32-bit non-bleed.** Two whole-pointer entries
`[p, p]` at offsets `0` and `8`: an aligned read at `8` returns `p`; reads at offsets `1` and `4`
straddle two entries and return no provenance (runtime) / the partial-pointer error (CTFE). Two
adjacent 32-bit entries at `0` and `4`: an aligned 4-byte read returns the first pointer, and a
read at `2` does not bleed provenance from either neighbour. -/
theorem w_lm_misaligned :
    ptrsRead #[(Size.ofBytes 0, pvRt 7 7), (Size.ofBytes 8, pvRt 7 7)] 8 8 = .ok (some (pvRt 7 7)) ∧
    ptrsRead #[(Size.ofBytes 0, pvRt 7 7), (Size.ofBytes 8, pvRt 7 7)] 1 8 = .ok none ∧
    ptrsRead #[(Size.ofBytes 0, pvRt 7 7), (Size.ofBytes 8, pvRt 7 7)] 4 8 = .ok none ∧
    ptrsRead #[(Size.ofBytes 0, pvCt 7 7), (Size.ofBytes 8, pvCt 7 7)] 4 8 =
      .error (.readPartialPointer (Size.ofBytes 4)) ∧
    ptrsRead #[(Size.ofBytes 0, pvRt 9 9), (Size.ofBytes 4, pvRt 9 9)] 0 4 = .ok (some (pvRt 9 9)) ∧
    ptrsRead #[(Size.ofBytes 0, pvRt 9 9), (Size.ofBytes 4, pvRt 9 9)] 2 4 = .ok none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (lm_ptrsread; lm_open; lm_close)

/-- Fragment state with a wildcard fragment at offset `0`, the bytes `1 .. 3` of the pointer with
image `img₁`, and the bytes `4 .. 7` of the pointer with image `img₂` (Miri runtime provenance). -/
def wildEntries (img₁ img₂ : Nat) : Array (Size × PointerFrag Provenance) :=
  #[(Size.ofBytes 0, ⟨0, .wildcard, ptrImage 8 img₁⟩), (Size.ofBytes 1, ⟨1, pvRt 7 7, ptrImage 8 img₁⟩),
    (Size.ofBytes 2, ⟨2, pvRt 7 7, ptrImage 8 img₁⟩), (Size.ofBytes 3, ⟨3, pvRt 7 7, ptrImage 8 img₁⟩),
    (Size.ofBytes 4, ⟨4, pvRt 7 7, ptrImage 8 img₂⟩), (Size.ofBytes 5, ⟨5, pvRt 7 7, ptrImage 8 img₂⟩),
    (Size.ofBytes 6, ⟨6, pvRt 7 7, ptrImage 8 img₂⟩), (Size.ofBytes 7, ⟨7, pvRt 7 7, ptrImage 8 img₂⟩)]

/-- **Wildcard provenance (`DIV-LM-WILDCARD`).** Vendored `inspectFragments` skips a wildcard
fragment, so a wildcard byte next to seven coherent bytes of `p` reads `p`'s provenance; a
wildcard does **not** rescue the `p` / `p + 4` offset splice. -/
theorem w_lm_wildcard :
    trRead (wildEntries 0x1000 0x1000) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (wildEntries 0x1000 0x1004) 0 8 = .ok none := by
  constructor <;> (unfold wildEntries; lm_trread; lm_open; lm_close)

/-- **Postmortem (W1): the whole-pointer path.** The pre-Episode-1 correspondence exercised only
whole-pointer `ProvenanceMap.ptrs` entries, which vendored `readPtr` answers by `getPtr` without
consulting fragments; the fragment path (`inspectFragments`) is where permuted byte images are
rejected (`w_lm_reversal`). -/
theorem pm_w1_whole_pointer_path_only :
    ptrsRead #[(Size.ofBytes 0, pvRt 7 7)] 0 8 = .ok (some (pvRt 7 7)) ∧
    ptrsRead #[(Size.ofBytes 0, pvCt 7 7)] 0 8 = .ok (some (pvCt 7 7)) := by
  constructor <;> (lm_ptrsread; lm_open; lm_close)

/-- **`Kani#5205` (vendored Miri half).** Vendored `Validity.checkPrimitive` rejects the byte `2`
at `bool` (`invalidBool 2`) and the surrogate `0xD800` at `char` (`invalidChar 0xD800`), accepts
`1` at `bool`, and accepts `2` at an integer scalar. -/
theorem w_lm_kani5205_miri :
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 2))
      (fun _ s => .ok false s) () = .error (.failure (.invalidBool 2)) () ∧
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 1))
      (fun _ s => .ok false s) () = .ok .valid () ∧
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800))
      (fun _ s => .ok false s) () = .error (.failure (.invalidChar 0xD800)) () ∧
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .scalar ⟨Size.ofBytes 1, ⟨0, 255⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 2))
      (fun _ s => .ok false s) () = .ok .valid () :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Part 0b. `Array.qsort` membership invariance, vendored `ProvenanceMap.{clear,prepareCopy,applyCopy}`, `pvRt` injectivity, missing-byte `readPtr`, `DIV-LM-CTFE-TAG`, and universal `Validity.checkPrimitive` -/

theorem vec_mem_swap {α : Type} {n : Nat} (v : Vector α n) (i j : Nat)
    (hi : i < n) (hj : j < n) (x : α) :
    x ∈ (v.swap i j hi hj).toArray ↔ x ∈ v.toArray := by
  have hiff : ∀ (w : Vector α n), x ∈ w.toArray ↔ ∃ k, ∃ (hk : k < n), w[k] = x := by
    intro w
    rw [Array.mem_iff_getElem]
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, by simpa using hk, by simpa using h⟩,
           fun ⟨k, hk, h⟩ => ⟨k, by simpa using hk, by simpa using h⟩⟩
  rw [hiff, hiff]
  constructor
  · rintro ⟨k, hk, heq⟩
    rw [Vector.getElem_swap] at heq
    split at heq
    · exact ⟨j, hj, heq⟩
    · split at heq
      · exact ⟨i, hi, heq⟩
      · exact ⟨k, hk, heq⟩
  · rintro ⟨k, hk, heq⟩
    by_cases hki : k = i
    · subst hki
      refine ⟨j, hj, ?_⟩
      rw [Vector.getElem_swap]
      split
      · rename_i hji; subst hji; exact heq
      · simp [heq]
    · by_cases hkj : k = j
      · subst hkj
        refine ⟨i, hi, ?_⟩
        rw [Vector.getElem_swap]
        simp [heq]
      · refine ⟨k, hk, ?_⟩
        rw [Vector.getElem_swap]
        simp [hki, hkj, heq]

theorem qpartition_loop_mem {α : Type} {n : Nat} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot : α) :
    ∀ (d : Nat) (as : Vector α n) (i k : Nat)
      (ilo : lo ≤ i) (ik : i ≤ k) (wk : k ≤ hi), hi - k ≤ d →
      ∀ x, x ∈ ((qsort_priv% Array.qpartition.loop) lt lo hi hhi pivot as i k ilo ik wk).2.toArray ↔
        x ∈ as.toArray
  | 0, as, i, k, ilo, ik, wk, hd, x => by
    unfold_qsort_priv Array.qpartition.loop
    have hnk : ¬ (k < hi) := by omega
    simp only [hnk, ↓reduceDIte]
    exact vec_mem_swap as i hi (by omega) hhi x
  | d + 1, as, i, k, ilo, ik, wk, hd, x => by
    unfold_qsort_priv Array.qpartition.loop
    by_cases hk : k < hi
    · simp only [hk, ↓reduceDIte]
      split
      · rw [qpartition_loop_mem lt lo hi hhi pivot d (as.swap i k (by omega) (by omega))
              (i + 1) (k + 1) (by omega) (by omega) (by omega) (by omega) x]
        exact vec_mem_swap as i k (by omega) (by omega) x
      · exact qpartition_loop_mem lt lo hi hhi pivot d as i (k + 1) ilo (by omega) (by omega) (by omega) x
    · simp only [hk, ↓reduceDIte]
      exact vec_mem_swap as i hi (by omega) hhi x

theorem qpartition_mem {α : Type} {n : Nat} (as : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (x : α) :
    x ∈ (Array.qpartition as lt lo hi w hlo hhi).2.toArray ↔ x ∈ as.toArray := by
  have hswap : ∀ (v : Vector α n) (c : Bool) (a b : Nat) (ha : a < n) (hb : b < n),
      (x ∈ (if c then v.swap a b ha hb else v).toArray ↔ x ∈ v.toArray) := by
    intro v c a b ha hb
    cases c
    · simp
    · simpa using vec_mem_swap v a b ha hb x
  unfold Array.qpartition
  dsimp only
  rw [qpartition_loop_mem lt lo hi hhi _ (hi - lo) _ _ _ _ _ _ (Nat.le_refl _) x, hswap, hswap, hswap]

theorem qsort_sort_mem {α : Type} {n : Nat} (lt : α → α → Bool) :
    ∀ (d : Nat) (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n),
      hi - lo ≤ d →
      ∀ x, x ∈ ((qsort_priv% Array.qsort.sort) lt as lo hi w hlo hhi).toArray ↔ x ∈ as.toArray
  | 0, as, lo, hi, w, hlo, hhi, hd, x => by
    unfold_qsort_priv Array.qsort.sort
    have hnl : ¬ (lo < hi) := by omega
    simp only [hnl, ↓reduceDIte]
  | d + 1, as, lo, hi, w, hlo, hhi, hd, x => by
    unfold_qsort_priv Array.qsort.sort
    by_cases h1 : lo < hi
    · simp only [h1, ↓reduceDIte]
      have hpart := qpartition_mem as lt lo hi w hlo hhi x
      rcases hp : Array.qpartition as lt lo hi w hlo hhi with ⟨⟨mid, hmid_lo, hmid_hi⟩, as'⟩
      rw [hp] at hpart
      dsimp only at hpart ⊢
      split
      · exact hpart
      · rw [qsort_sort_mem lt d _ (mid + 1) hi (by omega) (by omega) hhi (by omega) x,
            qsort_sort_mem lt d as' lo mid hmid_lo hlo (by omega) (by omega) x]
        exact hpart
    · simp only [h1, ↓reduceDIte]

/-- **Propositional membership invariance of `Array.qsort`.** Sorting any array preserves exact
element membership, enabling kernel-checked evaluation of vendored `ProvenanceMap.clear` and
`ProvenanceMap.applyCopy` without requiring kernel reduction of well-founded `Array.qsort`. -/
theorem mem_qsort {α : Type} (as : Array α) (lt : α → α → Bool) (lo hi : Nat) (x : α) :
    x ∈ as.qsort lt lo hi ↔ x ∈ as := by
  unfold Array.qsort
  split
  · rfl
  · exact qsort_sort_mem lt _ as.toVector _ _ _ _ _ (Nat.le_refl _) x

theorem mem_qsort_push_filter {α : Type} (values : Array (Size × α)) (off : Size) (val : α)
    (lo hi : Nat) (e : Size × α) :
    e ∈ ((values.filter fun entry => entry.1.bytes != off.bytes).push (off, val)).qsort
      (fun left right => decide (left.1.bytes < right.1.bytes)) lo hi ↔
      (e ∈ values ∧ e.1.bytes ≠ off.bytes) ∨ e = (off, val) := by
  rw [mem_qsort, Array.mem_push, Array.mem_filter]
  simp [bne_iff_ne]

local elab "miri_priv% " mod:ident decl:ident : term => do
  let n := Lean.mkPrivateNameCore mod.getId decl.getId
  Lean.Elab.Term.elabTerm (← `(@$(Lean.mkCIdent n))) none

private theorem mem_miri_insertEntry {α : Type} (values : Array (Size × α)) (off : Size)
    (val : α) (e : Size × α) :
    e ∈ (miri_priv% Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.insertEntry) values off val ↔
      (e ∈ values ∧ e.1.bytes ≠ off.bytes) ∨ e = (off, val) := by
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.insertEntry]
  exact mem_qsort_push_filter values off val _ _ e

theorem array_find?_eq_some_of_unique {α : Type} (arr : Array α) (p : α → Bool) (a : α)
    (hmem : a ∈ arr) (hp : p a = true) (huniq : ∀ b ∈ arr, p b = true → b = a) :
    arr.find? p = some a := by
  cases h : arr.find? p with
  | none => exact absurd hp (Array.find?_eq_none.mp h a hmem)
  | some b => rw [huniq b (Array.mem_of_find?_eq_some h) (Array.find?_some h)]

theorem array_filter_isEmpty_false_of_mem {α : Type} (arr : Array α) (p : α → Bool) (a : α)
    (hmem : a ∈ arr) (hp : p a = true) :
    (arr.filter p).isEmpty = false := by
  cases h : (arr.filter p).isEmpty with
  | false => rfl
  | true =>
    have hsz : (arr.filter p).size = 0 := Array.isEmpty_iff_size_eq_zero.mp h
    obtain ⟨i, hi, _⟩ := Array.mem_iff_getElem.mp (Array.mem_filter.mpr ⟨hmem, hp⟩)
    omega

theorem fromPresortedPtrs_fields {Prov : Type} (ptrs : Array (Size × Prov)) (pm : ProvenanceMap Prov)
    (h : ProvenanceMap.fromPresortedPtrs ptrs = .ok pm) :
    pm.ptrs = ptrs ∧ pm.byteFragments = none := by
  unfold ProvenanceMap.fromPresortedPtrs at h
  split at h
  · injection h with h; subst h; exact ⟨rfl, rfl⟩
  · cases h

/-- `pvRt` produces a non-wildcard `Provenance.concrete` whenever `a, t < 2^64 - 1`. -/
theorem pvRt_concrete (a t : Nat) (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    ∃ h1 h2, pvRt a t = .concrete ⟨UInt64.ofNat (a + 1), h1⟩ ⟨UInt64.ofNat (t + 1), h2⟩ := by
  have h1 : UInt64.ofNat (a + 1) ≠ 0 := by
    intro h0
    have := congrArg UInt64.toNat h0
    simp only [UInt64.toNat_ofNat', UInt64.toNat_zero, Nat.mod_eq_of_lt ha] at this
    omega
  have h2 : UInt64.ofNat (t + 1) ≠ 0 := by
    intro h0
    have := congrArg UInt64.toNat h0
    simp only [UInt64.toNat_ofNat', UInt64.toNat_zero, Nat.mod_eq_of_lt ht] at this
    omega
  refine ⟨h1, h2, ?_⟩
  unfold pvRt
  simp only [h1, h2, ↓reduceDIte]

theorem pvRt_ne_wildcard (a t : Nat) (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    ¬ some (pvRt a t) = PointerProvenance.wildcard (Prov := Provenance) := by
  obtain ⟨_, _, heq⟩ := pvRt_concrete a t ha ht
  rw [heq]
  intro h
  cases h

/-- `pvRt` is injective on `(allocId, tag)` for all `< 2^64 - 1`. -/
theorem pvRt_inj (a t a' t' : Nat) (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64)
    (ha' : a' + 1 < 2 ^ 64) (ht' : t' + 1 < 2 ^ 64)
    (h : pvRt a t = pvRt a' t') : a = a' ∧ t = t' := by
  obtain ⟨_, _, h1⟩ := pvRt_concrete a t ha ht
  obtain ⟨_, _, h2⟩ := pvRt_concrete a' t' ha' ht'
  rw [h1, h2] at h
  injection h with hae hte
  have hae' : UInt64.ofNat (a + 1) = UInt64.ofNat (a' + 1) := congrArg AllocId.value hae
  have hte' : UInt64.ofNat (t + 1) = UInt64.ofNat (t' + 1) := congrArg BorTag.value hte
  have hna := congrArg UInt64.toNat hae'
  have hnt := congrArg UInt64.toNat hte'
  simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha',
    Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hna hnt
  omega

/-- **Vendored `ProvenanceMap.clear` mid-pointer partial overwrite (64-bit).**
Overwriting 1 byte at offset `1` of an 8-byte whole-pointer entry at offset `0` splits it into
exact surviving `PointerFrag`s at offsets `0` and `2 .. 7` (`pm'.ptrs = #[]`, `bytes` =
pointer's data bytes), and subsequent unmodified vendored `ProvenanceMap.readPtr 0 8` strips
provenance (`.ok none` in runtime mode, `.error (.readPartialPointer 0)` in CTFE mode). -/
theorem clear_partial_mid_strips_8 {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (prov : Prov) (data : Array UInt8) (hdata : data.size = 8) :
    ∃ pm pm',
      ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok pm ∧
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 1⟩ data (Size.ofBytes 8) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      (∃ frags, pm'.byteFragments = some frags ∧
        (∀ e, e ∈ frags ↔
          ∃ k, k < 8 ∧ k ≠ 1 ∧
            e = (Size.ofBytes (UInt64.ofNat k),
                 ⟨UInt8.ofNat k, prov, Vector.ofFn fun idx =>
                   if hi : idx.val < 8 then data[idx.val]'(by omega) else 0⟩))) ∧
      pm'.readPtr (Size.ofBytes 0) (Size.ofBytes 8) =
        (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
         else .error (.readPartialPointer (Size.ofBytes 0))) := by
  have hex : ∃ pm, ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok pm := by
    unfold ProvenanceMap.fromPresortedPtrs
    simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
    exact ⟨_, rfl⟩
  obtain ⟨pm, hpm⟩ := hex
  obtain ⟨hp, hf⟩ := fromPresortedPtrs_fields _ pm hpm
  have hclear : ∃ pm',
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 1⟩ data (Size.ofBytes 8) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      (∃ frags, pm'.byteFragments = some frags ∧
        (∀ e, e ∈ frags ↔
          ∃ k, k < 8 ∧ k ≠ 1 ∧
            e = (Size.ofBytes (UInt64.ofNat k),
                 ⟨UInt8.ofNat k, prov, Vector.ofFn fun idx =>
                   if hi : idx.val < 8 then data[idx.val]'(by omega) else 0⟩))) := by
    unfold ProvenanceMap.clear
    simp only [ProvenanceMap.rangePtrs]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.adjustedStart,
      Miri.Memory.ProvenanceMap.rangeEntries, Miri.Memory.ProvenanceMap.removeEntries,
      Miri.Memory.ProvenanceMap.ptrFragments]
    simp (config := { decide := true }) [hp, hf, AllocRange.endExclusive,
      AllocRange.end, Size.add, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, EStateM.bind, EStateM.get, EStateM.set, hdata,
      List.range', List.forIn_cons, List.forIn_nil]
    intro s f
    simp only [Array.foldl_push, Array.foldl_empty, Option.getD_some, Option.getD_none,
      mem_miri_insertEntry, Array.not_mem_empty, false_and, false_or]
    constructor
    · intro h
      rcases h with ⟨⟨⟨⟨⟨⟨h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h
      · exact ⟨0, by decide, by decide, by simpa using h⟩
      · exact ⟨2, by decide, by decide, by simpa using h⟩
      · exact ⟨3, by decide, by decide, by simpa using h⟩
      · exact ⟨4, by decide, by decide, by simpa using h⟩
      · exact ⟨5, by decide, by decide, by simpa using h⟩
      · exact ⟨6, by decide, by decide, by simpa using h⟩
      · exact ⟨7, by decide, by decide, by simpa using h⟩
    · rintro ⟨k, hk, hne, hs, hf'⟩
      subst hs hf'
      have : k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true })
  obtain ⟨pm', hcl, hptrs', frags, hfrags, hmem⟩ := hclear
  refine ⟨pm, pm', hpm, hcl, hptrs', ⟨frags, hfrags, hmem⟩, ?_⟩
  let vec : Vector UInt8 8 := Vector.ofFn fun idx => if hi : idx.val < 8 then data[idx.val]'(by omega) else 0
  have hmem0 : (Size.ofBytes 0, ⟨0, prov, vec⟩) ∈ frags :=
    (hmem _).mpr ⟨0, by decide, by decide, rfl⟩
  have hnonempty : (frags.filter fun entry => decide (entry.1.bytes < 8)).isEmpty = false :=
    array_filter_isEmpty_false_of_mem frags _ (Size.ofBytes 0, ⟨0, prov, vec⟩) hmem0 rfl
  have hfind0 : frags.find? (fun entry => entry.1.bytes == 0) = some (Size.ofBytes 0, ⟨0, prov, vec⟩) := by
    refine array_find?_eq_some_of_unique frags _ _ hmem0 rfl ?_
    intro b hb hbp
    obtain ⟨k, hk, _, rfl⟩ := (hmem b).mp hb
    have hk0 : k = 0 := by
      simp only [Size.ofBytes, beq_iff_eq] at hbp
      have := congrArg UInt64.toNat hbp
      simp [UInt64.toNat_ofNat'] at this
      omega
    subst hk0; rfl
  have hfind1 : frags.find? (fun entry => entry.1.bytes == 1) = none := by
    rw [Array.find?_eq_none]
    intro b hb hbp
    obtain ⟨k, hk, hne1, rfl⟩ := (hmem b).mp hb
    simp only [Size.ofBytes, beq_iff_eq] at hbp
    have := congrArg UInt64.toNat hbp
    simp [UInt64.toNat_ofNat'] at this
    omega
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hptrs', hfrags]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    List.range', throw, throwThe, MonadExceptOf.throw]
  rw [hnonempty, hfind0, hfind1]
  simp only [Option.map_some, Option.map_none]
  by_cases hw : some prov = PointerProvenance.wildcard (Prov := Prov)
  · simp [hw]; cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp
  · simp [hw]; cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp

/-- **Vendored `ProvenanceMap.clear` mid-pointer partial overwrite (32-bit).**
Overwriting 1 byte at offset `1` of a 4-byte whole-pointer entry at offset `0` splits it into
exact surviving `PointerFrag`s at offsets `0, 2, 3`, and subsequent unmodified vendored
`ProvenanceMap.readPtr 0 4` strips provenance in both runtime and CTFE modes. -/
theorem clear_partial_mid_strips_4 {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (prov : Prov) (data : Array UInt8) (hdata : data.size = 4) :
    ∃ pm pm',
      ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok pm ∧
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 1⟩ data (Size.ofBytes 4) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      (∃ frags, pm'.byteFragments = some frags ∧
        (∀ e, e ∈ frags ↔
          ∃ k, k < 4 ∧ k ≠ 1 ∧
            e = (Size.ofBytes (UInt64.ofNat k),
                 ⟨UInt8.ofNat k, prov, Vector.ofFn fun idx =>
                   if hi : idx.val < 4 then data[idx.val]'(by omega) else 0⟩))) ∧
      pm'.readPtr (Size.ofBytes 0) (Size.ofBytes 4) =
        (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
         else .error (.readPartialPointer (Size.ofBytes 0))) := by
  have hex : ∃ pm, ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok pm := by
    unfold ProvenanceMap.fromPresortedPtrs
    simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
    exact ⟨_, rfl⟩
  obtain ⟨pm, hpm⟩ := hex
  obtain ⟨hp, hf⟩ := fromPresortedPtrs_fields _ pm hpm
  have hclear : ∃ pm',
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 1⟩ data (Size.ofBytes 4) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      (∃ frags, pm'.byteFragments = some frags ∧
        (∀ e, e ∈ frags ↔
          ∃ k, k < 4 ∧ k ≠ 1 ∧
            e = (Size.ofBytes (UInt64.ofNat k),
                 ⟨UInt8.ofNat k, prov, Vector.ofFn fun idx =>
                   if hi : idx.val < 4 then data[idx.val]'(by omega) else 0⟩))) := by
    unfold ProvenanceMap.clear
    simp only [ProvenanceMap.rangePtrs]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.adjustedStart,
      Miri.Memory.ProvenanceMap.rangeEntries, Miri.Memory.ProvenanceMap.removeEntries,
      Miri.Memory.ProvenanceMap.ptrFragments]
    simp (config := { decide := true }) [hp, hf, AllocRange.endExclusive,
      AllocRange.end, Size.add, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, EStateM.bind, EStateM.get, EStateM.set, hdata,
      List.range', List.forIn_cons, List.forIn_nil]
    intro s f
    simp only [Array.foldl_push, Array.foldl_empty, Option.getD_some, Option.getD_none,
      mem_miri_insertEntry, Array.not_mem_empty, false_and, false_or]
    constructor
    · intro h
      rcases h with ⟨⟨h, _⟩ | h, _⟩ | h
      · exact ⟨0, by decide, by decide, by simpa using h⟩
      · exact ⟨2, by decide, by decide, by simpa using h⟩
      · exact ⟨3, by decide, by decide, by simpa using h⟩
    · rintro ⟨k, hk, hne, hs, hf'⟩
      subst hs hf'
      have : k = 0 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl <;> simp (config := { decide := true })
  obtain ⟨pm', hcl, hptrs', frags, hfrags, hmem⟩ := hclear
  refine ⟨pm, pm', hpm, hcl, hptrs', ⟨frags, hfrags, hmem⟩, ?_⟩
  let vec : Vector UInt8 8 := Vector.ofFn fun idx => if hi : idx.val < 4 then data[idx.val]'(by omega) else 0
  have hmem0 : (Size.ofBytes 0, ⟨0, prov, vec⟩) ∈ frags :=
    (hmem _).mpr ⟨0, by decide, by decide, rfl⟩
  have hnonempty : (frags.filter fun entry => decide (entry.1.bytes < 4)).isEmpty = false :=
    array_filter_isEmpty_false_of_mem frags _ (Size.ofBytes 0, ⟨0, prov, vec⟩) hmem0 rfl
  have hfind0 : frags.find? (fun entry => entry.1.bytes == 0) = some (Size.ofBytes 0, ⟨0, prov, vec⟩) := by
    refine array_find?_eq_some_of_unique frags _ _ hmem0 rfl ?_
    intro b hb hbp
    obtain ⟨k, hk, _, rfl⟩ := (hmem b).mp hb
    have hk0 : k = 0 := by
      simp only [Size.ofBytes, beq_iff_eq] at hbp
      have := congrArg UInt64.toNat hbp
      simp [UInt64.toNat_ofNat'] at this
      omega
    subst hk0; rfl
  have hfind1 : frags.find? (fun entry => entry.1.bytes == 1) = none := by
    rw [Array.find?_eq_none]
    intro b hb hbp
    obtain ⟨k, hk, hne1, rfl⟩ := (hmem b).mp hb
    simp only [Size.ofBytes, beq_iff_eq] at hbp
    have := congrArg UInt64.toNat hbp
    simp [UInt64.toNat_ofNat'] at this
    omega
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hptrs', hfrags]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    List.range', throw, throwThe, MonadExceptOf.throw]
  rw [hnonempty, hfind0, hfind1]
  simp only [Option.map_some, Option.map_none]
  by_cases hw : some prov = PointerProvenance.wildcard (Prov := Prov)
  · simp [hw]; cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp
  · simp [hw]; cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp

/-- **Direct `clearRead` evaluation via `Miri.Memory.QSortProof.singleton`.** Overwriting bytes
`1 .. 7` of a whole-pointer entry at offset `0` leaves a single fragment at offset `0`, so
`clearRead` reduces directly and strips provenance in both runtime and CTFE modes. -/
theorem clear_partial_7bytes_strips_8 {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (prov : Prov) (data : Array UInt8) (hdata : data.size = 8) :
    clearRead #[(Size.ofBytes 0, prov)] 1 7 data 8 0 8 =
      (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
       else .error (.readPartialPointer (Size.ofBytes 0))) := by
  have hex : ∃ pm, ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok pm := by
    unfold ProvenanceMap.fromPresortedPtrs
    simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
    exact ⟨_, rfl⟩
  obtain ⟨pm, hpm⟩ := hex
  obtain ⟨hp, hf⟩ := fromPresortedPtrs_fields _ pm hpm
  unfold clearRead
  rw [hpm]
  dsimp only
  have hcl : ∃ pm',
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 7⟩ data (Size.ofBytes 8) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      pm'.byteFragments = some #[(Size.ofBytes 0, ⟨0, prov, Vector.ofFn fun idx =>
        if hi : idx.val < 8 then data[idx.val]'(by omega) else 0⟩)] := by
    unfold ProvenanceMap.clear
    simp only [ProvenanceMap.rangePtrs]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.adjustedStart,
      Miri.Memory.ProvenanceMap.rangeEntries, Miri.Memory.ProvenanceMap.removeEntries,
      Miri.Memory.ProvenanceMap.ptrFragments, Miri.Memory.ProvenanceMap.insertEntry]
    simp (config := { decide := true }) [hp, hf, AllocRange.endExclusive,
      AllocRange.end, Size.add, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, EStateM.bind, EStateM.get, EStateM.set, hdata,
      Array.filter_empty, List.range', List.forIn_cons, List.forIn_nil]
    exact Miri.Memory.QSortProof.singleton _ _
  obtain ⟨pm', hcl_eq, hp', hf'⟩ := hcl
  rw [hcl_eq]
  dsimp only
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp', hf']
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    List.range', throw, throwThe, MonadExceptOf.throw]
  by_cases hw : some prov = PointerProvenance.wildcard (Prov := Prov)
  · simp [hw]; cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp
  · simp [hw]; cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp

/-- **Vendored `ProvenanceMap.prepareCopy` + `applyCopy` end-to-end intact bytewise copy (64-bit).**
Splitting a whole-pointer entry `p = 0x1000` into byte `0` and bytes `1 .. 7` via unmodified
vendored `prepareCopy` and copying both slices into a fresh `ProvenanceMap` via unmodified vendored
`applyCopy` yields a fragment map whose vendored `readPtr 0 8` retains `.ok (some prov)` in both
runtime and CTFE modes. -/
theorem prepareCopy_applyCopy_intact_8 {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (prov : Prov) (hnw : ¬ some prov = PointerProvenance.wildcard (Prov := Prov)) :
    let data : Array UInt8 := #[0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    ∃ src c0 c1 dst1 dst2,
      ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok src ∧
      src.prepareCopy ⟨Size.ofBytes 0, Size.ofBytes 1⟩ data (Size.ofBytes 8) = .ok c0 ∧
      src.prepareCopy ⟨Size.ofBytes 1, Size.ofBytes 7⟩ data (Size.ofBytes 8) = .ok c1 ∧
      ProvenanceMap.applyCopy c0 ⟨Size.ofBytes 0, Size.ofBytes 1⟩ 1 ProvenanceMap.new = .ok () dst1 ∧
      ProvenanceMap.applyCopy c1 ⟨Size.ofBytes 1, Size.ofBytes 7⟩ 1 dst1 = .ok () dst2 ∧
      dst2.readPtr (Size.ofBytes 0) (Size.ofBytes 8) = .ok (some prov) := by
  intro data
  have hsrc : ∃ src, ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov)] = .ok src := by
    unfold ProvenanceMap.fromPresortedPtrs
    simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
    exact ⟨_, rfl⟩
  obtain ⟨src, hsrc_eq⟩ := hsrc
  obtain ⟨hsp, hsf⟩ := fromPresortedPtrs_fields _ src hsrc_eq
  let vP : Vector UInt8 8 := #v[0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let c0 : ProvenanceCopy Prov := ⟨#[], #[(Size.ofBytes 0, ⟨0, prov, vP⟩)]⟩
  let c1 : ProvenanceCopy Prov := ⟨#[], #[
    (Size.ofBytes 0, ⟨1, prov, vP⟩), (Size.ofBytes 1, ⟨2, prov, vP⟩),
    (Size.ofBytes 2, ⟨3, prov, vP⟩), (Size.ofBytes 3, ⟨4, prov, vP⟩),
    (Size.ofBytes 4, ⟨5, prov, vP⟩), (Size.ofBytes 5, ⟨6, prov, vP⟩),
    (Size.ofBytes 6, ⟨7, prov, vP⟩)]⟩
  have hc0 : src.prepareCopy ⟨Size.ofBytes 0, Size.ofBytes 1⟩ data (Size.ofBytes 8) = .ok c0 := by
    unfold ProvenanceMap.prepareCopy
    simp only [ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes, hsp, hsf]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.rangeEnd,
      Miri.Memory.ProvenanceMap.adjustedStart, Miri.Memory.ProvenanceMap.rangeEntries,
      Miri.Memory.ProvenanceMap.subtractSize, Miri.Memory.ProvenanceMap.ptrFragments]
    simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end,
      Size.add, Size.sub, Size.ZERO, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, data, c0, vP,
      ← Array.forIn_toList, List.range', List.forIn_cons, List.forIn_nil]
    decide
  have hc1 : src.prepareCopy ⟨Size.ofBytes 1, Size.ofBytes 7⟩ data (Size.ofBytes 8) = .ok c1 := by
    unfold ProvenanceMap.prepareCopy
    simp only [ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes, hsp, hsf]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.rangeEnd,
      Miri.Memory.ProvenanceMap.adjustedStart, Miri.Memory.ProvenanceMap.rangeEntries,
      Miri.Memory.ProvenanceMap.subtractSize, Miri.Memory.ProvenanceMap.ptrFragments]
    simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end,
      Size.add, Size.sub, Size.ZERO, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, data, c1, vP,
      ← Array.forIn_toList, List.range', List.forIn_cons, List.forIn_nil]
    decide
  have happ1 : ∃ dst1,
      ProvenanceMap.applyCopy c0 ⟨Size.ofBytes 0, Size.ofBytes 1⟩ 1 ProvenanceMap.new = .ok () dst1 ∧
      dst1.ptrs = #[] ∧
      ∃ f1, dst1.byteFragments = some f1 ∧ ∀ e, e ∈ f1 ↔ e = (Size.ofBytes 0, ⟨0, prov, vP⟩) := by
    unfold ProvenanceMap.applyCopy
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.shiftedCopyOffset]
    simp (config := { decide := true }) [c0, ProvenanceMap.new, Size.add, Size.mul, Size.ofBytes,
      Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, EStateM.pure, EStateM.bind,
      EStateM.get, EStateM.set, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
      -Array.forIn_toList, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
    intro s f
    simp only [mem_miri_insertEntry, Array.not_mem_empty, false_and, false_or]
    constructor <;> (intro h; simpa using h)
  obtain ⟨dst1, hdst1, hp1, f1, hf1, hm1⟩ := happ1
  have happ2 : ∃ dst2,
      ProvenanceMap.applyCopy c1 ⟨Size.ofBytes 1, Size.ofBytes 7⟩ 1 dst1 = .ok () dst2 ∧
      dst2.ptrs = #[] ∧
      ∃ f2, dst2.byteFragments = some f2 ∧
        (∀ e, e ∈ f2 ↔ ∃ k, k < 8 ∧ e = (Size.ofBytes (UInt64.ofNat k), ⟨UInt8.ofNat k, prov, vP⟩)) := by
    unfold ProvenanceMap.applyCopy
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.shiftedCopyOffset]
    simp (config := { decide := true }) [c1, hp1, hf1, Size.add, Size.mul, Size.ofBytes,
      Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, EStateM.pure, EStateM.bind,
      EStateM.get, EStateM.set, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
      -Array.forIn_toList, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
    intro s f
    simp only [mem_miri_insertEntry, hm1]
    constructor
    · intro h
      rcases h with ⟨⟨⟨⟨⟨⟨⟨h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h
      · exact ⟨0, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨1, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨2, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨3, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨4, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨5, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨6, by decide, by simpa [Size.ofBytes] using h⟩
      · exact ⟨7, by decide, by simpa [Size.ofBytes] using h⟩
    · rintro ⟨k, hk, hs, hf'⟩
      subst hs hf'
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true })
  obtain ⟨dst2, hdst2, hp2, f2, hf2, hm2⟩ := happ2
  refine ⟨src, c0, c1, dst1, dst2, hsrc_eq, hc0, hc1, hdst1, hdst2, ?_⟩
  have hmemk : ∀ k, k < 8 → (Size.ofBytes (UInt64.ofNat k), ⟨UInt8.ofNat k, prov, vP⟩) ∈ f2 :=
    fun k hk => (hm2 _).mpr ⟨k, hk, rfl⟩
  have hnonempty : (f2.filter fun entry => decide (entry.1.bytes < 8)).isEmpty = false :=
    array_filter_isEmpty_false_of_mem f2 _ _ (hmemk 0 (by decide)) rfl
  have hfindk : ∀ k (hk : k < 8),
      f2.find? (fun entry => entry.1.bytes == UInt64.ofNat k) =
        some (Size.ofBytes (UInt64.ofNat k), ⟨UInt8.ofNat k, prov, vP⟩) := by
    intro k hk
    refine array_find?_eq_some_of_unique f2 _ _ (hmemk k hk) (by simp [Size.ofBytes]) ?_
    intro b hb hbp
    obtain ⟨j, hj, rfl⟩ := (hm2 b).mp hb
    have hjk : j = k := by
      simp only [Size.ofBytes, beq_iff_eq] at hbp
      have := congrArg UInt64.toNat hbp
      simp [UInt64.toNat_ofNat'] at this
      omega
    subst hjk; rfl
  have hf0 : f2.find? (fun entry => entry.1.bytes == 0) = some (Size.ofBytes 0, ⟨0, prov, vP⟩) := hfindk 0 (by decide)
  have hf1' : f2.find? (fun entry => entry.1.bytes == 1) = some (Size.ofBytes 1, ⟨1, prov, vP⟩) := hfindk 1 (by decide)
  have hf2' : f2.find? (fun entry => entry.1.bytes == 2) = some (Size.ofBytes 2, ⟨2, prov, vP⟩) := hfindk 2 (by decide)
  have hf3 : f2.find? (fun entry => entry.1.bytes == 3) = some (Size.ofBytes 3, ⟨3, prov, vP⟩) := hfindk 3 (by decide)
  have hf4 : f2.find? (fun entry => entry.1.bytes == 4) = some (Size.ofBytes 4, ⟨4, prov, vP⟩) := hfindk 4 (by decide)
  have hf5 : f2.find? (fun entry => entry.1.bytes == 5) = some (Size.ofBytes 5, ⟨5, prov, vP⟩) := hfindk 5 (by decide)
  have hf6 : f2.find? (fun entry => entry.1.bytes == 6) = some (Size.ofBytes 6, ⟨6, prov, vP⟩) := hfindk 6 (by decide)
  have hf7 : f2.find? (fun entry => entry.1.bytes == 7) = some (Size.ofBytes 7, ⟨7, prov, vP⟩) := hfindk 7 (by decide)
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp2, hf2]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    List.range', throw, throwThe, MonadExceptOf.throw]
  rw [hnonempty, hf0, hf1', hf2', hf3, hf4, hf5, hf6, hf7]
  simp [hnw]

/-- **Vendored `ProvenanceMap.prepareCopy` + `applyCopy` end-to-end `p` / `p + 256` offset splice.**
Starting from two whole-pointer entries `p = 0x1000` (at offset `0`) and `p + 256 = 0x1100` (at
offset `8`, sharing identical byte `0 = 0x00`), copying byte `0` of `p` and bytes `1 .. 7` of
`p + 256` through unmodified vendored `prepareCopy` and `applyCopy` strips provenance on
subsequent vendored `readPtr 0 8` (`.ok none` in runtime mode, `.error (.readPartialPointer 0)`
in CTFE mode). -/
theorem prepareCopy_applyCopy_splice_p_p256 {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (prov : Prov) (hnw : ¬ some prov = PointerProvenance.wildcard (Prov := Prov)) :
    let data : Array UInt8 := #[
      0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    ]
    ∃ src c0 c1 dst1 dst2,
      ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov), (Size.ofBytes 8, prov)] = .ok src ∧
      src.prepareCopy ⟨Size.ofBytes 0, Size.ofBytes 1⟩ data (Size.ofBytes 8) = .ok c0 ∧
      src.prepareCopy ⟨Size.ofBytes 9, Size.ofBytes 7⟩ data (Size.ofBytes 8) = .ok c1 ∧
      ProvenanceMap.applyCopy c0 ⟨Size.ofBytes 0, Size.ofBytes 1⟩ 1 ProvenanceMap.new = .ok () dst1 ∧
      ProvenanceMap.applyCopy c1 ⟨Size.ofBytes 1, Size.ofBytes 7⟩ 1 dst1 = .ok () dst2 ∧
      dst2.readPtr (Size.ofBytes 0) (Size.ofBytes 8) =
        (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
         else .error (.readPartialPointer (Size.ofBytes 0))) := by
  intro data
  have hsrc : ∃ src, ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, prov), (Size.ofBytes 8, prov)] = .ok src := by
    unfold ProvenanceMap.fromPresortedPtrs
    simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
    simp [Size.ofBytes]
  obtain ⟨src, hsrc_eq⟩ := hsrc
  obtain ⟨hsp, hsf⟩ := fromPresortedPtrs_fields _ src hsrc_eq
  let vP : Vector UInt8 8 := #v[0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let vP256 : Vector UInt8 8 := #v[0x00, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let c0 : ProvenanceCopy Prov := ⟨#[], #[(Size.ofBytes 0, ⟨0, prov, vP⟩)]⟩
  let c1 : ProvenanceCopy Prov := ⟨#[], #[
    (Size.ofBytes 0, ⟨1, prov, vP256⟩), (Size.ofBytes 1, ⟨2, prov, vP256⟩),
    (Size.ofBytes 2, ⟨3, prov, vP256⟩), (Size.ofBytes 3, ⟨4, prov, vP256⟩),
    (Size.ofBytes 4, ⟨5, prov, vP256⟩), (Size.ofBytes 5, ⟨6, prov, vP256⟩),
    (Size.ofBytes 6, ⟨7, prov, vP256⟩)]⟩
  have hc0 : src.prepareCopy ⟨Size.ofBytes 0, Size.ofBytes 1⟩ data (Size.ofBytes 8) = .ok c0 := by
    unfold ProvenanceMap.prepareCopy
    simp only [ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes, hsp, hsf]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.rangeEnd,
      Miri.Memory.ProvenanceMap.adjustedStart, Miri.Memory.ProvenanceMap.rangeEntries,
      Miri.Memory.ProvenanceMap.subtractSize, Miri.Memory.ProvenanceMap.ptrFragments]
    simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end,
      Size.add, Size.sub, Size.ZERO, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, data, c0, vP,
      ← Array.forIn_toList, List.range', List.forIn_cons, List.forIn_nil]
    decide
  have hc1 : src.prepareCopy ⟨Size.ofBytes 9, Size.ofBytes 7⟩ data (Size.ofBytes 8) = .ok c1 := by
    unfold ProvenanceMap.prepareCopy
    simp only [ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes, hsp, hsf]
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.rangeEnd,
      Miri.Memory.ProvenanceMap.adjustedStart, Miri.Memory.ProvenanceMap.rangeEntries,
      Miri.Memory.ProvenanceMap.subtractSize, Miri.Memory.ProvenanceMap.ptrFragments]
    simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end,
      Size.add, Size.sub, Size.ZERO, Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, data, c1, vP256,
      ← Array.forIn_toList, List.range', List.forIn_cons, List.forIn_nil]
    decide
  have happ1 : ∃ dst1,
      ProvenanceMap.applyCopy c0 ⟨Size.ofBytes 0, Size.ofBytes 1⟩ 1 ProvenanceMap.new = .ok () dst1 ∧
      dst1.ptrs = #[] ∧
      ∃ f1, dst1.byteFragments = some f1 ∧ ∀ e, e ∈ f1 ↔ e = (Size.ofBytes 0, ⟨0, prov, vP⟩) := by
    unfold ProvenanceMap.applyCopy
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.shiftedCopyOffset]
    simp (config := { decide := true }) [c0, ProvenanceMap.new, Size.add, Size.mul, Size.ofBytes,
      Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, EStateM.pure, EStateM.bind,
      EStateM.get, EStateM.set, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
      -Array.forIn_toList, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
    intro s f
    simp only [mem_miri_insertEntry, Array.not_mem_empty, false_and, false_or]
    constructor <;> (intro h; simpa using h)
  obtain ⟨dst1, hdst1, hp1, f1, hf1, hm1⟩ := happ1
  have happ2 : ∃ dst2,
      ProvenanceMap.applyCopy c1 ⟨Size.ofBytes 1, Size.ofBytes 7⟩ 1 dst1 = .ok () dst2 ∧
      dst2.ptrs = #[] ∧
      ∃ f2, dst2.byteFragments = some f2 ∧
        (∀ e, e ∈ f2 ↔ e = (Size.ofBytes 0, ⟨0, prov, vP⟩) ∨
          (∃ k, 1 ≤ k ∧ k < 8 ∧ e = (Size.ofBytes (UInt64.ofNat k), ⟨UInt8.ofNat k, prov, vP256⟩))) := by
    unfold ProvenanceMap.applyCopy
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.checked,
      Miri.Memory.ProvenanceMap.shiftedCopyOffset]
    simp (config := { decide := true }) [c1, hp1, hf1, Size.add, Size.mul, Size.ofBytes,
      Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, EStateM.pure, EStateM.bind,
      EStateM.get, EStateM.set, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
      -Array.forIn_toList, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
    intro s f
    simp only [mem_miri_insertEntry, hm1]
    constructor
    · intro h
      rcases h with ⟨⟨⟨⟨⟨⟨⟨h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h, _⟩ | h
      · exact Or.inl (by simpa [Size.ofBytes] using h)
      · exact Or.inr ⟨1, by decide, by decide, by simpa [Size.ofBytes] using h⟩
      · exact Or.inr ⟨2, by decide, by decide, by simpa [Size.ofBytes] using h⟩
      · exact Or.inr ⟨3, by decide, by decide, by simpa [Size.ofBytes] using h⟩
      · exact Or.inr ⟨4, by decide, by decide, by simpa [Size.ofBytes] using h⟩
      · exact Or.inr ⟨5, by decide, by decide, by simpa [Size.ofBytes] using h⟩
      · exact Or.inr ⟨6, by decide, by decide, by simpa [Size.ofBytes] using h⟩
      · exact Or.inr ⟨7, by decide, by decide, by simpa [Size.ofBytes] using h⟩
    · rintro (⟨hs, hf'⟩ | ⟨k, hk1, hk8, hs, hf'⟩)
      · subst hs hf'; simp (config := { decide := true })
      · subst hs hf'
        have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (config := { decide := true })
  obtain ⟨dst2, hdst2, hp2, f2, hf2, hm2⟩ := happ2
  refine ⟨src, c0, c1, dst1, dst2, hsrc_eq, hc0, hc1, hdst1, hdst2, ?_⟩
  have hmem0 : (Size.ofBytes 0, ⟨0, prov, vP⟩) ∈ f2 := (hm2 _).mpr (Or.inl rfl)
  have hmem1 : (Size.ofBytes 1, ⟨1, prov, vP256⟩) ∈ f2 := (hm2 _).mpr (Or.inr ⟨1, by decide, by decide, rfl⟩)
  have hnonempty : (f2.filter fun entry => decide (entry.1.bytes < 8)).isEmpty = false :=
    array_filter_isEmpty_false_of_mem f2 _ _ hmem0 rfl
  have hfind0 : f2.find? (fun entry => entry.1.bytes == 0) = some (Size.ofBytes 0, ⟨0, prov, vP⟩) := by
    refine array_find?_eq_some_of_unique f2 _ _ hmem0 rfl ?_
    intro b hb hbp
    rcases (hm2 b).mp hb with rfl | ⟨k, hk1, hk8, rfl⟩
    · rfl
    · simp only [Size.ofBytes, beq_iff_eq] at hbp
      have := congrArg UInt64.toNat hbp; simp [UInt64.toNat_ofNat'] at this; omega
  have hfind1 : f2.find? (fun entry => entry.1.bytes == 1) = some (Size.ofBytes 1, ⟨1, prov, vP256⟩) := by
    refine array_find?_eq_some_of_unique f2 _ _ hmem1 rfl ?_
    intro b hb hbp
    rcases (hm2 b).mp hb with rfl | ⟨k, hk1, hk8, rfl⟩
    · simp only [Size.ofBytes, beq_iff_eq] at hbp; exact absurd hbp (by decide)
    · have hk : k = 1 := by
        simp only [Size.ofBytes, beq_iff_eq] at hbp
        have := congrArg UInt64.toNat hbp; simp [UInt64.toNat_ofNat'] at this; omega
      subst hk; rfl
  have hvne : ¬ (vP256 = vP) := by decide
  unfold ProvenanceMap.readPtr
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes,
    ProvenanceMap.getByte, hp2, hf2]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  simp (config := { decide := true }) [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ofBytes, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    List.range', throw, throwThe, MonadExceptOf.throw]
  rw [hnonempty, hfind0, hfind1]
  simp [hnw, hvne]
  cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp [Size.ofBytes]

/-- Empty fragment map reads `.ok none` in both runtime and CTFE modes (4-byte and 8-byte). -/
theorem trRead_empty {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (n : UInt64) (hn : n ≠ 0) :
    trRead (Prov := Prov) #[] 0 n = .ok none := by
  have hfrom : ∃ pm, ProvenanceMap.fromParts (Prov := Prov) #[] (some #[]) = .ok pm := by
    unfold ProvenanceMap.fromParts
    simp only [Option.map_some, Option.getD_some, Array.toList_empty]
    simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
    exact ⟨_, rfl⟩
  obtain ⟨pm, hpm⟩ := hfrom
  obtain ⟨hp, hf⟩ := fromParts_fields _ _ pm hpm
  unfold trRead
  rw [hpm]
  dsimp only
  unfold ProvenanceMap.readPtr
  simp only [ProvenanceMap.getPtr, ProvenanceMap.rangePtrs, ProvenanceMap.rangeBytes, hp, hf]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
    Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
  have h0n : (0 : UInt64) + n = n := UInt64.zero_add n
  have hlt : ¬ (n < 0) := by
    intro h; simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] at h; omega
  simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes, hn, h0n, hlt,
    Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/-- General missing-byte stripping lemma for any positive pointer width `n ≤ 8` (in particular `4`
and `8`): any non-empty fragment map on `[0, n)` missing at least one byte `k < n` strips
provenance in both runtime (`.ok none`) and CTFE (`.error (.readPartialPointer 0)`) modes. -/
theorem readPtr_missing_byte_strips {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (n : Nat) (hn0 : 0 < n) (hn8 : n ≤ 8)
    (pm : ProvenanceMap Prov) (frags : Array (Size × PointerFrag Prov))
    (hp : pm.ptrs = #[]) (hf : pm.byteFragments = some frags)
    (hne : ∃ e ∈ frags, e.1.bytes < UInt64.ofNat n)
    (hmiss : ∃ k, k < n ∧ ∀ e ∈ frags, e.1.bytes ≠ UInt64.ofNat k) :
    pm.readPtr (Size.ofBytes 0) (Size.ofBytes (UInt64.ofNat n)) =
      (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
       else .error (.readPartialPointer (Size.ofBytes 0))) := by
  obtain ⟨e0, he0, he0lt⟩ := hne
  obtain ⟨k, hk, hno⟩ := hmiss
  have hfind_none : frags.find? (fun entry => entry.1.bytes == UInt64.ofNat k) = none := by
    rw [Array.find?_eq_none]
    intro e he hbeq
    exact hno e he (beq_iff_eq.mp hbeq)
  have hn_nz : UInt64.ofNat n ≠ 0 := by
    intro h0; have := congrArg UInt64.toNat h0
    have hn64 : n < 2 ^ 64 := by omega
    simp only [UInt64.toNat_ofNat', UInt64.toNat_zero, Nat.mod_eq_of_lt hn64] at this; omega
  have hget_ok : ∀ (j : Nat), j < n →
      pm.getByte (Size.ofBytes (UInt64.ofNat j)) (Size.ofBytes (UInt64.ofNat n)) =
        .ok ((frags.find? fun entry => entry.1.bytes == UInt64.ofNat j).map Prod.snd) := by
    intro j hj
    unfold ProvenanceMap.getByte ProvenanceMap.rangePtrs
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
      Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
    have hj1 : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one]
      have : j < 2 ^ 64 := by omega
      have : j + 1 < 2 ^ 64 := by omega
      omega
    have hnotlt : ¬ (UInt64.ofNat j + 1 < UInt64.ofNat j) := by
      rw [hj1, UInt64.lt_iff_toNat_lt]
      simp only [UInt64.toNat_ofNat']
      have : j < 2 ^ 64 := by omega
      have : j + 1 < 2 ^ 64 := by omega
      omega
    simp [hp, hf, hn_nz, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes, hnotlt,
      Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  have hadd0 : ∀ (j : Nat),
      Size.add (Size.ofBytes 0) (Size.ofBytes (UInt64.ofNat j)) =
        .ok (Size.ofBytes (UInt64.ofNat j)) := by
    intro j
    unfold Size.add Size.ofBytes
    have h0 : (0 : UInt64) + UInt64.ofNat j = UInt64.ofNat j := UInt64.zero_add _
    have hnot : ¬ (UInt64.ofNat j < 0) := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]; omega
    simp [h0, hnot]
  let body : Nat → Option (Option Prov) × Option (Prov × Vector UInt8 8) →
      Except ProvenanceMapError (ForInStep (Option (Option Prov) × Option (Prov × Vector UInt8 8))) :=
    fun idx r => do
      let position ← (Size.add (Size.ofBytes 0) (Size.ofBytes (UInt64.ofNat idx))).mapError
        (ProvenanceMapError.memory ∘ MemoryError.sizeError)
      let fragment ← pm.getByte position (Size.ofBytes (UInt64.ofNat n))
      match fragment with
      | some frag =>
        if some frag.prov == PointerProvenance.wildcard (Prov := Prov) then
          pure (ForInStep.yield (none, r.2))
        else if frag.idx.toNat != idx then
          pure (ForInStep.done (some none, r.2))
        else
          match r.2 with
          | some pair =>
            if (frag.prov, frag.bytes) != pair then pure (ForInStep.done (some none, r.2))
            else pure (ForInStep.yield (none, r.2))
          | none => pure (ForInStep.yield (none, some (frag.prov, frag.bytes)))
      | _ => pure (ForInStep.done (some none, r.2))
  have hloop : ∀ (l : List Nat) (acc : Option (Prov × Vector UInt8 8)),
      (∀ j ∈ l, j < n) → k ∈ l →
      ∃ acc', forIn l ((none : Option (Option Prov)), acc) body = .ok (some none, acc') := by
    intro l
    induction l with
    | nil => intro _ _ hmem; cases hmem
    | cons j rest ih =>
      intro acc hlt hmem
      rw [List.forIn_cons]
      have hj : j < n := hlt j (List.Mem.head _)
      have hstep : body j (none, acc) =
          match frags.find? (fun entry => entry.1.bytes == UInt64.ofNat j) with
          | none => .ok (.done (some none, acc))
          | some pair =>
            if some pair.2.prov == PointerProvenance.wildcard (Prov := Prov) then
              .ok (.yield (none, acc))
            else if pair.2.idx.toNat != j then
              .ok (.done (some none, acc))
            else
              match acc with
              | some p =>
                if (pair.2.prov, pair.2.bytes) != p then .ok (.done (some none, acc))
                else .ok (.yield (none, acc))
              | none => .ok (.yield (none, some (pair.2.prov, pair.2.bytes))) := by
        dsimp only [body]
        simp only [bind, Except.bind, pure, Except.pure, hadd0 j, Except.mapError, hget_ok j hj]
        cases frags.find? (fun entry => entry.1.bytes == UInt64.ofNat j) <;> rfl
      rw [hstep]
      by_cases hjk : j = k
      · subst hjk; rw [hfind_none]; exact ⟨acc, rfl⟩
      · have hkr : k ∈ rest := by
          cases hmem with
          | head => exact absurd rfl hjk
          | tail _ hr => exact hr
        have hlt' : ∀ x ∈ rest, x < n := fun x hx => hlt x (List.Mem.tail _ hx)
        cases frags.find? (fun entry => entry.1.bytes == UInt64.ofNat j) with
        | none => exact ⟨acc, rfl⟩
        | some pair =>
          by_cases hw : (some pair.2.prov == PointerProvenance.wildcard (Prov := Prov)) = true
          · simp only [hw, ↓reduceIte, bind, Except.bind]; exact ih acc hlt' hkr
          · simp only [hw, Bool.false_eq_true, ↓reduceIte]
            by_cases hi : (pair.2.idx.toNat != j) = true
            · simp only [hi, ↓reduceIte, bind, Except.bind]; exact ⟨acc, rfl⟩
            · simp only [hi, Bool.false_eq_true, ↓reduceIte]
              cases acc with
              | none => simp only [bind, Except.bind]; exact ih (some (pair.2.prov, pair.2.bytes)) hlt' hkr
              | some p =>
                by_cases hpq : ((pair.2.prov, pair.2.bytes) != p) = true
                · simp only [hpq, ↓reduceIte, bind, Except.bind]; exact ⟨some p, rfl⟩
                · simp only [hpq, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]; exact ih (some p) hlt' hkr
  have hmem_range : k ∈ List.range' 0 n 1 := by
    rw [List.mem_range']; exact ⟨k, hk, by omega⟩
  have hlt_range : ∀ j ∈ List.range' 0 n 1, j < n := by
    intro j hj; rw [List.mem_range'] at hj; obtain ⟨i, hi, rfl⟩ := hj; omega
  obtain ⟨acc', hres⟩ := hloop (List.range' 0 n 1) none hlt_range hmem_range
  have h0n : (0 : UInt64) + UInt64.ofNat n = UInt64.ofNat n := UInt64.zero_add _
  have hnotlt0 : ¬ (UInt64.ofNat n < 0) := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]; omega
  have hn_toNat : (UInt64.ofNat n).toNat = n := by
    have hn64 : n < 2 ^ 64 := by omega
    simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn64]
  have hgetPtr : pm.getPtr (Size.ofBytes 0) = none := by
    simp [ProvenanceMap.getPtr, hp]
  have hrangePtrs : pm.rangePtrs (allocRange (Size.ofBytes 0) (Size.ofBytes (UInt64.ofNat n)))
      (Size.ofBytes (UInt64.ofNat n)) = .ok #[] := by
    unfold ProvenanceMap.rangePtrs
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.adjustedStart,
      Miri.Memory.ProvenanceMap.rangeEnd, Miri.Memory.ProvenanceMap.rangeEntries]
    simp [hp, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes,
      hn_nz, h0n, hnotlt0, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  have hrangeBytes : ∃ fs, pm.rangeBytes (allocRange (Size.ofBytes 0) (Size.ofBytes (UInt64.ofNat n))) = .ok fs ∧
      fs.isEmpty = false := by
    unfold ProvenanceMap.rangeBytes
    delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.rangeEnd,
      Miri.Memory.ProvenanceMap.rangeEntries]
    have hre : (allocRange (Size.ofBytes 0) (Size.ofBytes (UInt64.ofNat n))).endExclusive =
        .ok (Size.ofBytes (UInt64.ofNat n)) := by
      simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes,
        Except.mapError, h0n, hnotlt0]
    simp only [hf, hre, Option.getD_some, Except.mapError, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure]
    refine ⟨_, rfl, ?_⟩
    exact array_filter_isEmpty_false_of_mem frags _ e0 he0 (by
      simp [allocRange, Size.ofBytes, he0lt, UInt64.zero_le])
  obtain ⟨fs, hrb, hfs_ne⟩ := hrangeBytes
  unfold ProvenanceMap.readPtr
  simp only [hgetPtr, hrangePtrs, hrb, Array.isEmpty_empty, hfs_ne,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]
  delta_miri_private Miri.Memory.ProvenanceMap [Miri.Memory.ProvenanceMap.inspectFragments]
  simp only [Size.ofBytes, hn_toNat, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]
  have hforIn : ∀ (f : Nat → Option (Option Prov) × Option (Prov × Vector UInt8 8) →
      Except ProvenanceMapError (ForInStep (Option (Option Prov) × Option (Prov × Vector UInt8 8)))),
      (∀ idx r, f idx r = body idx r) →
      forIn (List.range' 0 n 1) ((none : Option (Option Prov)), (none : Option (Prov × Vector UInt8 8))) f =
        .ok (some none, acc') := by
    intro f hf; have : f = body := funext fun i => funext (hf i); rw [this]; exact hres
  rw [hforIn _ (fun idx r => by
    dsimp only [body]
    simp only [Size.ofBytes, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    cases Except.mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
        ((Size.mk 0).add (Size.mk (UInt64.ofNat idx))) with
    | error _ => rfl
    | ok v =>
      cases pm.getByte v (Size.mk (UInt64.ofNat n)) with
      | error _ => rfl
      | ok v =>
        cases v with
        | none => rfl
        | some frag => cases r.snd <;> rfl)]
  cases PointerProvenance.offsetIsAddr (Prov := Prov) <;> simp [Size.ofBytes]

/-- Any non-empty fragment map on `[0, 4)` missing at least one byte `k < 4` strips provenance in
both runtime (`.ok none`) and CTFE (`.error (.readPartialPointer 0)`) modes. -/
theorem readPtr4_missing_byte_strips {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pm : ProvenanceMap Prov) (frags : Array (Size × PointerFrag Prov))
    (hp : pm.ptrs = #[]) (hf : pm.byteFragments = some frags)
    (hne : ∃ e ∈ frags, e.1.bytes < 4)
    (hmiss : ∃ k, k < 4 ∧ ∀ e ∈ frags, e.1.bytes ≠ UInt64.ofNat k) :
    pm.readPtr (Size.ofBytes 0) (Size.ofBytes 4) =
      (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
       else .error (.readPartialPointer (Size.ofBytes 0))) :=
  readPtr_missing_byte_strips 4 (by decide) (by decide) pm frags hp hf hne hmiss

/-- Any non-empty fragment map on `[0, 8)` missing at least one byte `k < 8` strips provenance in
both runtime (`.ok none`) and CTFE (`.error (.readPartialPointer 0)`) modes. -/
theorem readPtr8_missing_byte_strips {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pm : ProvenanceMap Prov) (frags : Array (Size × PointerFrag Prov))
    (hp : pm.ptrs = #[]) (hf : pm.byteFragments = some frags)
    (hne : ∃ e ∈ frags, e.1.bytes < 8)
    (hmiss : ∃ k, k < 8 ∧ ∀ e ∈ frags, e.1.bytes ≠ UInt64.ofNat k) :
    pm.readPtr (Size.ofBytes 0) (Size.ofBytes 8) =
      (if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok none
       else .error (.readPartialPointer (Size.ofBytes 0))) :=
  readPtr_missing_byte_strips 8 (by decide) (by decide) pm frags hp hf hne hmiss

/-- **CTFE tag blindness (`DIV-LM-CTFE-TAG`).** Splicing two pointers into the same allocation
`alloc 7` with different borrow tags (`tag = 7` vs `tag = 9`): Miri runtime (`pvRt`) strips
provenance because `Provenance.concrete` carries `BorTag`, whereas tag-free CTFE `AllocId`
(`pvCt`) retains `pvCt 7 7`. -/
theorem w_lm_ctfe_tag_blind :
    trRead (fe8 ⟨0, pvRt 7 7, ptrImage 8 0x1000⟩ ⟨1, pvRt 7 7, ptrImage 8 0x1000⟩
      ⟨2, pvRt 7 7, ptrImage 8 0x1000⟩ ⟨3, pvRt 7 7, ptrImage 8 0x1000⟩
      ⟨4, pvRt 7 9, ptrImage 8 0x1000⟩ ⟨5, pvRt 7 9, ptrImage 8 0x1000⟩
      ⟨6, pvRt 7 9, ptrImage 8 0x1000⟩ ⟨7, pvRt 7 9, ptrImage 8 0x1000⟩) 0 8 = .ok none ∧
    trRead (fe8 ⟨0, pvCt 7 7, ptrImage 8 0x1000⟩ ⟨1, pvCt 7 7, ptrImage 8 0x1000⟩
      ⟨2, pvCt 7 7, ptrImage 8 0x1000⟩ ⟨3, pvCt 7 7, ptrImage 8 0x1000⟩
      ⟨4, pvCt 7 9, ptrImage 8 0x1000⟩ ⟨5, pvCt 7 9, ptrImage 8 0x1000⟩
      ⟨6, pvCt 7 9, ptrImage 8 0x1000⟩ ⟨7, pvCt 7 9, ptrImage 8 0x1000⟩) 0 8 = .ok (some (pvCt 7 7)) :=
  ⟨(readPtr8_runtime _ _ _ _ _ _ _ _ rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by decide),
   (readPtr8_ctfe _ _ _ _ _ _ _ _ rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by decide)⟩

/-- **Universal `Kani#5205` vendored Miri `bool` validity characterization.** For every byte
`b : UInt8`, unmodified vendored `Validity.checkPrimitive .boolean` accepts `b` iff `b ≤ 1` and
rejects every `b ≥ 2` with `.invalidBool b`. -/
theorem miri_checkPrimitive_bool_iff (b : UInt8) :
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 b))
      (fun _ s => .ok false s) () =
      (if b.toNat ≤ 1 then .ok .valid () else .error (.failure (.invalidBool b)) ()) := by
  unfold Validity.checkPrimitive Scalar.toBool Scalar.toUInt8 Scalar.toUInt Scalar.toBits
    Scalar.toScalarInt Scalar.tryToScalarInt Scalar.fromScalarInt ScalarInt.toBits
    ScalarInt.ofUInt8 Size.ofBytes
  have hlt : b.toNat < 256 := UInt8.toNat_lt b
  have h128 : b.toNat < 2 ^ 128 := by omega
  simp (config := { decide := true }) only [Id.run, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.mapError, throw, throwThe, MonadExceptOf.throw, ↓reduceIte,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128, UInt8.ofNat_toNat]
  by_cases h0 : b = 0
  · subst h0; rfl
  · by_cases h1 : b = 1
    · subst h1; rfl
    · have hgt : ¬ (b.toNat ≤ 1) := by
        intro hle
        have : b.toNat = 0 ∨ b.toNat = 1 := by omega
        rcases this with hb | hb
        · exact h0 (UInt8.toNat_inj.mp hb)
        · exact h1 (UInt8.toNat_inj.mp hb)
      simp only [hgt, ↓reduceIte, beq_iff_eq, h0, h1]

/-- **Universal `Kani#5205` vendored Miri `char` validity characterization.** For every `c : UInt32`,
unmodified vendored `Validity.checkPrimitive .character` accepts `c` iff `c` is a Unicode scalar
value (`c < 0xD800 ∨ 0xE000 ≤ c ≤ 0x10FFFF`) and rejects every surrogate/out-of-range value with
`.invalidChar c`. -/
theorem miri_checkPrimitive_char_iff (c : UInt32) :
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 c))
      (fun _ s => .ok false s) () =
      (if c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF) then .ok .valid ()
       else .error (.failure (.invalidChar c)) ()) := by
  unfold Validity.checkPrimitive Scalar.toChar ScalarInt.toChar ScalarInt.toUInt32
    ScalarInt.toUInt ScalarInt.toBits Scalar.toScalarInt Scalar.tryToScalarInt Scalar.fromScalarInt
    ScalarInt.ofUInt32 Size.ofBytes
  delta_miri_private Miri.Memory.ScalarInt [Miri.Memory.ScalarInt.isUnicodeScalar]
  delta_miri_private Miri.Memory.Scalar [Miri.Memory.Scalar.wrapIntError]
  have hlt : c.toNat < 2 ^ 32 := UInt32.toNat_lt c
  have h128 : c.toNat < 2 ^ 128 := by omega
  simp (config := { decide := true }) only [Id.run, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.mapError, throw, throwThe, MonadExceptOf.throw, ↓reduceIte,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128, UInt32.ofNat_toNat]
  by_cases hc : c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF)
  · have h1 : c.toNat ≤ 0x10FFFF := by omega
    have h2 : ¬ (0xD800 ≤ c.toNat ∧ c.toNat ≤ 0xDFFF) := by omega
    have h3 : 0xD800 ≤ c.toNat → 0xE000 ≤ c.toNat := by omega
    simp [hc, h1, h2]
    exact h3
  · simp only [hc, ↓reduceIte]
    by_cases hle : c.toNat ≤ 0x10FFFF
    · have hsurr : 0xD800 ≤ c.toNat ∧ c.toNat ≤ 0xDFFF := by omega
      simp [hle, hsurr.1, hsurr.2]
    · simp [hle]

/-- 64-bit little-endian target data layout for vendored `Miri.Memory.Allocation` witnesses. -/
def miriLayout64 : TargetDataLayout :=
  { endian := .little, pointerWidth := .w64 }

/-- Run vendored `Allocation.fromBytes` → `Allocation.writeBytes` → `Allocation.readScalar`
(untyped byte write followed by scalar read) for `Kani#5205` end-to-end correspondence. -/
def miriWriteThenReadScalar (init write : Array UInt8) (readSz : UInt64) :
    Except AllocError (Scalar Provenance) := do
  let a0 ← Allocation.fromBytes (Prov := Provenance) init Align.ONE .Mut
  match Allocation.writeBytes Size.ZERO write (Size.ofBytes 8) a0 with
  | .ok () a1 => a1.readScalar miriLayout64 ⟨Size.ZERO, Size.ofBytes readSz⟩ false
  | .error e _ => .error e

/-- **End-to-end vendored `Miri.Memory.Allocation` `Kani#5205` witness.** Writing untyped byte
`2u8` (resp. surrogate `0xD800`) into a mutable `Allocation` via `Allocation.writeBytes` succeeds
without write-time UB; `Allocation.readScalar` reads back the raw scalar cleanly, which
`Validity.checkPrimitive` accepts at `.scalar` and rejects at `.boolean` (`invalidBool 2`) /
`.character` (`invalidChar 0xD800`). -/
theorem w_lm_kani5205_alloc_e2e :
    miriWriteThenReadScalar #[0] #[2] 1 = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 2)) ∧
    miriWriteThenReadScalar #[0, 0, 0, 0] #[0x00, 0xD8, 0x00, 0x00] 4 =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800)) ∧
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 2))
      (fun _ s => .ok false s) () = .error (.failure (.invalidBool 2)) () ∧
    Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
      .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800))
      (fun _ s => .ok false s) () = .error (.failure (.invalidChar 0xD800)) () := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> (
    unfold miriWriteThenReadScalar Allocation.fromBytes Allocation.writeBytes Allocation.readScalar
      miriLayout64
    delta_miri_private Miri.Memory.Allocation [Miri.Memory.checkedAlign,
      Miri.Memory.sizeForArray, Miri.Memory.readTargetUInt, Miri.Memory.pointerSize,
      Miri.Memory.Allocation.checkedSlice, Miri.Memory.Allocation.setInitialization,
      Miri.Memory.Allocation.overwriteRawBytes]
    simp (config := { decide := true }) [ProvenanceMap.clear_new, InitMask.new, InitMask.setRange,
      InitMask.isRangeInitialized, Align.ONE, Size.ZERO, Size.ofBytes, allocRange,
      AllocRange.endExclusive, AllocRange.end, Size.add, Except.mapError, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure, Id.run, Scalar.fromUInt, ScalarInt.ofUInt8,
      ScalarInt.ofUInt32, Scalar.fromScalarInt]
    try rfl)

/-- Non-vacuous instantiations of vendored `ProvenanceMap.clear`, `prepareCopy`+`applyCopy`,
`pvRt` injectivity, and `Validity.checkPrimitive` universal theorems. -/
theorem clear_and_prepareCopy_instance :
    (clearRead #[(Size.ofBytes 0, pvRt 7 7)] 1 7 #[0, 16, 0, 0, 0, 0, 0, 0] 8 0 8 = .ok none) ∧
    (clearRead #[(Size.ofBytes 0, pvCt 7 7)] 1 7 #[0, 16, 0, 0, 0, 0, 0, 0] 8 0 8 =
      .error (.readPartialPointer (Size.ofBytes 0))) ∧
    (∃ pm pm', ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, pvRt 7 7)] = .ok pm ∧
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 1⟩ #[0, 16, 0, 0, 0, 0, 0, 0] (Size.ofBytes 8) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      (∃ frags, pm'.byteFragments = some frags ∧
        (∀ e, e ∈ frags ↔ ∃ k, k < 8 ∧ k ≠ 1 ∧
          e = (Size.ofBytes (UInt64.ofNat k),
            ⟨UInt8.ofNat k, pvRt 7 7, Vector.ofFn fun idx =>
              if hi : idx.val < 8 then (#[0, 16, 0, 0, 0, 0, 0, 0] : Array UInt8)[idx.val]'(by omega) else 0⟩))) ∧
      pm'.readPtr (Size.ofBytes 0) (Size.ofBytes 8) = .ok none) ∧
    (∃ pm pm', ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, pvRt 9 9)] = .ok pm ∧
      ProvenanceMap.clear ⟨Size.ofBytes 1, Size.ofBytes 1⟩ #[0, 16, 0, 0] (Size.ofBytes 4) pm = .ok () pm' ∧
      pm'.ptrs = #[] ∧
      (∃ frags, pm'.byteFragments = some frags ∧
        (∀ e, e ∈ frags ↔ ∃ k, k < 4 ∧ k ≠ 1 ∧
          e = (Size.ofBytes (UInt64.ofNat k),
            ⟨UInt8.ofNat k, pvRt 9 9, Vector.ofFn fun idx =>
              if hi : idx.val < 4 then (#[0, 16, 0, 0] : Array UInt8)[idx.val]'(by omega) else 0⟩))) ∧
      pm'.readPtr (Size.ofBytes 0) (Size.ofBytes 4) = .ok none) ∧
    (∃ src c0 c1 dst1 dst2,
      ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, pvRt 7 7)] = .ok src ∧
      src.prepareCopy ⟨Size.ofBytes 0, Size.ofBytes 1⟩ #[0, 16, 0, 0, 0, 0, 0, 0] (Size.ofBytes 8) = .ok c0 ∧
      src.prepareCopy ⟨Size.ofBytes 1, Size.ofBytes 7⟩ #[0, 16, 0, 0, 0, 0, 0, 0] (Size.ofBytes 8) = .ok c1 ∧
      ProvenanceMap.applyCopy c0 ⟨Size.ofBytes 0, Size.ofBytes 1⟩ 1 ProvenanceMap.new = .ok () dst1 ∧
      ProvenanceMap.applyCopy c1 ⟨Size.ofBytes 1, Size.ofBytes 7⟩ 1 dst1 = .ok () dst2 ∧
      dst2.readPtr (Size.ofBytes 0) (Size.ofBytes 8) = .ok (some (pvRt 7 7))) ∧
    (∃ src c0 c1 dst1 dst2,
      ProvenanceMap.fromPresortedPtrs #[(Size.ofBytes 0, pvRt 7 7), (Size.ofBytes 8, pvRt 7 7)] = .ok src ∧
      src.prepareCopy ⟨Size.ofBytes 0, Size.ofBytes 1⟩ #[0, 16, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0] (Size.ofBytes 8) = .ok c0 ∧
      src.prepareCopy ⟨Size.ofBytes 9, Size.ofBytes 7⟩ #[0, 16, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0] (Size.ofBytes 8) = .ok c1 ∧
      ProvenanceMap.applyCopy c0 ⟨Size.ofBytes 0, Size.ofBytes 1⟩ 1 ProvenanceMap.new = .ok () dst1 ∧
      ProvenanceMap.applyCopy c1 ⟨Size.ofBytes 1, Size.ofBytes 7⟩ 1 dst1 = .ok () dst2 ∧
      dst2.readPtr (Size.ofBytes 0) (Size.ofBytes 8) = .ok none) ∧
    (trRead (Prov := Provenance) #[] 0 8 = .ok none) ∧
    (trRead (Prov := AllocId) #[] 0 4 = .ok none) :=
  ⟨clear_partial_7bytes_strips_8 (pvRt 7 7) _ rfl,
   clear_partial_7bytes_strips_8 (pvCt 7 7) _ rfl,
   clear_partial_mid_strips_8 (pvRt 7 7) _ rfl,
   clear_partial_mid_strips_4 (pvRt 9 9) _ rfl,
   prepareCopy_applyCopy_intact_8 (pvRt 7 7) (pvRt_ne_wildcard 7 7 (by decide) (by decide)),
   prepareCopy_applyCopy_splice_p_p256 (pvRt 7 7) (pvRt_ne_wildcard 7 7 (by decide) (by decide)),
   trRead_empty 8 (by decide),
   trRead_empty 4 (by decide)⟩


/-! ## `V2026_06_01`: correspondence of `Trusted.Rustc.V2026_06_01.MirSemantics` with vendored `Miri.Memory.ProvenanceMap` -/

namespace V06

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### §1. The translation `PtrByteFrag → PointerFrag` -/

/-- The vendored Miri fragment of a `Trusted` pointer-byte fragment: index `byteIdx`, provenance
`pv allocId tag`, and the zero-padded 8-byte image of the originating pointer. -/
def mkFrag {Prov : Type} (pv : Nat → Nat → Prov) (f : PtrByteFrag) : PointerFrag Prov :=
  ⟨UInt8.ofNat f.byteIdx, pv f.allocId f.tag, ptrImage f.ptrBytes f.origOffset⟩

/-- The fragment (if any) that a `Trusted` abstract byte contributes to the provenance map.
Plain and uninitialized bytes contribute none: Miri tracks initialization in the `InitMask`, not
in the `ProvenanceMap`. -/
def fragOf {Prov : Type} (pv : Nat → Nat → Prov) : AbstractByte → Option (PointerFrag Prov)
  | .init _ (some f) => some (mkFrag pv f)
  | _ => none

def trEntriesAux {Prov : Type} (pv : Nat → Nat → Prov) :
    Nat → List AbstractByte → List (Size × PointerFrag Prov)
  | _, [] => []
  | i, b :: rest =>
    match fragOf pv b with
    | some g => (Size.ofBytes (UInt64.ofNat i), g) :: trEntriesAux pv (i + 1) rest
    | none => trEntriesAux pv (i + 1) rest

/-- **The exact translation of a `Trusted` byte stream to a vendored Miri fragment state**
(`ProvenanceMap.fromParts #[] (some (trEntries pv bs))`): one `PointerFrag` per
fragment-carrying byte, at that byte's offset. -/
def trEntries {Prov : Type} (pv : Nat → Nat → Prov) (bs : List AbstractByte) :
    Array (Size × PointerFrag Prov) :=
  (trEntriesAux pv 0 bs).toArray

/-- Well-formed fragment of a `pb`-byte target: the fragment width is the target pointer width,
the index is in range, and the originating offset is normalized (`normPtrByteOffset`). -/
def WF (pb : Nat) (f : PtrByteFrag) : Prop :=
  f.ptrBytes = pb ∧ f.byteIdx < pb ∧ f.origOffset < 256 ^ pb

theorem mkFrag_idx {Prov : Type} (pv : Nat → Nat → Prov) (f : PtrByteFrag)
    (h : f.byteIdx < 256) : (mkFrag pv f).idx.toNat = f.byteIdx := by
  show (UInt8.ofNat f.byteIdx).toNat = f.byteIdx
  rw [u8_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem scalarModulus_eq : ∀ n, scalarModulus n = 256 ^ n
  | 0 => rfl
  | n + 1 => by
      show Nat.mul 256 (scalarModulus n) = 256 ^ (n + 1)
      rw [scalarModulus_eq n, Nat.pow_succ, Nat.mul_comm]
      rfl

theorem normPtrByteOffset_lt (pb o : Nat) : normPtrByteOffset pb o < 256 ^ pb := by
  show Nat.mod o (scalarModulus pb) < 256 ^ pb
  rw [scalarModulus_eq]
  exact Nat.mod_lt _ (pow256_pos pb)

/-- **Exact byte-vector injectivity of `normPtrByteOffset`** for every pointer width
`0 < ptrBytes ≤ 8` (in particular `4` and `8`): two normalized offsets have the same vendored
`PointerFrag.bytes` image iff they are equal. -/
theorem normOffset_image_inj (pb o o' : Nat) (h8 : pb ≤ 8) :
    ptrImage pb (normPtrByteOffset pb o) = ptrImage pb (normPtrByteOffset pb o') ↔
      normPtrByteOffset pb o = normPtrByteOffset pb o' :=
  ptrImage_inj pb _ _ h8 (normPtrByteOffset_lt pb o) (normPtrByteOffset_lt pb o')

/-- The fragments of an encoded pointer are well formed. -/
theorem encodePtrBytes_wf (bits pb a t i : Nat) (b : AbstractByte)
    (h : (encodePtrBytes bits pb a t)[i]? = some b) :
    ∃ v f, b = .init v (some f) ∧ f = ⟨a, t, i, normPtrByteOffset pb bits, pb⟩ ∧ WF pb f := by
  have key : ∀ (n bits' idx : Nat), idx + n = pb → ∀ j b',
      (encodePtrBytesAux a t (normPtrByteOffset pb bits) pb bits' idx n)[j]? = some b' →
        ∃ v, b' = .init v (some ⟨a, t, idx + j, normPtrByteOffset pb bits, pb⟩) ∧ idx + j < pb := by
    intro n
    induction n with
    | zero =>
        intro _ _ _ j b' hj
        cases hj
    | succ n ih =>
        intro bits' idx hn j b' hj
        cases j with
        | zero =>
            have hx : some (AbstractByte.init (UInt8.ofNat bits')
                (some ⟨a, t, idx, normPtrByteOffset pb bits, pb⟩)) = some b' := hj
            injection hx with hx
            exact ⟨_, hx.symm, by omega⟩
        | succ j =>
            have hj' : (encodePtrBytesAux a t (normPtrByteOffset pb bits) pb (Nat.div bits' 256)
                (Nat.add idx 1) n)[j]? = some b' := hj
            obtain ⟨v, hv, hlt⟩ := ih (Nat.div bits' 256) (Nat.add idx 1) (by
              show idx + 1 + n = pb
              omega) j b' hj'
            refine ⟨v, ?_, by
              show idx + (j + 1) < pb
              have : idx + 1 + j < pb := hlt
              omega⟩
            rw [hv]
            have e : Nat.add idx 1 + j = idx + (j + 1) := by
              show idx + 1 + j = idx + (j + 1)
              omega
            rw [e]
  obtain ⟨v, hv, hlt⟩ := key pb bits 0 (by omega) i b h
  rw [Nat.zero_add] at hv hlt
  exact ⟨v, _, hv, rfl, rfl, hlt, normPtrByteOffset_lt pb bits⟩

/-! ### §2. `Trusted` coherence on a fragment-headed stream -/

theorem coh?_isSome (v : UInt8) (f : PtrByteFrag) (rest : List AbstractByte) :
    (abstractBytesCoherentPtrProv? (.init v (some f) :: rest)).isSome =
      Bool.and (Nat.blt 0 f.ptrBytes)
        (Bool.and (Nat.beq f.byteIdx 0)
          (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) := by
  show (match Bool.and (Nat.blt 0 f.ptrBytes)
      (Bool.and (Nat.beq f.byteIdx 0)
        (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) with
    | true => some f
    | false => none).isSome = _
  cases Bool.and (Nat.blt 0 f.ptrBytes)
      (Bool.and (Nat.beq f.byteIdx 0)
        (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) <;> rfl

/-! ### §3.4. Universal correspondence on `4`-byte fragment streams -/

/-- **Exact coherence correspondence on `4` well-formed fragments.** Vendored Miri's in-order
fragment agreement on the translated fragments is exactly `Trusted`'s coherence verdict
(`abstractBytesCoherentPtrProv?`), for any provenance embedding that separates the fragments'
`(allocId, tag)` pairs from that of fragment `0`. -/
theorem coh_iff4 {Prov : Type} [DecidableEq Prov] (pv : Nat → Nat → Prov)
    (v0 v1 v2 v3 : UInt8) (f0 f1 f2 f3 : PtrByteFrag)
    (wf0 : WF 4 f0)
    (wf1 : WF 4 f1)
    (wf2 : WF 4 f2)
    (wf3 : WF 4 f3)
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag) :
    miriCoh [mkFrag pv f0, mkFrag pv f1, mkFrag pv f2, mkFrag pv f3] = (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]).isSome := by
  obtain ⟨p0, i0, o0⟩ := wf0
  obtain ⟨p1, i1, o1⟩ := wf1
  obtain ⟨p2, i2, o2⟩ := wf2
  obtain ⟨p3, i3, o3⟩ := wf3
  have e0 := mkFrag_idx pv f0 (by omega)
  have e1 := mkFrag_idx pv f1 (by omega)
  have e2 := mkFrag_idx pv f2 (by omega)
  have e3 := mkFrag_idx pv f3 (by omega)
  have r1 : (mkFrag pv f1).prov = (mkFrag pv f0).prov ↔ f1.allocId = f0.allocId ∧ f1.tag = f0.tag :=
    ⟨hinj1, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r2 : (mkFrag pv f2).prov = (mkFrag pv f0).prov ↔ f2.allocId = f0.allocId ∧ f2.tag = f0.tag :=
    ⟨hinj2, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r3 : (mkFrag pv f3).prov = (mkFrag pv f0).prov ↔ f3.allocId = f0.allocId ∧ f3.tag = f0.tag :=
    ⟨hinj3, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have m1 : (mkFrag pv f1).bytes = (mkFrag pv f0).bytes ↔ f1.origOffset = f0.origOffset := by
    show ptrImage f1.ptrBytes f1.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p1, p0]
    exact ptrImage_inj 4 _ _ (by decide) o1 o0
  have m2 : (mkFrag pv f2).bytes = (mkFrag pv f0).bytes ↔ f2.origOffset = f0.origOffset := by
    show ptrImage f2.ptrBytes f2.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p2, p0]
    exact ptrImage_inj 4 _ _ (by decide) o2 o0
  have m3 : (mkFrag pv f3).bytes = (mkFrag pv f0).bytes ↔ f3.origOffset = f0.origOffset := by
    show ptrImage f3.ptrBytes f3.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p3, p0]
    exact ptrImage_inj 4 _ _ (by decide) o3 o0
  rw [coh?_isSome]
  apply Bool.eq_iff_iff.mpr
  simp only [miriCoh, miriCohAux, abstractBytesCoherentPtrProvAux, Bool.and_eq_true,
    decide_eq_true_eq, nat_beq_iff, Nat.blt_eq, Nat.add_eq, e0, e1, e2, e3, r1, r2, r3, m1, m2, m3, p0, p1, p2, p3]
  all_goals (constructor <;> intro h <;> simp_all)

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
`4`-byte pointers).** For every stream of `4` well-formed fragment bytes, the vendored read of
the translated fragment state returns `some (pv allocId tag)` exactly when `Trusted` finds the
stream coherent, and no provenance otherwise:
`abstractBytesCoherentPtrProv? bytes = some _ ↔ readPtr … = .ok (some _)` and
`abstractBytesCoherentPtrProv? bytes = none ↔ readPtr … = .ok none`. -/
theorem readPtr4_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (v0 v1 v2 v3 : UInt8) (f0 f1 f2 f3 : PtrByteFrag)
    (wf0 : WF 4 f0)
    (wf1 : WF 4 f1)
    (wf2 : WF 4 f2)
    (wf3 : WF 4 f3)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]) 0 4 =
      .ok (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]).isSome then
        some (pv f0.allocId f0.tag) else none) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] = fe4 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) from rfl,
    readPtr4_runtime _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3,
    coh_iff4 pv v0 v1 v2 v3 f0 f1 f2 f3 wf0 wf1 wf2 wf3 hinj1 hinj2 hinj3]
  rfl

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE strict
partial-pointer mode, `4`-byte pointers).** A coherent stream reads its provenance; every
incoherent stream is the vendored `readPartialPointer` error. -/
theorem readPtr4_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (v0 v1 v2 v3 : UInt8) (f0 f1 f2 f3 : PtrByteFrag)
    (wf0 : WF 4 f0)
    (wf1 : WF 4 f1)
    (wf2 : WF 4 f2)
    (wf3 : WF 4 f3)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]) 0 4 =
      (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]).isSome then
        .ok (some (pv f0.allocId f0.tag)) else .error (.readPartialPointer (Size.ofBytes 0))) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] = fe4 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) from rfl,
    readPtr4_ctfe _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3,
    coh_iff4 pv v0 v1 v2 v3 f0 f1 f2 f3 wf0 wf1 wf2 wf3 hinj1 hinj2 hinj3]
  rfl

/-! ### §3.8. Universal correspondence on `8`-byte fragment streams -/

/-- **Exact coherence correspondence on `8` well-formed fragments.** Vendored Miri's in-order
fragment agreement on the translated fragments is exactly `Trusted`'s coherence verdict
(`abstractBytesCoherentPtrProv?`), for any provenance embedding that separates the fragments'
`(allocId, tag)` pairs from that of fragment `0`. -/
theorem coh_iff8 {Prov : Type} [DecidableEq Prov] (pv : Nat → Nat → Prov)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) (f0 f1 f2 f3 f4 f5 f6 f7 : PtrByteFrag)
    (wf0 : WF 8 f0)
    (wf1 : WF 8 f1)
    (wf2 : WF 8 f2)
    (wf3 : WF 8 f3)
    (wf4 : WF 8 f4)
    (wf5 : WF 8 f5)
    (wf6 : WF 8 f6)
    (wf7 : WF 8 f7)
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag)
    (hinj4 : pv f4.allocId f4.tag = pv f0.allocId f0.tag → f4.allocId = f0.allocId ∧ f4.tag = f0.tag)
    (hinj5 : pv f5.allocId f5.tag = pv f0.allocId f0.tag → f5.allocId = f0.allocId ∧ f5.tag = f0.tag)
    (hinj6 : pv f6.allocId f6.tag = pv f0.allocId f0.tag → f6.allocId = f0.allocId ∧ f6.tag = f0.tag)
    (hinj7 : pv f7.allocId f7.tag = pv f0.allocId f0.tag → f7.allocId = f0.allocId ∧ f7.tag = f0.tag) :
    miriCoh [mkFrag pv f0, mkFrag pv f1, mkFrag pv f2, mkFrag pv f3, mkFrag pv f4, mkFrag pv f5, mkFrag pv f6, mkFrag pv f7] = (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]).isSome := by
  obtain ⟨p0, i0, o0⟩ := wf0
  obtain ⟨p1, i1, o1⟩ := wf1
  obtain ⟨p2, i2, o2⟩ := wf2
  obtain ⟨p3, i3, o3⟩ := wf3
  obtain ⟨p4, i4, o4⟩ := wf4
  obtain ⟨p5, i5, o5⟩ := wf5
  obtain ⟨p6, i6, o6⟩ := wf6
  obtain ⟨p7, i7, o7⟩ := wf7
  have e0 := mkFrag_idx pv f0 (by omega)
  have e1 := mkFrag_idx pv f1 (by omega)
  have e2 := mkFrag_idx pv f2 (by omega)
  have e3 := mkFrag_idx pv f3 (by omega)
  have e4 := mkFrag_idx pv f4 (by omega)
  have e5 := mkFrag_idx pv f5 (by omega)
  have e6 := mkFrag_idx pv f6 (by omega)
  have e7 := mkFrag_idx pv f7 (by omega)
  have r1 : (mkFrag pv f1).prov = (mkFrag pv f0).prov ↔ f1.allocId = f0.allocId ∧ f1.tag = f0.tag :=
    ⟨hinj1, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r2 : (mkFrag pv f2).prov = (mkFrag pv f0).prov ↔ f2.allocId = f0.allocId ∧ f2.tag = f0.tag :=
    ⟨hinj2, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r3 : (mkFrag pv f3).prov = (mkFrag pv f0).prov ↔ f3.allocId = f0.allocId ∧ f3.tag = f0.tag :=
    ⟨hinj3, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r4 : (mkFrag pv f4).prov = (mkFrag pv f0).prov ↔ f4.allocId = f0.allocId ∧ f4.tag = f0.tag :=
    ⟨hinj4, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r5 : (mkFrag pv f5).prov = (mkFrag pv f0).prov ↔ f5.allocId = f0.allocId ∧ f5.tag = f0.tag :=
    ⟨hinj5, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r6 : (mkFrag pv f6).prov = (mkFrag pv f0).prov ↔ f6.allocId = f0.allocId ∧ f6.tag = f0.tag :=
    ⟨hinj6, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r7 : (mkFrag pv f7).prov = (mkFrag pv f0).prov ↔ f7.allocId = f0.allocId ∧ f7.tag = f0.tag :=
    ⟨hinj7, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have m1 : (mkFrag pv f1).bytes = (mkFrag pv f0).bytes ↔ f1.origOffset = f0.origOffset := by
    show ptrImage f1.ptrBytes f1.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p1, p0]
    exact ptrImage_inj 8 _ _ (by decide) o1 o0
  have m2 : (mkFrag pv f2).bytes = (mkFrag pv f0).bytes ↔ f2.origOffset = f0.origOffset := by
    show ptrImage f2.ptrBytes f2.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p2, p0]
    exact ptrImage_inj 8 _ _ (by decide) o2 o0
  have m3 : (mkFrag pv f3).bytes = (mkFrag pv f0).bytes ↔ f3.origOffset = f0.origOffset := by
    show ptrImage f3.ptrBytes f3.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p3, p0]
    exact ptrImage_inj 8 _ _ (by decide) o3 o0
  have m4 : (mkFrag pv f4).bytes = (mkFrag pv f0).bytes ↔ f4.origOffset = f0.origOffset := by
    show ptrImage f4.ptrBytes f4.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p4, p0]
    exact ptrImage_inj 8 _ _ (by decide) o4 o0
  have m5 : (mkFrag pv f5).bytes = (mkFrag pv f0).bytes ↔ f5.origOffset = f0.origOffset := by
    show ptrImage f5.ptrBytes f5.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p5, p0]
    exact ptrImage_inj 8 _ _ (by decide) o5 o0
  have m6 : (mkFrag pv f6).bytes = (mkFrag pv f0).bytes ↔ f6.origOffset = f0.origOffset := by
    show ptrImage f6.ptrBytes f6.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p6, p0]
    exact ptrImage_inj 8 _ _ (by decide) o6 o0
  have m7 : (mkFrag pv f7).bytes = (mkFrag pv f0).bytes ↔ f7.origOffset = f0.origOffset := by
    show ptrImage f7.ptrBytes f7.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p7, p0]
    exact ptrImage_inj 8 _ _ (by decide) o7 o0
  rw [coh?_isSome]
  apply Bool.eq_iff_iff.mpr
  simp only [miriCoh, miriCohAux, abstractBytesCoherentPtrProvAux, Bool.and_eq_true,
    decide_eq_true_eq, nat_beq_iff, Nat.blt_eq, Nat.add_eq, e0, e1, e2, e3, e4, e5, e6, e7, r1, r2, r3, r4, r5, r6, r7, m1, m2, m3, m4, m5, m6, m7, p0, p1, p2, p3, p4, p5, p6, p7]
  all_goals (constructor <;> intro h <;> simp_all)

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
`8`-byte pointers).** For every stream of `8` well-formed fragment bytes, the vendored read of
the translated fragment state returns `some (pv allocId tag)` exactly when `Trusted` finds the
stream coherent, and no provenance otherwise:
`abstractBytesCoherentPtrProv? bytes = some _ ↔ readPtr … = .ok (some _)` and
`abstractBytesCoherentPtrProv? bytes = none ↔ readPtr … = .ok none`. -/
theorem readPtr8_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) (f0 f1 f2 f3 f4 f5 f6 f7 : PtrByteFrag)
    (wf0 : WF 8 f0)
    (wf1 : WF 8 f1)
    (wf2 : WF 8 f2)
    (wf3 : WF 8 f3)
    (wf4 : WF 8 f4)
    (wf5 : WF 8 f5)
    (wf6 : WF 8 f6)
    (wf7 : WF 8 f7)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw4 : ¬ some (pv f4.allocId f4.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw5 : ¬ some (pv f5.allocId f5.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw6 : ¬ some (pv f6.allocId f6.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw7 : ¬ some (pv f7.allocId f7.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag)
    (hinj4 : pv f4.allocId f4.tag = pv f0.allocId f0.tag → f4.allocId = f0.allocId ∧ f4.tag = f0.tag)
    (hinj5 : pv f5.allocId f5.tag = pv f0.allocId f0.tag → f5.allocId = f0.allocId ∧ f5.tag = f0.tag)
    (hinj6 : pv f6.allocId f6.tag = pv f0.allocId f0.tag → f6.allocId = f0.allocId ∧ f6.tag = f0.tag)
    (hinj7 : pv f7.allocId f7.tag = pv f0.allocId f0.tag → f7.allocId = f0.allocId ∧ f7.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]) 0 8 =
      .ok (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]).isSome then
        some (pv f0.allocId f0.tag) else none) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] = fe8 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) (mkFrag pv f4) (mkFrag pv f5) (mkFrag pv f6) (mkFrag pv f7) from rfl,
    readPtr8_runtime _ _ _ _ _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3 hnw4 hnw5 hnw6 hnw7,
    coh_iff8 pv v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7 wf0 wf1 wf2 wf3 wf4 wf5 wf6 wf7 hinj1 hinj2 hinj3 hinj4 hinj5 hinj6 hinj7]
  rfl

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE strict
partial-pointer mode, `8`-byte pointers).** A coherent stream reads its provenance; every
incoherent stream is the vendored `readPartialPointer` error. -/
theorem readPtr8_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) (f0 f1 f2 f3 f4 f5 f6 f7 : PtrByteFrag)
    (wf0 : WF 8 f0)
    (wf1 : WF 8 f1)
    (wf2 : WF 8 f2)
    (wf3 : WF 8 f3)
    (wf4 : WF 8 f4)
    (wf5 : WF 8 f5)
    (wf6 : WF 8 f6)
    (wf7 : WF 8 f7)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw4 : ¬ some (pv f4.allocId f4.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw5 : ¬ some (pv f5.allocId f5.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw6 : ¬ some (pv f6.allocId f6.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw7 : ¬ some (pv f7.allocId f7.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag)
    (hinj4 : pv f4.allocId f4.tag = pv f0.allocId f0.tag → f4.allocId = f0.allocId ∧ f4.tag = f0.tag)
    (hinj5 : pv f5.allocId f5.tag = pv f0.allocId f0.tag → f5.allocId = f0.allocId ∧ f5.tag = f0.tag)
    (hinj6 : pv f6.allocId f6.tag = pv f0.allocId f0.tag → f6.allocId = f0.allocId ∧ f6.tag = f0.tag)
    (hinj7 : pv f7.allocId f7.tag = pv f0.allocId f0.tag → f7.allocId = f0.allocId ∧ f7.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]) 0 8 =
      (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]).isSome then
        .ok (some (pv f0.allocId f0.tag)) else .error (.readPartialPointer (Size.ofBytes 0))) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] = fe8 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) (mkFrag pv f4) (mkFrag pv f5) (mkFrag pv f6) (mkFrag pv f7) from rfl,
    readPtr8_ctfe _ _ _ _ _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3 hnw4 hnw5 hnw6 hnw7,
    coh_iff8 pv v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7 wf0 wf1 wf2 wf3 wf4 wf5 wf6 wf7 hinj1 hinj2 hinj3 hinj4 hinj5 hinj6 hinj7]
  rfl


/-! ### §4. Fixtures and kernel-checked witnesses -/

section Witnesses

open Trusted.Rustc.V2026_06_01.Layout

/-- `p = alloc 7 + 0x1000` (64-bit). -/
def lP : List AbstractByte := encodePtrBytes 0x1000 8 7 7
/-- `p + 4`. -/
def lP4 : List AbstractByte := encodePtrBytes 0x1004 8 7 7
/-- `p + 256`: byte 0 is `0x00`, exactly as in `p`. -/
def lP256 : List AbstractByte := encodePtrBytes 0x1100 8 7 7
/-- The all-zero image `alloc 7 + 0`. -/
def lZ : List AbstractByte := encodePtrBytes 0 8 7 7
/-- A pointer into another allocation. -/
def lO : List AbstractByte := encodePtrBytes 0x1000 8 8 8
/-- `q = alloc 9 + 0x1000` (32-bit). -/
def lQ : List AbstractByte := encodePtrBytes 0x1000 4 9 9
/-- `q + 256` (32-bit). -/
def lQ256 : List AbstractByte := encodePtrBytes 0x1100 4 9 9

/-- **Three-way witness: the intact pointer `p`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_intact :
    lP = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .ok (some (pvCt 7 7)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.ptr ⟨7, 4096⟩ 8) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.ptr ⟨7, 4096⟩ 8) :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 8-byte full reversal of the all-zero image of offset `0`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_zero_reversal :
    lZ.reverse = [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)] = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 7, 0, 8⟩ ⟨7, 7, 6, 0, 8⟩ ⟨7, 7, 5, 0, 8⟩ ⟨7, 7, 4, 0, 8⟩ ⟨7, 7, 3, 0, 8⟩ ⟨7, 7, 2, 0, 8⟩ ⟨7, 7, 1, 0, 8⟩ ⟨7, 7, 0, 0, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 7, 0, 8⟩ ⟨7, 7, 6, 0, 8⟩ ⟨7, 7, 5, 0, 8⟩ ⟨7, 7, 4, 0, 8⟩ ⟨7, 7, 3, 0, 8⟩ ⟨7, 7, 2, 0, 8⟩ ⟨7, 7, 1, 0, 8⟩ ⟨7, 7, 0, 0, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 8-byte full reversal of `p`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_reversal :
    lP.reverse = [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = some (.scalar ⟨4503599627370496, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 0 0 0 0 0 16 0 ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 0 0 0 0 0 16 0 ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the byte-0 / byte-1 swap.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_swap01 :
    (lP.take 2).reverse ++ lP.drop 2 = [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.scalar ⟨16, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: byte 0 of `p` repeated 8×.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_dup_head :
    List.replicate 8 (lP.headD .uninit) = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: a non-identity permutation (rotation by one byte).** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_rotate :
    lP.drop 1 ++ lP.take 1 = [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = some (.scalar ⟨16, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the `p` / `p + 4` offset splice.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_splice_p_p4 :
    lP.take 4 ++ lP4.drop 4 = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)] = some (.scalar ⟨4096, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4100, 8⟩ ⟨7, 7, 5, 4100, 8⟩ ⟨7, 7, 6, 4100, 8⟩ ⟨7, 7, 7, 4100, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4100, 8⟩ ⟨7, 7, 5, 4100, 8⟩ ⟨7, 7, 6, 4100, 8⟩ ⟨7, 7, 7, 4100, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the `p` / `p + 256` offset splice (byte 0 is `0x00` in both pointers).** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_splice_p_p256 :
    lP.take 1 ++ lP256.drop 1 = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)] = some (.scalar ⟨4352, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 17 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4352, 8⟩ ⟨7, 7, 2, 4352, 8⟩ ⟨7, 7, 3, 4352, 8⟩ ⟨7, 7, 4, 4352, 8⟩ ⟨7, 7, 5, 4352, 8⟩ ⟨7, 7, 6, 4352, 8⟩ ⟨7, 7, 7, 4352, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 17 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4352, 8⟩ ⟨7, 7, 2, 4352, 8⟩ ⟨7, 7, 3, 4352, 8⟩ ⟨7, 7, 4, 4352, 8⟩ ⟨7, 7, 5, 4352, 8⟩ ⟨7, 7, 6, 4352, 8⟩ ⟨7, 7, 7, 4352, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: a mixed-provenance (two allocations) splice.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_mixed_alloc :
    lP.take 4 ++ lO.drop 4 = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)] = some (.scalar ⟨4096, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨8, 8, 4, 4096, 8⟩ ⟨8, 8, 5, 4096, 8⟩ ⟨8, 8, 6, 4096, 8⟩ ⟨8, 8, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨8, 8, 4, 4096, 8⟩ ⟨8, 8, 5, 4096, 8⟩ ⟨8, 8, 6, 4096, 8⟩ ⟨8, 8, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the intact 32-bit pointer `q`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_intact32 :
    lQ = [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)]) 0 4 = .ok (some (pvRt 9 9)) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)]) 0 4 = .ok (some (pvCt 9 9)) ∧
    decodePtrBytesNoForge false (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)] = some (.ptr ⟨9, 4096⟩ 4) ∧
    decodePtrBytesNoForge true (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)] = some (.ptr ⟨9, 4096⟩ 4) :=
  ⟨rfl, (readPtr4_runtime_corr pvRt rfl 0 16 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 3, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr4_ctfe_corr pvCt rfl 0 16 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 3, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 4-byte full reversal of `q`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_reversal32 :
    lQ.reverse = [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)]) 0 4 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)]) 0 4 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 4 [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)] = some (.scalar ⟨1048576, 4⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 4 [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)] = none :=
  ⟨rfl, (readPtr4_runtime_corr pvRt rfl 0 0 16 0 ⟨9, 9, 3, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 0, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr4_ctfe_corr pvCt rfl 0 0 16 0 ⟨9, 9, 3, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 0, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 32-bit `q` / `q + 256` offset splice.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_splice32_q_q256 :
    lQ.take 1 ++ lQ256.drop 1 = [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)]) 0 4 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)]) 0 4 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)] = some (.scalar ⟨4352, 4⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)] = none :=
  ⟨rfl, (readPtr4_runtime_corr pvRt rfl 0 17 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4352, 4⟩ ⟨9, 9, 2, 4352, 4⟩ ⟨9, 9, 3, 4352, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr4_ctfe_corr pvCt rfl 0 17 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4352, 4⟩ ⟨9, 9, 2, 4352, 4⟩ ⟨9, 9, 3, 4352, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Missing provenance and uninitialized bytes.** A plain byte (or an uninitialized byte)
contributes no fragment, so the translated state is the shared `entriesMissing1`, which vendored
`readPtr` reads without provenance (runtime) / as a partial pointer (CTFE); `Trusted` reads a raw
pointer as a plain integer, rejects a reference, and rejects the uninitialized stream outright. -/
theorem w_lm_missing_and_uninit :
    trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = entriesMissing1 pvRt ∧
    trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .uninit, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = entriesMissing1 pvRt ∧
    trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = entriesMissing1 pvCt ∧
    trRead (entriesMissing1 pvRt) 0 8 = .ok none ∧
    trRead (entriesMissing1 pvCt) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.scalar ⟨4096, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = none ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .uninit, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = none :=
  ⟨rfl, rfl, rfl, w_lm_missing_miri_rt, w_lm_missing_miri_ct, rfl, rfl, rfl⟩

def wUnitL : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
def wU8L : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wCharL : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wU32L : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L] }
def wTyU8 : Ty := { kind := .uint .u8, layoutIdx := 1 }
def wTyBool : Ty := { kind := .bool, layoutIdx := 2 }
def wTyChar : Ty := { kind := .char, layoutIdx := 3 }
def wTyU32 : Ty := { kind := .uint .u32, layoutIdx := 4 }

/-- **`Kani#5205` (`Trusted` half).** `2u8` and the surrogate `0xD800` are representable as
untyped bytes (`u8`, `u32`, the raw-byte carrier) — writing them is not UB — and are rejected
(`none`, the `.ub` read fault) by the typed `bool` / `char` decode; the vendored Miri half is
`w_lm_kani5205_miri`. -/
theorem w_lm_kani5205_trusted :
    encodeUntypedValueToBytes 1 (.scalar ⟨2, 1⟩) = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU8 [.init 2 none] =
      some (.scalar ⟨2, 1⟩) ∧
    decodeRawAbstractByteVals? [encodeRawAbstractByteVal (.init 2 none)] = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 2 none] = none ∧
    validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨2, 1⟩) = false ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 1 none] =
      some (.scalar ⟨1, 1⟩) ∧
    encodeUntypedValueToBytes 1 (.scalar ⟨0xD800, 4⟩) =
      some [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU32
      [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none] =
      some (.scalar ⟨0xD800, 4⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar
      [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none] = none ∧
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = false := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- Non-vacuous instantiations of the byte-vector injectivity law (`4` and `8` bytes). -/
theorem normOffset_image_inj_instance :
    ptrImage 8 (normPtrByteOffset 8 0x1000) ≠ ptrImage 8 (normPtrByteOffset 8 0x1100) ∧
    ptrImage 4 (normPtrByteOffset 4 0x1000) ≠ ptrImage 4 (normPtrByteOffset 4 0x1100) ∧
    ptrImage 4 (normPtrByteOffset 4 0x1000) = ptrImage 4 (normPtrByteOffset 4 0x100001000) :=
  ⟨fun h => absurd ((normOffset_image_inj 8 _ _ (by decide)).mp h) (by decide),
   fun h => absurd ((normOffset_image_inj 4 _ _ (by decide)).mp h) (by decide),
   (normOffset_image_inj 4 _ _ (by decide)).mpr (by decide)⟩

end Witnesses

/-! ### §5. Truly universal all-bytes correspondence (including plain & `.uninit` bytes), intact & carrier round-trips, wide pointers, and universal / end-to-end `Kani#5205` -/

theorem trEntriesAux_keys_ge {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte) (e : Size × PointerFrag Prov),
      start + bs.length < 2 ^ 64 →
      e ∈ trEntriesAux pv start bs →
      start ≤ e.1.bytes.toNat ∧ e.1.bytes.toNat < start + bs.length
  | _, [], _, _, h => by cases h
  | start, b :: rest, e, hbd, h => by
    simp only [trEntriesAux] at h
    cases hf : fragOf pv b with
    | none =>
      rw [hf] at h
      have ih := trEntriesAux_keys_ge pv (start + 1) rest e (by simp only [List.length_cons] at hbd; omega) h
      simp only [List.length_cons]; omega
    | some g =>
      rw [hf] at h
      cases h with
      | head =>
        simp only [Size.ofBytes, UInt64.toNat_ofNat', List.length_cons]
        have : start < 2 ^ 64 := by simp only [List.length_cons] at hbd; omega
        rw [Nat.mod_eq_of_lt this]; omega
      | tail _ hr =>
        have ih := trEntriesAux_keys_ge pv (start + 1) rest e (by simp only [List.length_cons] at hbd; omega) hr
        simp only [List.length_cons]; omega

theorem trEntriesAux_sorted {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte),
      start + bs.length < 2 ^ 64 →
      ∃ pm, ProvenanceMap.fromParts #[] (some (trEntriesAux pv start bs).toArray) = .ok pm := by
  intro start bs hbd
  have hsorted : ∀ (s : Nat) (l : List AbstractByte), s + l.length < 2 ^ 64 →
      (ProvenanceMap.fromParts #[] (some (trEntriesAux pv s l).toArray)).isOk = true := by
    intro s l
    induction l generalizing s with
    | nil =>
      intro _
      unfold ProvenanceMap.fromParts
      simp only [trEntriesAux, Option.map_some, Option.getD_some, Array.toList_empty, List.toList_toArray]
      simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
      rfl
    | cons b rest ih =>
      intro hbd'
      simp only [trEntriesAux]
      cases hf : fragOf pv b with
      | none => exact ih (s + 1) (by simp only [List.length_cons] at hbd'; omega)
      | some g =>
        have ih' := ih (s + 1) (by simp only [List.length_cons] at hbd'; omega)
        unfold ProvenanceMap.fromParts at ih' ⊢
        simp only [Option.map_some, Option.getD_some, Array.toList_empty, List.toList_toArray] at ih' ⊢
        cases hrest : trEntriesAux pv (s + 1) rest with
        | nil =>
          simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
          rfl
        | cons hd tl =>
          have hge := trEntriesAux_keys_ge pv (s + 1) rest hd
            (by simp only [List.length_cons] at hbd'; omega) (by rw [hrest]; exact List.Mem.head _)
          have hs_lt : s < 2 ^ 64 := by simp only [List.length_cons] at hbd'; omega
          obtain ⟨hd_s, hd_f⟩ := hd
          dsimp only at hge
          have hlt : (Size.ofBytes (UInt64.ofNat s)).bytes < hd_s.bytes := by
            simp only [Size.ofBytes, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hs_lt]
            omega
          rw [hrest] at ih'
          split at ih'
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
            simp [hlt, hcond.2]
            rfl
          · cases ih'
  have hok := hsorted start bs hbd
  cases h : ProvenanceMap.fromParts #[] (some (trEntriesAux pv start bs).toArray) with
  | ok pm => exact ⟨pm, rfl⟩
  | error e => rw [h] at hok; cases hok

theorem mem_trEntriesAux_iff {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte) (e : Size × PointerFrag Prov),
      start + bs.length < 2 ^ 64 →
      (e ∈ trEntriesAux pv start bs ↔
        ∃ (i : Nat) (b : AbstractByte) (g : PointerFrag Prov),
          bs[i]? = some b ∧ fragOf pv b = some g ∧
          e = (Size.ofBytes (UInt64.ofNat (start + i)), g))
  | _, [], e, _ => by
    simp [trEntriesAux]
  | start, b :: rest, e, hbd => by
    simp only [trEntriesAux]
    have hbd' : start + 1 + rest.length < 2 ^ 64 := by simp only [List.length_cons] at hbd; omega
    cases hf : fragOf pv b with
    | none =>
      rw [mem_trEntriesAux_iff pv (start + 1) rest e hbd']
      constructor
      · rintro ⟨i, b', g, hget, hfg, rfl⟩
        refine ⟨i + 1, b', g, hget, hfg, ?_⟩
        have : start + 1 + i = start + (i + 1) := by omega
        rw [this]
      · rintro ⟨i, b', g, hget, hfg, rfl⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hget; subst hget; rw [hf] at hfg; cases hfg
        | succ j =>
          refine ⟨j, b', g, hget, hfg, ?_⟩
          have : start + (j + 1) = start + 1 + j := by omega
          rw [this]
    | some g0 =>
      simp only [List.mem_cons]
      rw [mem_trEntriesAux_iff pv (start + 1) rest e hbd']
      constructor
      · rintro (rfl | ⟨i, b', g, hget, hfg, rfl⟩)
        · exact ⟨0, b, g0, rfl, hf, by simp⟩
        · refine ⟨i + 1, b', g, hget, hfg, ?_⟩
          have : start + 1 + i = start + (i + 1) := by omega
          rw [this]
      · rintro ⟨i, b', g, hget, hfg, rfl⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hget; subst hget; rw [hf] at hfg
          injection hfg with hfg; subst hfg; left; simp
        | succ j =>
          right
          refine ⟨j, b', g, hget, hfg, ?_⟩
          have : start + (j + 1) = start + 1 + j := by omega
          rw [this]

theorem trEntries_eq_empty_of_no_prov {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte),
      abstractBytesHaveProv bs = false → trEntriesAux pv start bs = []
  | _, [], _ => rfl
  | start, .uninit :: rest, h => trEntries_eq_empty_of_no_prov pv (start + 1) rest h
  | start, .init _ none :: rest, h => trEntries_eq_empty_of_no_prov pv (start + 1) rest h
  | _, .init _ (some _) :: _, h => by cases h

theorem exists_prov_of_haveProv :
    ∀ (bs : List AbstractByte),
      abstractBytesHaveProv bs = true →
      ∃ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f))
  | [], h => by cases h
  | .uninit :: rest, h => by
    obtain ⟨i, v, f, hi⟩ := exists_prov_of_haveProv rest h
    exact ⟨i + 1, v, f, hi⟩
  | .init _ none :: rest, h => by
    obtain ⟨i, v, f, hi⟩ := exists_prov_of_haveProv rest h
    exact ⟨i + 1, v, f, hi⟩
  | .init v (some f) :: _, _ => ⟨0, v, f, rfl⟩

theorem coh?_none_of_no_frag :
    ∀ (bs : List AbstractByte) (i : Nat) (b : AbstractByte),
      bs[i]? = some b → (∀ v f, b ≠ .init v (some f)) →
      abstractBytesCoherentPtrProv? bs = none := by
  have aux : ∀ (a t o pb idx : Nat) (bs : List AbstractByte) (i : Nat) (b : AbstractByte),
      bs[i]? = some b → (∀ v f, b ≠ .init v (some f)) →
      abstractBytesCoherentPtrProvAux a t o pb idx bs = false := by
    intro a t o pb idx bs
    induction bs generalizing idx with
    | nil => intro i b h; cases h
    | cons x rest ih =>
      intro i b h hnf
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at h
        injection h with h; subst h
        cases x with
        | uninit => rfl
        | init v pr =>
          cases pr with
          | none => rfl
          | some f => exact absurd rfl (hnf v f)
      | succ j =>
        cases x with
        | uninit => rfl
        | init v pr =>
          cases pr with
          | none => rfl
          | some f =>
            show Bool.and _ (abstractBytesCoherentPtrProvAux a t o pb (Nat.add idx 1) rest) = false
            rw [ih (Nat.add idx 1) j b h hnf]
            simp
  intro bs i b h hnf
  cases bs with
  | nil => cases h
  | cons x rest =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at h
      injection h with h; subst h
      cases x with
      | uninit => rfl
      | init v pr =>
        cases pr with
        | none => rfl
        | some f => exact absurd rfl (hnf v f)
    | succ j =>
      cases x with
      | uninit => rfl
      | init v pr =>
        cases pr with
        | none => rfl
        | some f =>
          show (match Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) with
            | true => some f | false => none) = none
          rw [aux f.allocId f.tag f.origOffset f.ptrBytes 1 rest j b h hnf]
          simp

/-- Helper: decompose any `n`-byte stream into either all-fragmented or containing a plain/`.uninit` byte. -/
theorem list_all_frag_or_missing (bs : List AbstractByte) :
    (∀ (i : Nat) (b : AbstractByte), bs[i]? = some b → ∃ v f, b = .init v (some f)) ∨
    (∃ (i : Nat) (b : AbstractByte), i < bs.length ∧ bs[i]? = some b ∧ ∀ v f, b ≠ .init v (some f)) := by
  induction bs with
  | nil => left; intro i b h; cases h
  | cons x rest ih =>
    cases x with
    | uninit =>
      right; exact ⟨0, .uninit, by simp, rfl, fun _ _ h => by cases h⟩
    | init v pr =>
      cases pr with
      | none =>
        right; exact ⟨0, .init v none, by simp, rfl, fun _ _ h => by injection h with _ h; cases h⟩
      | some f =>
        rcases ih with hall | ⟨i, b, hlt, hb, hnf⟩
        · left
          intro i b hb
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero] at hb
            injection hb with hb; subst hb; exact ⟨v, f, rfl⟩
          | succ j => exact hall j b hb
        · right
          exact ⟨i + 1, b, by simp; omega, hb, hnf⟩

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
4-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr4_allBytes_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 4 =
      .ok ((abstractBytesCoherentPtrProv? bs).map fun f => pv f.allocId f.tag) := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    have hcorr := readPtr4_runtime_corr pv hoff v0 v1 v2 v3 f0 f1 f2 f3
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]
    dsimp only [Option.map]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]
      exact trRead_empty 4 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries
      rw [hpm]
      dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 4 := by
        cases Nat.lt_or_ge j 4 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq
        rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 4 := by
          cases Nat.lt_or_ge i 4 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq
          simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this
          exact this
        subst hik
        rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr =>
          cases pr with
          | none => cases hfg
          | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 4 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]
        simpa using hjlt
      have hread := readPtr4_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE mode,
4-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr4_allBytes_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 4 =
      match abstractBytesCoherentPtrProv? bs with
      | some f => .ok (some (pv f.allocId f.tag))
      | none =>
        if abstractBytesHaveProv bs then .error (.readPartialPointer (Size.ofBytes 0))
        else .ok none := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    have hcorr := readPtr4_ctfe_corr pv hoff v0 v1 v2 v3 f0 f1 f2 f3
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]; exact trRead_empty 4 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries
      rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 4 := by
        cases Nat.lt_or_ge j 4 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq
        rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 4 := by
          cases Nat.lt_or_ge i 4 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 4 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr4_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
8-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr8_allBytes_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 8 =
      .ok ((abstractBytesCoherentPtrProv? bs).map fun f => pv f.allocId f.tag) := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    obtain ⟨v4, f4, rfl⟩ := hall 4 b4 rfl
    obtain ⟨v5, f5, rfl⟩ := hall 5 b5 rfl
    obtain ⟨v6, f6, rfl⟩ := hall 6 b6 rfl
    obtain ⟨v7, f7, rfl⟩ := hall 7 b7 rfl
    have hcorr := readPtr8_runtime_corr pv hoff v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hwf 4 _ _ rfl) (hwf 5 _ _ rfl) (hwf 6 _ _ rfl) (hwf 7 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hnw 4 _ _ rfl) (hnw 5 _ _ rfl) (hnw 6 _ _ rfl) (hnw 7 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
      (hinj 4 0 _ _ _ _ rfl rfl) (hinj 5 0 _ _ _ _ rfl rfl) (hinj 6 0 _ _ _ _ rfl rfl)
      (hinj 7 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]
    dsimp only [Option.map]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]
      exact trRead_empty 8 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries
      rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 8 := by
        cases Nat.lt_or_ge j 8 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq
        rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 8 := by
          cases Nat.lt_or_ge i 8 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 8 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr8_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE mode,
8-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr8_allBytes_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 8 =
      match abstractBytesCoherentPtrProv? bs with
      | some f => .ok (some (pv f.allocId f.tag))
      | none =>
        if abstractBytesHaveProv bs then .error (.readPartialPointer (Size.ofBytes 0))
        else .ok none := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    obtain ⟨v4, f4, rfl⟩ := hall 4 b4 rfl
    obtain ⟨v5, f5, rfl⟩ := hall 5 b5 rfl
    obtain ⟨v6, f6, rfl⟩ := hall 6 b6 rfl
    obtain ⟨v7, f7, rfl⟩ := hall 7 b7 rfl
    have hcorr := readPtr8_ctfe_corr pv hoff v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hwf 4 _ _ rfl) (hwf 5 _ _ rfl) (hwf 6 _ _ rfl) (hwf 7 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hnw 4 _ _ rfl) (hnw 5 _ _ rfl) (hnw 6 _ _ rfl) (hnw 7 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
      (hinj 4 0 _ _ _ _ rfl rfl) (hinj 5 0 _ _ _ _ rfl rfl) (hinj 6 0 _ _ _ _ rfl rfl)
      (hinj 7 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]; exact trRead_empty 8 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries
      rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 8 := by
        cases Nat.lt_or_ge j 8 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq
        rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 8 := by
          cases Nat.lt_or_ge i 8 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 8 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr8_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- Explicit biconditional form of `readPtr8_allBytes_runtime_corr`:
`(∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔ (∃ p, trRead (trEntries pv bs) 0 8 = .ok (some p))`
and `abstractBytesCoherentPtrProv? bs = none ↔ trRead (trEntries pv bs) 0 8 = .ok none`. -/
theorem readPtr8_allBytes_runtime_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 8 = .ok (some p)) ∧
    (abstractBytesCoherentPtrProv? bs = none ↔
      trRead (trEntries pv bs) 0 8 = .ok none) := by
  have h := readPtr8_allBytes_runtime_corr pv hoff bs hlen hwf hnw hinj
  rw [h]
  cases abstractBytesCoherentPtrProv? bs with
  | none => simp
  | some f => simp

/-- Explicit biconditional form of `readPtr4_allBytes_runtime_corr` (32-bit). -/
theorem readPtr4_allBytes_runtime_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 4 = .ok (some p)) ∧
    (abstractBytesCoherentPtrProv? bs = none ↔
      trRead (trEntries pv bs) 0 4 = .ok none) := by
  have h := readPtr4_allBytes_runtime_corr pv hoff bs hlen hwf hnw hinj
  rw [h]
  cases abstractBytesCoherentPtrProv? bs with
  | none => simp
  | some f => simp

/-- **Explicit CTFE biconditionals (`8`-byte pointers).** In CTFE strict partial-pointer mode,
vendored `readPtr` of the translated state retains provenance iff `Trusted` finds the stream
coherent; it is the `readPartialPointer` error iff the stream is incoherent but carries some
provenance fragment; and it is `.ok none` iff the stream carries no provenance fragment at all. -/
theorem readPtr8_allBytes_ctfe_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 8 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = true) ↔
      trRead (trEntries pv bs) 0 8 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = false) ↔
      trRead (trEntries pv bs) 0 8 = .ok none) := by
  rw [readPtr8_allBytes_ctfe_corr pv hoff bs hlen hwf hnw hinj]
  cases abstractBytesCoherentPtrProv? bs with
  | none => cases abstractBytesHaveProv bs <;> simp
  | some f => cases abstractBytesHaveProv bs <;> simp

/-- **Explicit CTFE biconditionals (`4`-byte pointers).** In CTFE strict partial-pointer mode,
vendored `readPtr` of the translated state retains provenance iff `Trusted` finds the stream
coherent; it is the `readPartialPointer` error iff the stream is incoherent but carries some
provenance fragment; and it is `.ok none` iff the stream carries no provenance fragment at all. -/
theorem readPtr4_allBytes_ctfe_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 4 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = true) ↔
      trRead (trEntries pv bs) 0 4 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = false) ↔
      trRead (trEntries pv bs) 0 4 = .ok none) := by
  rw [readPtr4_allBytes_ctfe_corr pv hoff bs hlen hwf hnw hinj]
  cases abstractBytesCoherentPtrProv? bs with
  | none => cases abstractBytesHaveProv bs <;> simp
  | some f => cases abstractBytesHaveProv bs <;> simp

/-- Helper: decoding LE bits of `encodePtrBytesAux` yields `bits % 256 ^ n`. -/
theorem decodeLittleEndianBits_encodePtrBytesAux (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      decodeLittleEndianBits (encodePtrBytesAux a t o pb bits idx n) = some (bits % 256 ^ n)
  | 0, bits, _ => by simp [decodeLittleEndianBits, encodePtrBytesAux, Nat.mod_one]
  | n + 1, bits, idx => by
    show (match decodeLittleEndianBits (encodePtrBytesAux a t o pb (bits / 256) (idx + 1) n) with
      | some hi => some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 hi))
      | none => none) = some (bits % 256 ^ (n + 1))
    rw [decodeLittleEndianBits_encodePtrBytesAux a t o pb n (bits / 256) (idx + 1)]
    show some ((UInt8.ofNat bits).toNat + 256 * (bits / 256 % 256 ^ n)) = some (bits % 256 ^ (n + 1))
    rw [u8_ofNat_toNat, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

/-- Helper: `encodeRawAbstractByteVal` / `decodeRawAbstractByteVals?` round-trips losslessly. -/
theorem rawCarrier_roundtrip_lm :
    ∀ bs : List AbstractByte,
      decodeRawAbstractByteVals? (bs.map encodeRawAbstractByteVal) = some bs
  | [] => rfl
  | .uninit :: rest => by
    show (match some AbstractByte.uninit, decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
      | some b', some bs' => some (b' :: bs') | _, _ => none) = _
    rw [rawCarrier_roundtrip_lm rest]
  | .init v none :: rest => by
    have h1 : decodeRawAbstractByteVal? (encodeRawAbstractByteVal (.init v none)) = some (.init v none) := by
      show decodeRawAbstractByteVal? (.scalar ⟨v.toBitVec.toNat, 1⟩) = _
      unfold decodeRawAbstractByteVal?
      split <;> simp_all <;> (rename_i hb; subst hb; exact UInt8.ofNat_toNat)
    show (match decodeRawAbstractByteVal? (encodeRawAbstractByteVal (.init v none)),
        decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
      | some b', some bs' => some (b' :: bs') | _, _ => none) = _
    rw [h1, rawCarrier_roundtrip_lm rest]
  | .init v (some f) :: rest => by
    have hv : UInt8.ofNat v.toBitVec.toNat = v := UInt8.ofNat_toNat
    show (match some (AbstractByte.init (UInt8.ofNat v.toBitVec.toNat) (some f)),
        decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
      | some b', some bs' => some (b' :: bs') | _, _ => none) = _
    rw [hv, rawCarrier_roundtrip_lm rest]

/-- **Universal intact 64-bit pointer round-trip (`Trusted` ↔ vendored `ProvenanceMap.readPtr`,
runtime & CTFE, raw & ref).** -/
theorem intact_roundtrip_8 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    let bs := encodePtrBytes bits 8 a t
    decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 8 } 8) ∧
    trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt a t)) ∧
    trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt a t)) := by
  intro bs
  have hbits : decodeLittleEndianBits bs = some (bits % 256 ^ 8) :=
    decodeLittleEndianBits_encodePtrBytesAux a t _ 8 8 bits 0
  have hcoh : abstractBytesCoherentPtrProv? bs = some ⟨a, t, 0, normPtrByteOffset 8 bits, 8⟩ := by
    simp (config := { decide := true }) [bs, encodePtrBytes, encodePtrBytesAux,
      abstractBytesCoherentPtrProv?, abstractBytesCoherentPtrProvAux]
    rfl
  have hdec : decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 8 } 8) := by
    unfold decodePtrBytesNoForge
    have hlen : length bs = 8 := rfl
    simp (config := { decide := true }) [hlen, hbits, hcoh]
    rfl
  have hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f := by
    intro i v f hi
    obtain ⟨v', f', hv, _, hwf⟩ := encodePtrBytes_wf bits 8 a t i _ hi
    injection hv with _ hf; injection hf with hf; subst hf; exact hwf
  have hrt : trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt a t)) := by
    have h := readPtr8_allBytes_runtime_corr pvRt rfl bs rfl hwf
      (fun i v f hi => by
        obtain ⟨_, _, hv, hf, _⟩ := encodePtrBytes_wf bits 8 a t i _ hi
        injection hv with _ he; injection he with he; subst he; subst hf
        exact pvRt_ne_wildcard a t ha ht)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 8 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 8 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]; rfl
  have hct : trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt a t)) := by
    have h := readPtr8_allBytes_ctfe_corr pvCt rfl bs rfl hwf
      (fun i v f hi => by intro hw; cases hw)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 8 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 8 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]
  exact ⟨hdec, hrt, hct⟩

/-- **Universal intact 32-bit pointer round-trip (`Trusted` ↔ vendored `ProvenanceMap.readPtr`,
runtime & CTFE, raw & ref).** -/
theorem intact_roundtrip_4 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    let bs := encodePtrBytes bits 4 a t
    decodePtrBytesNoForge isRef (.uint .u8) 4 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 4 } 4) ∧
    trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt a t)) ∧
    trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt a t)) := by
  intro bs
  have hbits : decodeLittleEndianBits bs = some (bits % 256 ^ 4) :=
    decodeLittleEndianBits_encodePtrBytesAux a t _ 4 4 bits 0
  have hcoh : abstractBytesCoherentPtrProv? bs = some ⟨a, t, 0, normPtrByteOffset 4 bits, 4⟩ := by
    simp (config := { decide := true }) [bs, encodePtrBytes, encodePtrBytesAux,
      abstractBytesCoherentPtrProv?, abstractBytesCoherentPtrProvAux]
    rfl
  have hdec : decodePtrBytesNoForge isRef (.uint .u8) 4 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 4 } 4) := by
    unfold decodePtrBytesNoForge
    have hlen : length bs = 4 := rfl
    simp (config := { decide := true }) [hlen, hbits, hcoh]
    rfl
  have hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f := by
    intro i v f hi
    obtain ⟨v', f', hv, _, hwf⟩ := encodePtrBytes_wf bits 4 a t i _ hi
    injection hv with _ hf; injection hf with hf; subst hf; exact hwf
  have hrt : trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt a t)) := by
    have h := readPtr4_allBytes_runtime_corr pvRt rfl bs rfl hwf
      (fun i v f hi => by
        obtain ⟨_, _, hv, hf, _⟩ := encodePtrBytes_wf bits 4 a t i _ hi
        injection hv with _ he; injection he with he; subst he; subst hf
        exact pvRt_ne_wildcard a t ha ht)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 4 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 4 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]; rfl
  have hct : trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt a t)) := by
    have h := readPtr4_allBytes_ctfe_corr pvCt rfl bs rfl hwf
      (fun i v f hi => by intro hw; cases hw)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 4 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 4 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]
  exact ⟨hdec, hrt, hct⟩

/-- **Universal union raw-byte carrier pointer round-trip (64-bit, `Trusted` ↔ vendored Miri).** -/
theorem rawCarrier_ptr_roundtrip_8 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    ∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes bits 8 a t).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
        some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 8 } 8) ∧
      trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt a t)) ∧
      trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt a t)) :=
  let ⟨h1, h2, h3⟩ := intact_roundtrip_8 isRef bits a t ha ht
  ⟨encodePtrBytes bits 8 a t, rawCarrier_roundtrip_lm _, h1, h2, h3⟩

/-- **Universal union raw-byte carrier pointer round-trip (32-bit, `Trusted` ↔ vendored Miri).** -/
theorem rawCarrier_ptr_roundtrip_4 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    ∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes bits 4 a t).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge isRef (.uint .u8) 4 bs =
        some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 4 } 4) ∧
      trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt a t)) ∧
      trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt a t)) :=
  let ⟨h1, h2, h3⟩ := intact_roundtrip_4 isRef bits a t ha ht
  ⟨encodePtrBytes bits 4 a t, rawCarrier_roundtrip_lm _, h1, h2, h3⟩

section WideAndKani

open Trusted.Rustc.V2026_06_01.Layout

/-- Plain length `3` (64-bit and 32-bit) and vtable pointers (64-bit and 32-bit) for wide-pointer witnesses. -/
def lLen64 : List AbstractByte := encodePlainLittleEndianBytes 3 8
def lLen32 : List AbstractByte := encodePlainLittleEndianBytes 3 4
def lVt64 : List AbstractByte := encodePtrBytes 0x80 8 42 42
def lVt32 : List AbstractByte := encodePtrBytes 0x20 4 43 43

/-- **Wide slice & `str` pointers (64-bit & 32-bit) against vendored `ProvenanceMap.readPtr`.**
Intact `data ++ len` decodes identically in `Trusted` and vendored Miri (data half at offset `0`
carries provenance; length half at offset `pb` has no provenance); reversed data half strips
provenance in both; swapped `len ++ data` has no provenance at offset `0` and triggers `Trusted`
metadata provenance rejection (matching CTFE `readPointerAsInt` on metadata at offset `pb`). -/
theorem w_lm_wide_slice_and_str :
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lP ++ lLen64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (lP ++ lLen64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge true .str 8 (lP ++ lLen64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    trRead (trEntries pvRt (lP ++ lLen64)) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (trEntries pvRt (lP ++ lLen64)) 8 8 = .ok none ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 4 (lQ ++ lLen32) =
      some (.aggregate 0 [.ptr ⟨9, 0x1000⟩ 4, .scalar ⟨3, 4⟩]) ∧
    trRead (trEntries pvRt (lQ ++ lLen32)) 0 4 = .ok (some (pvRt 9 9)) ∧
    trRead (trEntries pvRt (lQ ++ lLen32)) 4 4 = .ok none ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lP.reverse ++ lLen64) = none ∧
    trRead (trEntries pvRt (lP.reverse ++ lLen64)) 0 8 = .ok none ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lLen64 ++ lP) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (lLen64 ++ lP) = none ∧
    trRead (trEntries pvRt (lLen64 ++ lP)) 0 8 = .ok none := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩ <;>
    (simp only [lP, lQ, lLen64, lLen32, encodePtrBytes, encodePtrBytesAux,
      encodePlainLittleEndianBytes, normPtrByteOffset, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, trEntries, trEntriesAux, fragOf, mkFrag,
      Nat.reduceAdd, Nat.reducePow, Nat.reduceMod]
     lm_trread; lm_open; lm_close)

/-- **Wide `&dyn Trait` pointers (64-bit & 32-bit) against vendored `ProvenanceMap.readPtr`.**
Intact `data ++ vtable` reads data provenance at offset `0` and vtable provenance at offset `pb`
in both `Trusted` and vendored Miri; a reversed vtable half strips vtable provenance in both. -/
theorem w_lm_wide_dyn :
    decodePtrBytesNoForge true (.dynamic "T") 8 (lP ++ lVt64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .ptr ⟨42, 0x80⟩ 8]) ∧
    trRead (trEntries pvRt (lP ++ lVt64)) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (trEntries pvRt (lP ++ lVt64)) 8 8 = .ok (some (pvRt 42 42)) ∧
    decodePtrBytesNoForge true (.dynamic "T") 4 (lQ ++ lVt32) =
      some (.aggregate 0 [.ptr ⟨9, 0x1000⟩ 4, .ptr ⟨43, 0x20⟩ 4]) ∧
    trRead (trEntries pvRt (lQ ++ lVt32)) 0 4 = .ok (some (pvRt 9 9)) ∧
    trRead (trEntries pvRt (lQ ++ lVt32)) 4 4 = .ok (some (pvRt 43 43)) ∧
    decodePtrBytesNoForge true (.dynamic "T") 8 (lP ++ lVt64.reverse) = none ∧
    decodePtrBytesNoForge false (.dynamic "T") 8 (lP ++ lVt64.reverse) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨0x8000000000000000, 8⟩]) ∧
    trRead (trEntries pvRt (lP ++ lVt64.reverse)) 8 8 = .ok none ∧
    trRead (trEntries pvCt (lP ++ lVt64.reverse)) 8 8 = .error (.readPartialPointer (Size.ofBytes 8)) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩ <;>
    (simp only [lP, lQ, lVt64, lVt32, encodePtrBytes, encodePtrBytesAux, normPtrByteOffset,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      trEntries, trEntriesAux, fragOf, mkFrag, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod]
     lm_trread; lm_open; lm_close)

/-- **Universal `Kani#5205` `Trusted` ↔ vendored Miri `bool` validity biconditional.** For every
byte `b : UInt8`, `Trusted.validateValueForTy?` and `Trusted.decodeTypedValueFromBytes` at `bool`
accept `b` iff unmodified vendored `Miri.Memory.Validity.checkPrimitive .boolean` returns `.ok .valid ()`. -/
theorem kani5205_bool_validity_iff (b : UInt8) :
    (validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨b.toNat, 1⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 b))
        (fun _ s => .ok false s) () = .ok .valid ()) ∧
    ((decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init b none]).isSome = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 b))
        (fun _ s => .ok false s) () = .ok .valid ()) := by
  rw [miri_checkPrimitive_bool_iff b]
  have hlt : b.toNat < 256 := UInt8.toNat_lt b
  by_cases hb : b.toNat ≤ 1
  · have : b = 0 ∨ b = 1 := by
      have : b.toNat = 0 ∨ b.toNat = 1 := by omega
      rcases this with h | h
      · exact Or.inl (UInt8.toNat_inj.mp h)
      · exact Or.inr (UInt8.toNat_inj.mp h)
    simp only [hb, ↓reduceIte, iff_true]
    rcases this with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · have hble : Nat.ble b.toNat 1 = false := by
      cases h : Nat.ble b.toNat 1 with
      | false => rfl
      | true => exact absurd (Nat.ble_eq.mp h) hb
    have hval : validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨b.toNat, 1⟩) = false := by
      show Bool.and true (Nat.ble b.toNat 1) = false
      rw [hble]; rfl
    have hne0 : Nat.beq b.toBitVec.toNat 0 = false := by
      cases h : Nat.beq b.toBitVec.toNat 0 with
      | false => rfl
      | true => have : b.toNat = 0 := Nat.eq_of_beq_eq_true h; omega
    have hne1 : Nat.beq b.toBitVec.toNat 1 = false := by
      cases h : Nat.beq b.toBitVec.toNat 1 with
      | false => rfl
      | true => have : b.toNat = 1 := Nat.eq_of_beq_eq_true h; omega
    have hdec : decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init b none] = none := by
      show (match Nat.beq b.toBitVec.toNat 0 with
        | true => some (Value.scalar ⟨0, 1⟩)
        | false => match Nat.beq b.toBitVec.toNat 1 with
          | true => some (Value.scalar ⟨1, 1⟩)
          | false => none) = none
      rw [hne0, hne1]
    simp [hb, hval, hdec]

/-- **Universal `Kani#5205` `Trusted` ↔ vendored Miri `char` validity biconditional.** For every
32-bit word `c : UInt32`, `Trusted.validateValueForTy?` at `char` accepts `c` iff unmodified
vendored `Miri.Memory.Validity.checkPrimitive .character` returns `.ok .valid ()`. -/
theorem kani5205_char_validity_iff (c : UInt32) :
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨c.toNat, 4⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 c))
        (fun _ s => .ok false s) () = .ok .valid () := by
  rw [miri_checkPrimitive_char_iff c]
  have hlt : c.toNat < 2 ^ 32 := UInt32.toNat_lt c
  show (Bool.and (Nat.beq 4 4) (isValidCharCode c.toNat) = true) ↔ _
  unfold isValidCharCode
  by_cases hc : c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF)
  · simp only [hc, ↓reduceIte, iff_true]
    rcases hc with h1 | ⟨h2, h3⟩
    · have hblt : Nat.blt c.toNat 55296 = true := by unfold Nat.blt; rw [Nat.ble_eq]; omega
      simp [hblt]
      left
      cases h : Nat.ble 55296 c.toNat with
      | false => rfl
      | true => have := Nat.ble_eq.mp h; omega
    · have h2' : Nat.ble 57344 c.toNat = true := Nat.ble_eq.mpr h2
      have h3' : Nat.ble c.toNat 1114111 = true := Nat.ble_eq.mpr h3
      simp [h2', h3']
  · simp only [hc, ↓reduceIte]
    have h1 : Nat.blt c.toNat 55296 = false := by
      cases h : Nat.blt c.toNat 55296 with
      | false => rfl
      | true =>
        have : c.toNat < 55296 := by unfold Nat.blt at h; rw [Nat.ble_eq] at h; omega
        exact absurd (Or.inl this) hc
    have h2 : (Bool.and (Nat.ble 57344 c.toNat) (Nat.ble c.toNat 1114111)) = false := by
      cases h : Bool.and (Nat.ble 57344 c.toNat) (Nat.ble c.toNat 1114111) with
      | false => rfl
      | true =>
        simp only [Bool.and_eq_true, Nat.ble_eq] at h
        exact absurd (Or.inr h) hc
    simp [h1, h2]
    omega

def wUnalignedBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [2] }
def wMaybeUninitBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }
def wMaybeUninitCharL : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [3, 0] }
def wKaniLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L, wUnalignedBoolL, wMaybeUninitBoolL, wMaybeUninitCharL] }
def wTyUnalignedBool : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 5 }
def wTyMaybeUninitBool : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 6 }
def wTyMaybeUninitChar : Ty := { kind := .adt "core::mem::MaybeUninit" [.char], layoutIdx := 7 }

/-- **End-to-end `Kani#5205` MIR witness (`Trusted` `writeBytesAction` + `evalOperand` paired with
vendored `Miri.Memory.Allocation` + `Validity.checkPrimitive`).** Writing `2u8` into `bool`,
`Unaligned<bool>`, and `MaybeUninit<bool>` (and `0xD8` into `MaybeUninit<char>`) via untyped
`write_bytes` succeeds without write-time UB; container union reads pass `validateValueForTy?`,
while typed `evalOperand` reads of `bool`, `Unaligned<bool>`, `u.0`, `MaybeUninit<bool>.assume_init`,
and `MaybeUninit<char>.assume_init` all fault with `.ub`, matching `w_lm_kani5205_alloc_e2e`. -/
theorem w_lm_kani5205_e2e :
    let decls : List LocalDecl := [
      { mutability := .mut, ty := wTyBool, debugName := none },
      { mutability := .mut, ty := wTyUnalignedBool, debugName := none },
      { mutability := .mut, ty := wTyMaybeUninitBool, debugName := none },
      { mutability := .mut, ty := wTyMaybeUninitChar, debugName := none }
    ]
    let bs : List BorrowEntry := [
      { tag := 1, targetLocal := 0, targetProjection := [], perm := .active },
      { tag := 2, targetLocal := 1, targetProjection := [], perm := .active },
      { tag := 3, targetLocal := 2, targetProjection := [], perm := .active },
      { tag := 4, targetLocal := 3, targetProjection := [], perm := .active }
    ]
    let wb (tag : Nat) (tyArg : RigidTy) (byteVal : Nat) : WriteBytesAction :=
      writeBytesAction bs 0 { defPath := "core::ptr::write_bytes", typeArgs := [tyArg] }
        decls wKaniLayouts [] [.ptr { allocId := tag, offsetBytes := 0 } 8, .scalar ⟨byteVal, 1⟩, .scalar ⟨1, 8⟩]
    let surrVal : Value := .aggregate 0 [.unit, .unit, .aggregate 0
      (encodeRawAbstractByteVals (encodePlainLittleEndianBytes 0xD800 4))]
    (match wb 1 .bool 2, wb 2 wTyUnalignedBool.kind 2, wb 3 wTyMaybeUninitBool.kind 2 with
     | .store ⟨0, []⟩ 0 1 (.scalar ⟨2, 1⟩),
       .store ⟨1, []⟩ 1 2 unalVal,
       .store ⟨2, []⟩ 2 3 muBoolVal =>
       validateValueForTy? wKaniLayouts (some wTyMaybeUninitBool) muBoolVal = true ∧
       validateValueForTy? wKaniLayouts (some wTyMaybeUninitChar) surrVal = true ∧
       evalOperand [.init (.scalar ⟨2, 1⟩)] (.copy ⟨0, []⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .init unalVal] (.copy ⟨1, []⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]
         (.copy ⟨1, [.field 0 wTyBool]⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .uninit, .init muBoolVal]
         (.copy ⟨2, [.field 0 wTyBool]⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .uninit, .uninit, .init surrVal]
         (.copy ⟨3, [.field 0 wTyChar]⟩) [] [] wKaniLayouts [] decls = .ub
     | _, _, _ => False) ∧
    miriWriteThenReadScalar #[0] #[2] 1 = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 2)) ∧
    miriWriteThenReadScalar #[0, 0, 0, 0] #[0x00, 0xD8, 0x00, 0x00] 4 =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800)) :=
  ⟨by repeat first | refine ⟨?_, ?_⟩ | rfl | trivial,
   w_lm_kani5205_alloc_e2e.1,
   w_lm_kani5205_alloc_e2e.2.1⟩

/-- Non-vacuous instantiations of `encodePtrBytes_wf`, `readPtr{4,8}_allBytes_{runtime,ctfe}_corr`,
`intact_roundtrip_{4,8}`, `rawCarrier_ptr_roundtrip_{4,8}`, and `kani5205_{bool,char}_validity_iff`. -/
theorem ep2_b1_non_vacuity_instances :
    (∃ v f, lP[0]? = some (.init v (some f)) ∧ f = ⟨7, 7, 0, 0x1000, 8⟩ ∧ WF 8 f) ∧
    trRead (trEntries pvRt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok none ∧
    trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok none ∧
    trRead (trEntries pvRt (lP.take 7 ++ [.uninit])) 0 8 = .ok none ∧
    trRead (trEntries pvCt (lP.take 7 ++ [.uninit])) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    trRead (trEntries pvRt (lQ.take 3 ++ [.init 0 none])) 0 4 = .ok none ∧
    trRead (trEntries pvCt (lQ.take 3 ++ [.init 0 none])) 0 4 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    (decodePtrBytesNoForge true (.uint .u8) 8 (encodePtrBytes 0x1000 8 7 7) =
      some (.ptr { allocId := 7, offsetBytes := 0x1000 % 256 ^ 8 } 8) ∧
     trRead (trEntries pvRt (encodePtrBytes 0x1000 8 7 7)) 0 8 = .ok (some (pvRt 7 7)) ∧
     trRead (trEntries pvCt (encodePtrBytes 0x1000 8 7 7)) 0 8 = .ok (some (pvCt 7 7))) ∧
    (decodePtrBytesNoForge false (.uint .u8) 4 (encodePtrBytes 0x1000 4 9 9) =
      some (.ptr { allocId := 9, offsetBytes := 0x1000 % 256 ^ 4 } 4) ∧
     trRead (trEntries pvRt (encodePtrBytes 0x1000 4 9 9)) 0 4 = .ok (some (pvRt 9 9)) ∧
     trRead (trEntries pvCt (encodePtrBytes 0x1000 4 9 9)) 0 4 = .ok (some (pvCt 9 9))) ∧
    (∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes 0x1000 8 7 7).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge true (.uint .u8) 8 bs = some (.ptr { allocId := 7, offsetBytes := 0x1000 % 256 ^ 8 } 8) ∧
      trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt 7 7)) ∧
      trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt 7 7))) ∧
    (∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes 0x1000 4 9 9).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge false (.uint .u8) 4 bs = some (.ptr { allocId := 9, offsetBytes := 0x1000 % 256 ^ 4 } 4) ∧
      trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt 9 9)) ∧
      trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt 9 9))) ∧
    (validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨(2 : UInt8).toNat, 1⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 2))
        (fun _ s => .ok false s) () = .ok .valid ()) ∧
    (validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨(0xD800 : UInt32).toNat, 4⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800))
        (fun _ s => .ok false s) () = .ok .valid ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    intact_roundtrip_8 true 0x1000 7 7 (by decide) (by decide),
    intact_roundtrip_4 false 0x1000 9 9 (by decide) (by decide),
    rawCarrier_ptr_roundtrip_8 true 0x1000 7 7 (by decide) (by decide),
    rawCarrier_ptr_roundtrip_4 false 0x1000 9 9 (by decide) (by decide),
    (kani5205_bool_validity_iff 2).1,
    kani5205_char_validity_iff 0xD800⟩
  · obtain ⟨v, f, hv, hf, hwf⟩ := encodePtrBytes_wf 0x1000 8 7 7 0 _ rfl
    exact ⟨v, f, hv ▸ rfl, hf, hwf⟩
  · exact (readPtr8_allBytes_runtime_corr pvRt rfl (encodePlainLittleEndianBytes 0x1000 8) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)).trans rfl
  · exact (readPtr8_allBytes_ctfe_corr pvCt rfl (encodePlainLittleEndianBytes 0x1000 8) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)).trans rfl
  · exact (readPtr8_allBytes_runtime_corr pvRt rfl (lP.take 7 ++ [.uninit]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; decide
        | 7, h | _+8, h => cases h)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 7 ∧ fi.tag = 7 := by
            match i, hi with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          have hj' : fj.allocId = 7 ∧ fj.tag = 7 := by
            match j, hj with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl
  · exact (readPtr8_allBytes_ctfe_corr pvCt rfl (lP.take 7 ++ [.uninit]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 7, h | _+8, h => cases h)
      (by intro i v f hi hw; cases hw)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 7 ∧ fi.tag = 7 := by
            match i, hi with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          have hj' : fj.allocId = 7 ∧ fj.tag = 7 := by
            match j, hj with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl
  · exact (readPtr4_allBytes_runtime_corr pvRt rfl (lQ.take 3 ++ [.init 0 none]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 3, h | _+4, h => cases h)
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; decide
        | 3, h | _+4, h => cases h)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 9 ∧ fi.tag = 9 := by
            match i, hi with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          have hj' : fj.allocId = 9 ∧ fj.tag = 9 := by
            match j, hj with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl
  · exact (readPtr4_allBytes_ctfe_corr pvCt rfl (lQ.take 3 ++ [.init 0 none]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 3, h | _+4, h => cases h)
      (by intro i v f hi hw; cases hw)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 9 ∧ fi.tag = 9 := by
            match i, hi with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          have hj' : fj.allocId = 9 ∧ fj.tag = 9 := by
            match j, hj with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl

end WideAndKani

/-- Non-vacuous instantiations of `readPtr8_allBytes_ctfe_iff` and `readPtr4_allBytes_ctfe_iff`
on the plain (provenance-free) images of `0x1000` with CTFE provenance. -/
theorem readPtr_allBytes_ctfe_iff_instance :
    (((∃ f, abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 8) = some f) ↔
      ∃ p, trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 8) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 8) = true) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 8) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 8) = false) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok none)) ∧
    (((∃ f, abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 4) = some f) ↔
      ∃ p, trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 4)) 0 4 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 4) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 4) = true) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 4)) 0 4 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 4) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 4) = false) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 4)) 0 4 = .ok none)) :=
  ⟨readPtr8_allBytes_ctfe_iff pvCt rfl (encodePlainLittleEndianBytes 0x1000 8) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h),
   readPtr4_allBytes_ctfe_iff pvCt rfl (encodePlainLittleEndianBytes 0x1000 4) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | _+4, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | _+4, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | _+4, h => cases h)⟩

end V06

/-! ## `V2026_08_01`: correspondence of `Trusted.Rustc.V2026_08_01.MirSemantics` with vendored `Miri.Memory.ProvenanceMap` -/

namespace V08

open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.MirAst
open Trusted.Rustc.V2026_08_01.MirSemantics

/-! ### §1. The translation `PtrByteFrag → PointerFrag` -/

/-- The vendored Miri fragment of a `Trusted` pointer-byte fragment: index `byteIdx`, provenance
`pv allocId tag`, and the zero-padded 8-byte image of the originating pointer. -/
def mkFrag {Prov : Type} (pv : Nat → Nat → Prov) (f : PtrByteFrag) : PointerFrag Prov :=
  ⟨UInt8.ofNat f.byteIdx, pv f.allocId f.tag, ptrImage f.ptrBytes f.origOffset⟩

/-- The fragment (if any) that a `Trusted` abstract byte contributes to the provenance map.
Plain and uninitialized bytes contribute none: Miri tracks initialization in the `InitMask`, not
in the `ProvenanceMap`. -/
def fragOf {Prov : Type} (pv : Nat → Nat → Prov) : AbstractByte → Option (PointerFrag Prov)
  | .init _ (some f) => some (mkFrag pv f)
  | _ => none

def trEntriesAux {Prov : Type} (pv : Nat → Nat → Prov) :
    Nat → List AbstractByte → List (Size × PointerFrag Prov)
  | _, [] => []
  | i, b :: rest =>
    match fragOf pv b with
    | some g => (Size.ofBytes (UInt64.ofNat i), g) :: trEntriesAux pv (i + 1) rest
    | none => trEntriesAux pv (i + 1) rest

/-- **The exact translation of a `Trusted` byte stream to a vendored Miri fragment state**
(`ProvenanceMap.fromParts #[] (some (trEntries pv bs))`): one `PointerFrag` per
fragment-carrying byte, at that byte's offset. -/
def trEntries {Prov : Type} (pv : Nat → Nat → Prov) (bs : List AbstractByte) :
    Array (Size × PointerFrag Prov) :=
  (trEntriesAux pv 0 bs).toArray

/-- Well-formed fragment of a `pb`-byte target: the fragment width is the target pointer width,
the index is in range, and the originating offset is normalized (`normPtrByteOffset`). -/
def WF (pb : Nat) (f : PtrByteFrag) : Prop :=
  f.ptrBytes = pb ∧ f.byteIdx < pb ∧ f.origOffset < 256 ^ pb

theorem mkFrag_idx {Prov : Type} (pv : Nat → Nat → Prov) (f : PtrByteFrag)
    (h : f.byteIdx < 256) : (mkFrag pv f).idx.toNat = f.byteIdx := by
  show (UInt8.ofNat f.byteIdx).toNat = f.byteIdx
  rw [u8_ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem scalarModulus_eq : ∀ n, scalarModulus n = 256 ^ n
  | 0 => rfl
  | n + 1 => by
      show Nat.mul 256 (scalarModulus n) = 256 ^ (n + 1)
      rw [scalarModulus_eq n, Nat.pow_succ, Nat.mul_comm]
      rfl

theorem normPtrByteOffset_lt (pb o : Nat) : normPtrByteOffset pb o < 256 ^ pb := by
  show Nat.mod o (scalarModulus pb) < 256 ^ pb
  rw [scalarModulus_eq]
  exact Nat.mod_lt _ (pow256_pos pb)

/-- **Exact byte-vector injectivity of `normPtrByteOffset`** for every pointer width
`0 < ptrBytes ≤ 8` (in particular `4` and `8`): two normalized offsets have the same vendored
`PointerFrag.bytes` image iff they are equal. -/
theorem normOffset_image_inj (pb o o' : Nat) (h8 : pb ≤ 8) :
    ptrImage pb (normPtrByteOffset pb o) = ptrImage pb (normPtrByteOffset pb o') ↔
      normPtrByteOffset pb o = normPtrByteOffset pb o' :=
  ptrImage_inj pb _ _ h8 (normPtrByteOffset_lt pb o) (normPtrByteOffset_lt pb o')

/-- The fragments of an encoded pointer are well formed. -/
theorem encodePtrBytes_wf (bits pb a t i : Nat) (b : AbstractByte)
    (h : (encodePtrBytes bits pb a t)[i]? = some b) :
    ∃ v f, b = .init v (some f) ∧ f = ⟨a, t, i, normPtrByteOffset pb bits, pb⟩ ∧ WF pb f := by
  have key : ∀ (n bits' idx : Nat), idx + n = pb → ∀ j b',
      (encodePtrBytesAux a t (normPtrByteOffset pb bits) pb bits' idx n)[j]? = some b' →
        ∃ v, b' = .init v (some ⟨a, t, idx + j, normPtrByteOffset pb bits, pb⟩) ∧ idx + j < pb := by
    intro n
    induction n with
    | zero =>
        intro _ _ _ j b' hj
        cases hj
    | succ n ih =>
        intro bits' idx hn j b' hj
        cases j with
        | zero =>
            have hx : some (AbstractByte.init (UInt8.ofNat bits')
                (some ⟨a, t, idx, normPtrByteOffset pb bits, pb⟩)) = some b' := hj
            injection hx with hx
            exact ⟨_, hx.symm, by omega⟩
        | succ j =>
            have hj' : (encodePtrBytesAux a t (normPtrByteOffset pb bits) pb (Nat.div bits' 256)
                (Nat.add idx 1) n)[j]? = some b' := hj
            obtain ⟨v, hv, hlt⟩ := ih (Nat.div bits' 256) (Nat.add idx 1) (by
              show idx + 1 + n = pb
              omega) j b' hj'
            refine ⟨v, ?_, by
              show idx + (j + 1) < pb
              have : idx + 1 + j < pb := hlt
              omega⟩
            rw [hv]
            have e : Nat.add idx 1 + j = idx + (j + 1) := by
              show idx + 1 + j = idx + (j + 1)
              omega
            rw [e]
  obtain ⟨v, hv, hlt⟩ := key pb bits 0 (by omega) i b h
  rw [Nat.zero_add] at hv hlt
  exact ⟨v, _, hv, rfl, rfl, hlt, normPtrByteOffset_lt pb bits⟩

/-! ### §2. `Trusted` coherence on a fragment-headed stream -/

theorem coh?_isSome (v : UInt8) (f : PtrByteFrag) (rest : List AbstractByte) :
    (abstractBytesCoherentPtrProv? (.init v (some f) :: rest)).isSome =
      Bool.and (Nat.blt 0 f.ptrBytes)
        (Bool.and (Nat.beq f.byteIdx 0)
          (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) := by
  show (match Bool.and (Nat.blt 0 f.ptrBytes)
      (Bool.and (Nat.beq f.byteIdx 0)
        (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) with
    | true => some f
    | false => none).isSome = _
  cases Bool.and (Nat.blt 0 f.ptrBytes)
      (Bool.and (Nat.beq f.byteIdx 0)
        (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) <;> rfl

/-! ### §3.4. Universal correspondence on `4`-byte fragment streams -/

/-- **Exact coherence correspondence on `4` well-formed fragments.** Vendored Miri's in-order
fragment agreement on the translated fragments is exactly `Trusted`'s coherence verdict
(`abstractBytesCoherentPtrProv?`), for any provenance embedding that separates the fragments'
`(allocId, tag)` pairs from that of fragment `0`. -/
theorem coh_iff4 {Prov : Type} [DecidableEq Prov] (pv : Nat → Nat → Prov)
    (v0 v1 v2 v3 : UInt8) (f0 f1 f2 f3 : PtrByteFrag)
    (wf0 : WF 4 f0)
    (wf1 : WF 4 f1)
    (wf2 : WF 4 f2)
    (wf3 : WF 4 f3)
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag) :
    miriCoh [mkFrag pv f0, mkFrag pv f1, mkFrag pv f2, mkFrag pv f3] = (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]).isSome := by
  obtain ⟨p0, i0, o0⟩ := wf0
  obtain ⟨p1, i1, o1⟩ := wf1
  obtain ⟨p2, i2, o2⟩ := wf2
  obtain ⟨p3, i3, o3⟩ := wf3
  have e0 := mkFrag_idx pv f0 (by omega)
  have e1 := mkFrag_idx pv f1 (by omega)
  have e2 := mkFrag_idx pv f2 (by omega)
  have e3 := mkFrag_idx pv f3 (by omega)
  have r1 : (mkFrag pv f1).prov = (mkFrag pv f0).prov ↔ f1.allocId = f0.allocId ∧ f1.tag = f0.tag :=
    ⟨hinj1, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r2 : (mkFrag pv f2).prov = (mkFrag pv f0).prov ↔ f2.allocId = f0.allocId ∧ f2.tag = f0.tag :=
    ⟨hinj2, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r3 : (mkFrag pv f3).prov = (mkFrag pv f0).prov ↔ f3.allocId = f0.allocId ∧ f3.tag = f0.tag :=
    ⟨hinj3, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have m1 : (mkFrag pv f1).bytes = (mkFrag pv f0).bytes ↔ f1.origOffset = f0.origOffset := by
    show ptrImage f1.ptrBytes f1.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p1, p0]
    exact ptrImage_inj 4 _ _ (by decide) o1 o0
  have m2 : (mkFrag pv f2).bytes = (mkFrag pv f0).bytes ↔ f2.origOffset = f0.origOffset := by
    show ptrImage f2.ptrBytes f2.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p2, p0]
    exact ptrImage_inj 4 _ _ (by decide) o2 o0
  have m3 : (mkFrag pv f3).bytes = (mkFrag pv f0).bytes ↔ f3.origOffset = f0.origOffset := by
    show ptrImage f3.ptrBytes f3.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p3, p0]
    exact ptrImage_inj 4 _ _ (by decide) o3 o0
  rw [coh?_isSome]
  apply Bool.eq_iff_iff.mpr
  simp only [miriCoh, miriCohAux, abstractBytesCoherentPtrProvAux, Bool.and_eq_true,
    decide_eq_true_eq, nat_beq_iff, Nat.blt_eq, Nat.add_eq, e0, e1, e2, e3, r1, r2, r3, m1, m2, m3, p0, p1, p2, p3]
  all_goals (constructor <;> intro h <;> simp_all)

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
`4`-byte pointers).** For every stream of `4` well-formed fragment bytes, the vendored read of
the translated fragment state returns `some (pv allocId tag)` exactly when `Trusted` finds the
stream coherent, and no provenance otherwise:
`abstractBytesCoherentPtrProv? bytes = some _ ↔ readPtr … = .ok (some _)` and
`abstractBytesCoherentPtrProv? bytes = none ↔ readPtr … = .ok none`. -/
theorem readPtr4_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (v0 v1 v2 v3 : UInt8) (f0 f1 f2 f3 : PtrByteFrag)
    (wf0 : WF 4 f0)
    (wf1 : WF 4 f1)
    (wf2 : WF 4 f2)
    (wf3 : WF 4 f3)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]) 0 4 =
      .ok (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]).isSome then
        some (pv f0.allocId f0.tag) else none) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] = fe4 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) from rfl,
    readPtr4_runtime _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3,
    coh_iff4 pv v0 v1 v2 v3 f0 f1 f2 f3 wf0 wf1 wf2 wf3 hinj1 hinj2 hinj3]
  rfl

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE strict
partial-pointer mode, `4`-byte pointers).** A coherent stream reads its provenance; every
incoherent stream is the vendored `readPartialPointer` error. -/
theorem readPtr4_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (v0 v1 v2 v3 : UInt8) (f0 f1 f2 f3 : PtrByteFrag)
    (wf0 : WF 4 f0)
    (wf1 : WF 4 f1)
    (wf2 : WF 4 f2)
    (wf3 : WF 4 f3)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]) 0 4 =
      (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)]).isSome then
        .ok (some (pv f0.allocId f0.tag)) else .error (.readPartialPointer (Size.ofBytes 0))) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] = fe4 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) from rfl,
    readPtr4_ctfe _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3,
    coh_iff4 pv v0 v1 v2 v3 f0 f1 f2 f3 wf0 wf1 wf2 wf3 hinj1 hinj2 hinj3]
  rfl

/-! ### §3.8. Universal correspondence on `8`-byte fragment streams -/

/-- **Exact coherence correspondence on `8` well-formed fragments.** Vendored Miri's in-order
fragment agreement on the translated fragments is exactly `Trusted`'s coherence verdict
(`abstractBytesCoherentPtrProv?`), for any provenance embedding that separates the fragments'
`(allocId, tag)` pairs from that of fragment `0`. -/
theorem coh_iff8 {Prov : Type} [DecidableEq Prov] (pv : Nat → Nat → Prov)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) (f0 f1 f2 f3 f4 f5 f6 f7 : PtrByteFrag)
    (wf0 : WF 8 f0)
    (wf1 : WF 8 f1)
    (wf2 : WF 8 f2)
    (wf3 : WF 8 f3)
    (wf4 : WF 8 f4)
    (wf5 : WF 8 f5)
    (wf6 : WF 8 f6)
    (wf7 : WF 8 f7)
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag)
    (hinj4 : pv f4.allocId f4.tag = pv f0.allocId f0.tag → f4.allocId = f0.allocId ∧ f4.tag = f0.tag)
    (hinj5 : pv f5.allocId f5.tag = pv f0.allocId f0.tag → f5.allocId = f0.allocId ∧ f5.tag = f0.tag)
    (hinj6 : pv f6.allocId f6.tag = pv f0.allocId f0.tag → f6.allocId = f0.allocId ∧ f6.tag = f0.tag)
    (hinj7 : pv f7.allocId f7.tag = pv f0.allocId f0.tag → f7.allocId = f0.allocId ∧ f7.tag = f0.tag) :
    miriCoh [mkFrag pv f0, mkFrag pv f1, mkFrag pv f2, mkFrag pv f3, mkFrag pv f4, mkFrag pv f5, mkFrag pv f6, mkFrag pv f7] = (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]).isSome := by
  obtain ⟨p0, i0, o0⟩ := wf0
  obtain ⟨p1, i1, o1⟩ := wf1
  obtain ⟨p2, i2, o2⟩ := wf2
  obtain ⟨p3, i3, o3⟩ := wf3
  obtain ⟨p4, i4, o4⟩ := wf4
  obtain ⟨p5, i5, o5⟩ := wf5
  obtain ⟨p6, i6, o6⟩ := wf6
  obtain ⟨p7, i7, o7⟩ := wf7
  have e0 := mkFrag_idx pv f0 (by omega)
  have e1 := mkFrag_idx pv f1 (by omega)
  have e2 := mkFrag_idx pv f2 (by omega)
  have e3 := mkFrag_idx pv f3 (by omega)
  have e4 := mkFrag_idx pv f4 (by omega)
  have e5 := mkFrag_idx pv f5 (by omega)
  have e6 := mkFrag_idx pv f6 (by omega)
  have e7 := mkFrag_idx pv f7 (by omega)
  have r1 : (mkFrag pv f1).prov = (mkFrag pv f0).prov ↔ f1.allocId = f0.allocId ∧ f1.tag = f0.tag :=
    ⟨hinj1, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r2 : (mkFrag pv f2).prov = (mkFrag pv f0).prov ↔ f2.allocId = f0.allocId ∧ f2.tag = f0.tag :=
    ⟨hinj2, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r3 : (mkFrag pv f3).prov = (mkFrag pv f0).prov ↔ f3.allocId = f0.allocId ∧ f3.tag = f0.tag :=
    ⟨hinj3, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r4 : (mkFrag pv f4).prov = (mkFrag pv f0).prov ↔ f4.allocId = f0.allocId ∧ f4.tag = f0.tag :=
    ⟨hinj4, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r5 : (mkFrag pv f5).prov = (mkFrag pv f0).prov ↔ f5.allocId = f0.allocId ∧ f5.tag = f0.tag :=
    ⟨hinj5, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r6 : (mkFrag pv f6).prov = (mkFrag pv f0).prov ↔ f6.allocId = f0.allocId ∧ f6.tag = f0.tag :=
    ⟨hinj6, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have r7 : (mkFrag pv f7).prov = (mkFrag pv f0).prov ↔ f7.allocId = f0.allocId ∧ f7.tag = f0.tag :=
    ⟨hinj7, fun h => by show pv _ _ = pv _ _; rw [h.1, h.2]⟩
  have m1 : (mkFrag pv f1).bytes = (mkFrag pv f0).bytes ↔ f1.origOffset = f0.origOffset := by
    show ptrImage f1.ptrBytes f1.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p1, p0]
    exact ptrImage_inj 8 _ _ (by decide) o1 o0
  have m2 : (mkFrag pv f2).bytes = (mkFrag pv f0).bytes ↔ f2.origOffset = f0.origOffset := by
    show ptrImage f2.ptrBytes f2.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p2, p0]
    exact ptrImage_inj 8 _ _ (by decide) o2 o0
  have m3 : (mkFrag pv f3).bytes = (mkFrag pv f0).bytes ↔ f3.origOffset = f0.origOffset := by
    show ptrImage f3.ptrBytes f3.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p3, p0]
    exact ptrImage_inj 8 _ _ (by decide) o3 o0
  have m4 : (mkFrag pv f4).bytes = (mkFrag pv f0).bytes ↔ f4.origOffset = f0.origOffset := by
    show ptrImage f4.ptrBytes f4.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p4, p0]
    exact ptrImage_inj 8 _ _ (by decide) o4 o0
  have m5 : (mkFrag pv f5).bytes = (mkFrag pv f0).bytes ↔ f5.origOffset = f0.origOffset := by
    show ptrImage f5.ptrBytes f5.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p5, p0]
    exact ptrImage_inj 8 _ _ (by decide) o5 o0
  have m6 : (mkFrag pv f6).bytes = (mkFrag pv f0).bytes ↔ f6.origOffset = f0.origOffset := by
    show ptrImage f6.ptrBytes f6.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p6, p0]
    exact ptrImage_inj 8 _ _ (by decide) o6 o0
  have m7 : (mkFrag pv f7).bytes = (mkFrag pv f0).bytes ↔ f7.origOffset = f0.origOffset := by
    show ptrImage f7.ptrBytes f7.origOffset = ptrImage f0.ptrBytes f0.origOffset ↔ _
    rw [p7, p0]
    exact ptrImage_inj 8 _ _ (by decide) o7 o0
  rw [coh?_isSome]
  apply Bool.eq_iff_iff.mpr
  simp only [miriCoh, miriCohAux, abstractBytesCoherentPtrProvAux, Bool.and_eq_true,
    decide_eq_true_eq, nat_beq_iff, Nat.blt_eq, Nat.add_eq, e0, e1, e2, e3, e4, e5, e6, e7, r1, r2, r3, r4, r5, r6, r7, m1, m2, m3, m4, m5, m6, m7, p0, p1, p2, p3, p4, p5, p6, p7]
  all_goals (constructor <;> intro h <;> simp_all)

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
`8`-byte pointers).** For every stream of `8` well-formed fragment bytes, the vendored read of
the translated fragment state returns `some (pv allocId tag)` exactly when `Trusted` finds the
stream coherent, and no provenance otherwise:
`abstractBytesCoherentPtrProv? bytes = some _ ↔ readPtr … = .ok (some _)` and
`abstractBytesCoherentPtrProv? bytes = none ↔ readPtr … = .ok none`. -/
theorem readPtr8_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) (f0 f1 f2 f3 f4 f5 f6 f7 : PtrByteFrag)
    (wf0 : WF 8 f0)
    (wf1 : WF 8 f1)
    (wf2 : WF 8 f2)
    (wf3 : WF 8 f3)
    (wf4 : WF 8 f4)
    (wf5 : WF 8 f5)
    (wf6 : WF 8 f6)
    (wf7 : WF 8 f7)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw4 : ¬ some (pv f4.allocId f4.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw5 : ¬ some (pv f5.allocId f5.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw6 : ¬ some (pv f6.allocId f6.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw7 : ¬ some (pv f7.allocId f7.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag)
    (hinj4 : pv f4.allocId f4.tag = pv f0.allocId f0.tag → f4.allocId = f0.allocId ∧ f4.tag = f0.tag)
    (hinj5 : pv f5.allocId f5.tag = pv f0.allocId f0.tag → f5.allocId = f0.allocId ∧ f5.tag = f0.tag)
    (hinj6 : pv f6.allocId f6.tag = pv f0.allocId f0.tag → f6.allocId = f0.allocId ∧ f6.tag = f0.tag)
    (hinj7 : pv f7.allocId f7.tag = pv f0.allocId f0.tag → f7.allocId = f0.allocId ∧ f7.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]) 0 8 =
      .ok (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]).isSome then
        some (pv f0.allocId f0.tag) else none) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] = fe8 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) (mkFrag pv f4) (mkFrag pv f5) (mkFrag pv f6) (mkFrag pv f7) from rfl,
    readPtr8_runtime _ _ _ _ _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3 hnw4 hnw5 hnw6 hnw7,
    coh_iff8 pv v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7 wf0 wf1 wf2 wf3 wf4 wf5 wf6 wf7 hinj1 hinj2 hinj3 hinj4 hinj5 hinj6 hinj7]
  rfl

/-- **Universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE strict
partial-pointer mode, `8`-byte pointers).** A coherent stream reads its provenance; every
incoherent stream is the vendored `readPartialPointer` error. -/
theorem readPtr8_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (v0 v1 v2 v3 v4 v5 v6 v7 : UInt8) (f0 f1 f2 f3 f4 f5 f6 f7 : PtrByteFrag)
    (wf0 : WF 8 f0)
    (wf1 : WF 8 f1)
    (wf2 : WF 8 f2)
    (wf3 : WF 8 f3)
    (wf4 : WF 8 f4)
    (wf5 : WF 8 f5)
    (wf6 : WF 8 f6)
    (wf7 : WF 8 f7)
    (hnw0 : ¬ some (pv f0.allocId f0.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw1 : ¬ some (pv f1.allocId f1.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw2 : ¬ some (pv f2.allocId f2.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw3 : ¬ some (pv f3.allocId f3.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw4 : ¬ some (pv f4.allocId f4.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw5 : ¬ some (pv f5.allocId f5.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw6 : ¬ some (pv f6.allocId f6.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hnw7 : ¬ some (pv f7.allocId f7.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj1 : pv f1.allocId f1.tag = pv f0.allocId f0.tag → f1.allocId = f0.allocId ∧ f1.tag = f0.tag)
    (hinj2 : pv f2.allocId f2.tag = pv f0.allocId f0.tag → f2.allocId = f0.allocId ∧ f2.tag = f0.tag)
    (hinj3 : pv f3.allocId f3.tag = pv f0.allocId f0.tag → f3.allocId = f0.allocId ∧ f3.tag = f0.tag)
    (hinj4 : pv f4.allocId f4.tag = pv f0.allocId f0.tag → f4.allocId = f0.allocId ∧ f4.tag = f0.tag)
    (hinj5 : pv f5.allocId f5.tag = pv f0.allocId f0.tag → f5.allocId = f0.allocId ∧ f5.tag = f0.tag)
    (hinj6 : pv f6.allocId f6.tag = pv f0.allocId f0.tag → f6.allocId = f0.allocId ∧ f6.tag = f0.tag)
    (hinj7 : pv f7.allocId f7.tag = pv f0.allocId f0.tag → f7.allocId = f0.allocId ∧ f7.tag = f0.tag) :
    trRead (trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]) 0 8 =
      (if (abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)]).isSome then
        .ok (some (pv f0.allocId f0.tag)) else .error (.readPartialPointer (Size.ofBytes 0))) := by
  rw [show trEntries pv [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] = fe8 (mkFrag pv f0) (mkFrag pv f1) (mkFrag pv f2) (mkFrag pv f3) (mkFrag pv f4) (mkFrag pv f5) (mkFrag pv f6) (mkFrag pv f7) from rfl,
    readPtr8_ctfe _ _ _ _ _ _ _ _ hoff hnw0 hnw1 hnw2 hnw3 hnw4 hnw5 hnw6 hnw7,
    coh_iff8 pv v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7 wf0 wf1 wf2 wf3 wf4 wf5 wf6 wf7 hinj1 hinj2 hinj3 hinj4 hinj5 hinj6 hinj7]
  rfl


/-! ### §4. Fixtures and kernel-checked witnesses -/

section Witnesses

open Trusted.Rustc.V2026_08_01.Layout

/-- `p = alloc 7 + 0x1000` (64-bit). -/
def lP : List AbstractByte := encodePtrBytes 0x1000 8 7 7
/-- `p + 4`. -/
def lP4 : List AbstractByte := encodePtrBytes 0x1004 8 7 7
/-- `p + 256`: byte 0 is `0x00`, exactly as in `p`. -/
def lP256 : List AbstractByte := encodePtrBytes 0x1100 8 7 7
/-- The all-zero image `alloc 7 + 0`. -/
def lZ : List AbstractByte := encodePtrBytes 0 8 7 7
/-- A pointer into another allocation. -/
def lO : List AbstractByte := encodePtrBytes 0x1000 8 8 8
/-- `q = alloc 9 + 0x1000` (32-bit). -/
def lQ : List AbstractByte := encodePtrBytes 0x1000 4 9 9
/-- `q + 256` (32-bit). -/
def lQ256 : List AbstractByte := encodePtrBytes 0x1100 4 9 9

/-- **Three-way witness: the intact pointer `p`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_intact :
    lP = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .ok (some (pvCt 7 7)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.ptr ⟨7, 4096⟩ 8) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.ptr ⟨7, 4096⟩ 8) :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 8-byte full reversal of the all-zero image of offset `0`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_zero_reversal :
    lZ.reverse = [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)] = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 0, 8⟩), .init 0 (some ⟨7, 7, 6, 0, 8⟩), .init 0 (some ⟨7, 7, 5, 0, 8⟩), .init 0 (some ⟨7, 7, 4, 0, 8⟩), .init 0 (some ⟨7, 7, 3, 0, 8⟩), .init 0 (some ⟨7, 7, 2, 0, 8⟩), .init 0 (some ⟨7, 7, 1, 0, 8⟩), .init 0 (some ⟨7, 7, 0, 0, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 7, 0, 8⟩ ⟨7, 7, 6, 0, 8⟩ ⟨7, 7, 5, 0, 8⟩ ⟨7, 7, 4, 0, 8⟩ ⟨7, 7, 3, 0, 8⟩ ⟨7, 7, 2, 0, 8⟩ ⟨7, 7, 1, 0, 8⟩ ⟨7, 7, 0, 0, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 7, 0, 8⟩ ⟨7, 7, 6, 0, 8⟩ ⟨7, 7, 5, 0, 8⟩ ⟨7, 7, 4, 0, 8⟩ ⟨7, 7, 3, 0, 8⟩ ⟨7, 7, 2, 0, 8⟩ ⟨7, 7, 1, 0, 8⟩ ⟨7, 7, 0, 0, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 8-byte full reversal of `p`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_reversal :
    lP.reverse = [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = some (.scalar ⟨4503599627370496, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 0 0 0 0 0 16 0 ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 0 0 0 0 0 16 0 ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the byte-0 / byte-1 swap.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_swap01 :
    (lP.take 2).reverse ++ lP.drop 2 = [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.scalar ⟨16, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: byte 0 of `p` repeated 8×.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_dup_head :
    List.replicate 8 (lP.headD .uninit) = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = some (.scalar ⟨0, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 0 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: a non-identity permutation (rotation by one byte).** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_rotate :
    lP.drop 1 ++ lP.take 1 = [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = some (.scalar ⟨16, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩), .init 0 (some ⟨7, 7, 0, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 16 0 0 0 0 0 0 0 ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4096, 8⟩ ⟨7, 7, 5, 4096, 8⟩ ⟨7, 7, 6, 4096, 8⟩ ⟨7, 7, 7, 4096, 8⟩ ⟨7, 7, 0, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the `p` / `p + 4` offset splice.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_splice_p_p4 :
    lP.take 4 ++ lP4.drop 4 = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)] = some (.scalar ⟨4096, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4100, 8⟩), .init 0 (some ⟨7, 7, 5, 4100, 8⟩), .init 0 (some ⟨7, 7, 6, 4100, 8⟩), .init 0 (some ⟨7, 7, 7, 4100, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4100, 8⟩ ⟨7, 7, 5, 4100, 8⟩ ⟨7, 7, 6, 4100, 8⟩ ⟨7, 7, 7, 4100, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨7, 7, 4, 4100, 8⟩ ⟨7, 7, 5, 4100, 8⟩ ⟨7, 7, 6, 4100, 8⟩ ⟨7, 7, 7, 4100, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the `p` / `p + 256` offset splice (byte 0 is `0x00` in both pointers).** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_splice_p_p256 :
    lP.take 1 ++ lP256.drop 1 = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)] = some (.scalar ⟨4352, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 17 (some ⟨7, 7, 1, 4352, 8⟩), .init 0 (some ⟨7, 7, 2, 4352, 8⟩), .init 0 (some ⟨7, 7, 3, 4352, 8⟩), .init 0 (some ⟨7, 7, 4, 4352, 8⟩), .init 0 (some ⟨7, 7, 5, 4352, 8⟩), .init 0 (some ⟨7, 7, 6, 4352, 8⟩), .init 0 (some ⟨7, 7, 7, 4352, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 17 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4352, 8⟩ ⟨7, 7, 2, 4352, 8⟩ ⟨7, 7, 3, 4352, 8⟩ ⟨7, 7, 4, 4352, 8⟩ ⟨7, 7, 5, 4352, 8⟩ ⟨7, 7, 6, 4352, 8⟩ ⟨7, 7, 7, 4352, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 17 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4352, 8⟩ ⟨7, 7, 2, 4352, 8⟩ ⟨7, 7, 3, 4352, 8⟩ ⟨7, 7, 4, 4352, 8⟩ ⟨7, 7, 5, 4352, 8⟩ ⟨7, 7, 6, 4352, 8⟩ ⟨7, 7, 7, 4352, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: a mixed-provenance (two allocations) splice.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_mixed_alloc :
    lP.take 4 ++ lO.drop 4 = [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)]) 0 8 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)]) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)] = some (.scalar ⟨4096, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 (some ⟨7, 7, 1, 4096, 8⟩), .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨8, 8, 4, 4096, 8⟩), .init 0 (some ⟨8, 8, 5, 4096, 8⟩), .init 0 (some ⟨8, 8, 6, 4096, 8⟩), .init 0 (some ⟨8, 8, 7, 4096, 8⟩)] = none :=
  ⟨rfl, (readPtr8_runtime_corr pvRt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨8, 8, 4, 4096, 8⟩ ⟨8, 8, 5, 4096, 8⟩ ⟨8, 8, 6, 4096, 8⟩ ⟨8, 8, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr8_ctfe_corr pvCt rfl 0 16 0 0 0 0 0 0 ⟨7, 7, 0, 4096, 8⟩ ⟨7, 7, 1, 4096, 8⟩ ⟨7, 7, 2, 4096, 8⟩ ⟨7, 7, 3, 4096, 8⟩ ⟨8, 8, 4, 4096, 8⟩ ⟨8, 8, 5, 4096, 8⟩ ⟨8, 8, 6, 4096, 8⟩ ⟨8, 8, 7, 4096, 8⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the intact 32-bit pointer `q`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_intact32 :
    lQ = [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)]) 0 4 = .ok (some (pvRt 9 9)) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)]) 0 4 = .ok (some (pvCt 9 9)) ∧
    decodePtrBytesNoForge false (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)] = some (.ptr ⟨9, 4096⟩ 4) ∧
    decodePtrBytesNoForge true (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 0 (some ⟨9, 9, 3, 4096, 4⟩)] = some (.ptr ⟨9, 4096⟩ 4) :=
  ⟨rfl, (readPtr4_runtime_corr pvRt rfl 0 16 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 3, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr4_ctfe_corr pvCt rfl 0 16 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 3, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 4-byte full reversal of `q`.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_reversal32 :
    lQ.reverse = [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)]) 0 4 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)]) 0 4 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 4 [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)] = some (.scalar ⟨1048576, 4⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 4 [.init 0 (some ⟨9, 9, 3, 4096, 4⟩), .init 0 (some ⟨9, 9, 2, 4096, 4⟩), .init 16 (some ⟨9, 9, 1, 4096, 4⟩), .init 0 (some ⟨9, 9, 0, 4096, 4⟩)] = none :=
  ⟨rfl, (readPtr4_runtime_corr pvRt rfl 0 0 16 0 ⟨9, 9, 3, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 0, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr4_ctfe_corr pvCt rfl 0 0 16 0 ⟨9, 9, 3, 4096, 4⟩ ⟨9, 9, 2, 4096, 4⟩ ⟨9, 9, 1, 4096, 4⟩ ⟨9, 9, 0, 4096, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Three-way witness: the 32-bit `q` / `q + 256` offset splice.** `Trusted` (raw pointer and reference), vendored
`ProvenanceMap.readPtr` with Miri runtime provenance, and vendored `readPtr` with CTFE provenance,
all instantiating the universal correspondence theorems. -/
theorem w_lm_splice32_q_q256 :
    lQ.take 1 ++ lQ256.drop 1 = [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)] ∧
    trRead (trEntries pvRt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)]) 0 4 = .ok (none) ∧
    trRead (trEntries pvCt [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)]) 0 4 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)] = some (.scalar ⟨4352, 4⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 4 [.init 0 (some ⟨9, 9, 0, 4096, 4⟩), .init 17 (some ⟨9, 9, 1, 4352, 4⟩), .init 0 (some ⟨9, 9, 2, 4352, 4⟩), .init 0 (some ⟨9, 9, 3, 4352, 4⟩)] = none :=
  ⟨rfl, (readPtr4_runtime_corr pvRt rfl 0 17 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4352, 4⟩ ⟨9, 9, 2, 4352, 4⟩ ⟨9, 9, 3, 4352, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl,
   (readPtr4_ctfe_corr pvCt rfl 0 17 0 0 ⟨9, 9, 0, 4096, 4⟩ ⟨9, 9, 1, 4352, 4⟩ ⟨9, 9, 2, 4352, 4⟩ ⟨9, 9, 3, 4352, 4⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ ⟨rfl, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl, rfl, rfl⟩

/-- **Missing provenance and uninitialized bytes.** A plain byte (or an uninitialized byte)
contributes no fragment, so the translated state is the shared `entriesMissing1`, which vendored
`readPtr` reads without provenance (runtime) / as a partial pointer (CTFE); `Trusted` reads a raw
pointer as a plain integer, rejects a reference, and rejects the uninitialized stream outright. -/
theorem w_lm_missing_and_uninit :
    trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = entriesMissing1 pvRt ∧
    trEntries pvRt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .uninit, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = entriesMissing1 pvRt ∧
    trEntries pvCt [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = entriesMissing1 pvCt ∧
    trRead (entriesMissing1 pvRt) 0 8 = .ok none ∧
    trRead (entriesMissing1 pvCt) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = some (.scalar ⟨4096, 8⟩) ∧
    decodePtrBytesNoForge true (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .init 16 none, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = none ∧
    decodePtrBytesNoForge false (.uint .u8) 8 [.init 0 (some ⟨7, 7, 0, 4096, 8⟩), .uninit, .init 0 (some ⟨7, 7, 2, 4096, 8⟩), .init 0 (some ⟨7, 7, 3, 4096, 8⟩), .init 0 (some ⟨7, 7, 4, 4096, 8⟩), .init 0 (some ⟨7, 7, 5, 4096, 8⟩), .init 0 (some ⟨7, 7, 6, 4096, 8⟩), .init 0 (some ⟨7, 7, 7, 4096, 8⟩)] = none :=
  ⟨rfl, rfl, rfl, w_lm_missing_miri_rt, w_lm_missing_miri_ct, rfl, rfl, rfl⟩

def wUnitL : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }
def wU8L : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wCharL : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wU32L : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }
def wLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L] }
def wTyU8 : Ty := { kind := .uint .u8, layoutIdx := 1 }
def wTyBool : Ty := { kind := .bool, layoutIdx := 2 }
def wTyChar : Ty := { kind := .char, layoutIdx := 3 }
def wTyU32 : Ty := { kind := .uint .u32, layoutIdx := 4 }

/-- **`Kani#5205` (`Trusted` half).** `2u8` and the surrogate `0xD800` are representable as
untyped bytes (`u8`, `u32`, the raw-byte carrier) — writing them is not UB — and are rejected
(`none`, the `.ub` read fault) by the typed `bool` / `char` decode; the vendored Miri half is
`w_lm_kani5205_miri`. -/
theorem w_lm_kani5205_trusted :
    encodeUntypedValueToBytes 1 (.scalar ⟨2, 1⟩) = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU8 [.init 2 none] =
      some (.scalar ⟨2, 1⟩) ∧
    decodeRawAbstractByteVals? [encodeRawAbstractByteVal (.init 2 none)] = some [.init 2 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 2 none] = none ∧
    validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨2, 1⟩) = false ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init 1 none] =
      some (.scalar ⟨1, 1⟩) ∧
    encodeUntypedValueToBytes 1 (.scalar ⟨0xD800, 4⟩) =
      some [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none] ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyU32
      [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none] =
      some (.scalar ⟨0xD800, 4⟩) ∧
    decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyChar
      [.init 0x00 none, .init 0xD8 none, .init 0x00 none, .init 0x00 none] = none ∧
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨0xD800, 4⟩) = false := by
  repeat first | refine ⟨?_, ?_⟩ | rfl

/-- Non-vacuous instantiations of the byte-vector injectivity law (`4` and `8` bytes). -/
theorem normOffset_image_inj_instance :
    ptrImage 8 (normPtrByteOffset 8 0x1000) ≠ ptrImage 8 (normPtrByteOffset 8 0x1100) ∧
    ptrImage 4 (normPtrByteOffset 4 0x1000) ≠ ptrImage 4 (normPtrByteOffset 4 0x1100) ∧
    ptrImage 4 (normPtrByteOffset 4 0x1000) = ptrImage 4 (normPtrByteOffset 4 0x100001000) :=
  ⟨fun h => absurd ((normOffset_image_inj 8 _ _ (by decide)).mp h) (by decide),
   fun h => absurd ((normOffset_image_inj 4 _ _ (by decide)).mp h) (by decide),
   (normOffset_image_inj 4 _ _ (by decide)).mpr (by decide)⟩

end Witnesses

/-! ### §5. Truly universal all-bytes correspondence (including plain & `.uninit` bytes), intact & carrier round-trips, wide pointers, and universal / end-to-end `Kani#5205` -/

theorem trEntriesAux_keys_ge {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte) (e : Size × PointerFrag Prov),
      start + bs.length < 2 ^ 64 →
      e ∈ trEntriesAux pv start bs →
      start ≤ e.1.bytes.toNat ∧ e.1.bytes.toNat < start + bs.length
  | _, [], _, _, h => by cases h
  | start, b :: rest, e, hbd, h => by
    simp only [trEntriesAux] at h
    cases hf : fragOf pv b with
    | none =>
      rw [hf] at h
      have ih := trEntriesAux_keys_ge pv (start + 1) rest e (by simp only [List.length_cons] at hbd; omega) h
      simp only [List.length_cons]; omega
    | some g =>
      rw [hf] at h
      cases h with
      | head =>
        simp only [Size.ofBytes, UInt64.toNat_ofNat', List.length_cons]
        have : start < 2 ^ 64 := by simp only [List.length_cons] at hbd; omega
        rw [Nat.mod_eq_of_lt this]; omega
      | tail _ hr =>
        have ih := trEntriesAux_keys_ge pv (start + 1) rest e (by simp only [List.length_cons] at hbd; omega) hr
        simp only [List.length_cons]; omega

theorem trEntriesAux_sorted {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte),
      start + bs.length < 2 ^ 64 →
      ∃ pm, ProvenanceMap.fromParts #[] (some (trEntriesAux pv start bs).toArray) = .ok pm := by
  intro start bs hbd
  have hsorted : ∀ (s : Nat) (l : List AbstractByte), s + l.length < 2 ^ 64 →
      (ProvenanceMap.fromParts #[] (some (trEntriesAux pv s l).toArray)).isOk = true := by
    intro s l
    induction l generalizing s with
    | nil =>
      intro _
      unfold ProvenanceMap.fromParts
      simp only [trEntriesAux, Option.map_some, Option.getD_some, Array.toList_empty, List.toList_toArray]
      simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
      rfl
    | cons b rest ih =>
      intro hbd'
      simp only [trEntriesAux]
      cases hf : fragOf pv b with
      | none => exact ih (s + 1) (by simp only [List.length_cons] at hbd'; omega)
      | some g =>
        have ih' := ih (s + 1) (by simp only [List.length_cons] at hbd'; omega)
        unfold ProvenanceMap.fromParts at ih' ⊢
        simp only [Option.map_some, Option.getD_some, Array.toList_empty, List.toList_toArray] at ih' ⊢
        cases hrest : trEntriesAux pv (s + 1) rest with
        | nil =>
          simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
          rfl
        | cons hd tl =>
          have hge := trEntriesAux_keys_ge pv (s + 1) rest hd
            (by simp only [List.length_cons] at hbd'; omega) (by rw [hrest]; exact List.Mem.head _)
          have hs_lt : s < 2 ^ 64 := by simp only [List.length_cons] at hbd'; omega
          obtain ⟨hd_s, hd_f⟩ := hd
          dsimp only at hge
          have hlt : (Size.ofBytes (UInt64.ofNat s)).bytes < hd_s.bytes := by
            simp only [Size.ofBytes, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hs_lt]
            omega
          rw [hrest] at ih'
          split at ih'
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            simp_miri_private Miri.Memory.ProvenanceMap Miri.Memory.ProvenanceMap.sortedKeys
            simp [hlt, hcond.2]
            rfl
          · cases ih'
  have hok := hsorted start bs hbd
  cases h : ProvenanceMap.fromParts #[] (some (trEntriesAux pv start bs).toArray) with
  | ok pm => exact ⟨pm, rfl⟩
  | error e => rw [h] at hok; cases hok

theorem mem_trEntriesAux_iff {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte) (e : Size × PointerFrag Prov),
      start + bs.length < 2 ^ 64 →
      (e ∈ trEntriesAux pv start bs ↔
        ∃ (i : Nat) (b : AbstractByte) (g : PointerFrag Prov),
          bs[i]? = some b ∧ fragOf pv b = some g ∧
          e = (Size.ofBytes (UInt64.ofNat (start + i)), g))
  | _, [], e, _ => by simp [trEntriesAux]
  | start, b :: rest, e, hbd => by
    simp only [trEntriesAux]
    have hbd' : start + 1 + rest.length < 2 ^ 64 := by simp only [List.length_cons] at hbd; omega
    cases hf : fragOf pv b with
    | none =>
      rw [mem_trEntriesAux_iff pv (start + 1) rest e hbd']
      constructor
      · rintro ⟨i, b', g, hget, hfg, rfl⟩
        refine ⟨i + 1, b', g, hget, hfg, ?_⟩
        have : start + 1 + i = start + (i + 1) := by omega
        rw [this]
      · rintro ⟨i, b', g, hget, hfg, rfl⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hget; subst hget; rw [hf] at hfg; cases hfg
        | succ j =>
          refine ⟨j, b', g, hget, hfg, ?_⟩
          have : start + (j + 1) = start + 1 + j := by omega
          rw [this]
    | some g0 =>
      simp only [List.mem_cons]
      rw [mem_trEntriesAux_iff pv (start + 1) rest e hbd']
      constructor
      · rintro (rfl | ⟨i, b', g, hget, hfg, rfl⟩)
        · exact ⟨0, b, g0, rfl, hf, by simp⟩
        · refine ⟨i + 1, b', g, hget, hfg, ?_⟩
          have : start + 1 + i = start + (i + 1) := by omega
          rw [this]
      · rintro ⟨i, b', g, hget, hfg, rfl⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hget; subst hget; rw [hf] at hfg
          injection hfg with hfg; subst hfg; left; simp
        | succ j =>
          right
          refine ⟨j, b', g, hget, hfg, ?_⟩
          have : start + (j + 1) = start + 1 + j := by omega
          rw [this]

theorem trEntries_eq_empty_of_no_prov {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (start : Nat) (bs : List AbstractByte),
      abstractBytesHaveProv bs = false → trEntriesAux pv start bs = []
  | _, [], _ => rfl
  | start, .uninit :: rest, h => trEntries_eq_empty_of_no_prov pv (start + 1) rest h
  | start, .init _ none :: rest, h => trEntries_eq_empty_of_no_prov pv (start + 1) rest h
  | _, .init _ (some _) :: _, h => by cases h

theorem exists_prov_of_haveProv :
    ∀ (bs : List AbstractByte),
      abstractBytesHaveProv bs = true →
      ∃ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f))
  | [], h => by cases h
  | .uninit :: rest, h => by
    obtain ⟨i, v, f, hi⟩ := exists_prov_of_haveProv rest h
    exact ⟨i + 1, v, f, hi⟩
  | .init _ none :: rest, h => by
    obtain ⟨i, v, f, hi⟩ := exists_prov_of_haveProv rest h
    exact ⟨i + 1, v, f, hi⟩
  | .init v (some f) :: _, _ => ⟨0, v, f, rfl⟩

theorem coh?_none_of_no_frag :
    ∀ (bs : List AbstractByte) (i : Nat) (b : AbstractByte),
      bs[i]? = some b → (∀ v f, b ≠ .init v (some f)) →
      abstractBytesCoherentPtrProv? bs = none := by
  have aux : ∀ (a t o pb idx : Nat) (bs : List AbstractByte) (i : Nat) (b : AbstractByte),
      bs[i]? = some b → (∀ v f, b ≠ .init v (some f)) →
      abstractBytesCoherentPtrProvAux a t o pb idx bs = false := by
    intro a t o pb idx bs
    induction bs generalizing idx with
    | nil => intro i b h; cases h
    | cons x rest ih =>
      intro i b h hnf
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at h
        injection h with h; subst h
        cases x with
        | uninit => rfl
        | init v pr => cases pr with | none => rfl | some f => exact absurd rfl (hnf v f)
      | succ j =>
        cases x with
        | uninit => rfl
        | init v pr =>
          cases pr with
          | none => rfl
          | some f =>
            show Bool.and _ (abstractBytesCoherentPtrProvAux a t o pb (Nat.add idx 1) rest) = false
            rw [ih (Nat.add idx 1) j b h hnf]; simp
  intro bs i b h hnf
  cases bs with
  | nil => cases h
  | cons x rest =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at h
      injection h with h; subst h
      cases x with
      | uninit => rfl
      | init v pr => cases pr with | none => rfl | some f => exact absurd rfl (hnf v f)
    | succ j =>
      cases x with
      | uninit => rfl
      | init v pr =>
        cases pr with
        | none => rfl
        | some f =>
          show (match Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) with
            | true => some f | false => none) = none
          rw [aux f.allocId f.tag f.origOffset f.ptrBytes 1 rest j b h hnf]; simp

theorem list_all_frag_or_missing (bs : List AbstractByte) :
    (∀ (i : Nat) (b : AbstractByte), bs[i]? = some b → ∃ v f, b = .init v (some f)) ∨
    (∃ (i : Nat) (b : AbstractByte), i < bs.length ∧ bs[i]? = some b ∧ ∀ v f, b ≠ .init v (some f)) := by
  induction bs with
  | nil => left; intro i b h; cases h
  | cons x rest ih =>
    cases x with
    | uninit => right; exact ⟨0, .uninit, by simp, rfl, fun _ _ h => by cases h⟩
    | init v pr =>
      cases pr with
      | none => right; exact ⟨0, .init v none, by simp, rfl, fun _ _ h => by injection h with _ h; cases h⟩
      | some f =>
        rcases ih with hall | ⟨i, b, hlt, hb, hnf⟩
        · left; intro i b hb
          cases i with
          | zero => simp only [List.getElem?_cons_zero] at hb; injection hb with hb; subst hb; exact ⟨v, f, rfl⟩
          | succ j => exact hall j b hb
        · right; exact ⟨i + 1, b, by simp; omega, hb, hnf⟩

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
4-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr4_allBytes_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 4 =
      .ok ((abstractBytesCoherentPtrProv? bs).map fun f => pv f.allocId f.tag) := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    have hcorr := readPtr4_runtime_corr pv hoff v0 v1 v2 v3 f0 f1 f2 f3
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]; dsimp only [Option.map]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]; exact trRead_empty 4 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries; rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 4 := by
        cases Nat.lt_or_ge j 4 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq; rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 4 := by
          cases Nat.lt_or_ge i 4 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 4 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr4_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE mode,
4-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr4_allBytes_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 4 =
      match abstractBytesCoherentPtrProv? bs with
      | some f => .ok (some (pv f.allocId f.tag))
      | none =>
        if abstractBytesHaveProv bs then .error (.readPartialPointer (Size.ofBytes 0))
        else .ok none := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    have hcorr := readPtr4_ctfe_corr pv hoff v0 v1 v2 v3 f0 f1 f2 f3
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]; exact trRead_empty 4 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries; rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 4 := by
        cases Nat.lt_or_ge j 4 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq; rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 4 := by
          cases Nat.lt_or_ge i 4 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 4 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr4_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (runtime mode,
8-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr8_allBytes_runtime_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 8 =
      .ok ((abstractBytesCoherentPtrProv? bs).map fun f => pv f.allocId f.tag) := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    obtain ⟨v4, f4, rfl⟩ := hall 4 b4 rfl
    obtain ⟨v5, f5, rfl⟩ := hall 5 b5 rfl
    obtain ⟨v6, f6, rfl⟩ := hall 6 b6 rfl
    obtain ⟨v7, f7, rfl⟩ := hall 7 b7 rfl
    have hcorr := readPtr8_runtime_corr pv hoff v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hwf 4 _ _ rfl) (hwf 5 _ _ rfl) (hwf 6 _ _ rfl) (hwf 7 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hnw 4 _ _ rfl) (hnw 5 _ _ rfl) (hnw 6 _ _ rfl) (hnw 7 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
      (hinj 4 0 _ _ _ _ rfl rfl) (hinj 5 0 _ _ _ _ rfl rfl) (hinj 6 0 _ _ _ _ rfl rfl)
      (hinj 7 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]; dsimp only [Option.map]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]; exact trRead_empty 8 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries; rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 8 := by
        cases Nat.lt_or_ge j 8 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq; rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 8 := by
          cases Nat.lt_or_ge i 8 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 8 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr8_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- **Truly universal `Trusted` ↔ vendored `ProvenanceMap.readPtr` correspondence (CTFE mode,
8-byte pointers, ALL byte streams — fragmented, plain, or `.uninit`).** -/
theorem readPtr8_allBytes_ctfe_corr {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    trRead (trEntries pv bs) 0 8 =
      match abstractBytesCoherentPtrProv? bs with
      | some f => .ok (some (pv f.allocId f.tag))
      | none =>
        if abstractBytesHaveProv bs then .error (.readPartialPointer (Size.ofBytes 0))
        else .ok none := by
  rcases list_all_frag_or_missing bs with hall | ⟨k, bk, hkl, hbk, hnf⟩
  · rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
    obtain ⟨v0, f0, rfl⟩ := hall 0 b0 rfl
    obtain ⟨v1, f1, rfl⟩ := hall 1 b1 rfl
    obtain ⟨v2, f2, rfl⟩ := hall 2 b2 rfl
    obtain ⟨v3, f3, rfl⟩ := hall 3 b3 rfl
    obtain ⟨v4, f4, rfl⟩ := hall 4 b4 rfl
    obtain ⟨v5, f5, rfl⟩ := hall 5 b5 rfl
    obtain ⟨v6, f6, rfl⟩ := hall 6 b6 rfl
    obtain ⟨v7, f7, rfl⟩ := hall 7 b7 rfl
    have hcorr := readPtr8_ctfe_corr pv hoff v0 v1 v2 v3 v4 v5 v6 v7 f0 f1 f2 f3 f4 f5 f6 f7
      (hwf 0 _ _ rfl) (hwf 1 _ _ rfl) (hwf 2 _ _ rfl) (hwf 3 _ _ rfl)
      (hwf 4 _ _ rfl) (hwf 5 _ _ rfl) (hwf 6 _ _ rfl) (hwf 7 _ _ rfl)
      (hnw 0 _ _ rfl) (hnw 1 _ _ rfl) (hnw 2 _ _ rfl) (hnw 3 _ _ rfl)
      (hnw 4 _ _ rfl) (hnw 5 _ _ rfl) (hnw 6 _ _ rfl) (hnw 7 _ _ rfl)
      (hinj 1 0 _ _ _ _ rfl rfl) (hinj 2 0 _ _ _ _ rfl rfl) (hinj 3 0 _ _ _ _ rfl rfl)
      (hinj 4 0 _ _ _ _ rfl rfl) (hinj 5 0 _ _ _ _ rfl rfl) (hinj 6 0 _ _ _ _ rfl rfl)
      (hinj 7 0 _ _ _ _ rfl rfl)
    rw [hcorr]
    cases hcoh : abstractBytesCoherentPtrProv? [.init v0 (some f0), .init v1 (some f1), .init v2 (some f2), .init v3 (some f3), .init v4 (some f4), .init v5 (some f5), .init v6 (some f6), .init v7 (some f7)] with
    | none => rfl
    | some f =>
      have hf0 : f = f0 := by
        dsimp only [abstractBytesCoherentPtrProv?] at hcoh
        cases hb : Bool.and (Nat.blt 0 f0.ptrBytes) (Bool.and (Nat.beq f0.byteIdx 0)
            (abstractBytesCoherentPtrProvAux f0.allocId f0.tag f0.origOffset f0.ptrBytes 1 _)) with
        | false => rw [hb] at hcoh; cases hcoh
        | true => rw [hb] at hcoh; injection hcoh with h; exact h.symm
      subst hf0; rfl
  · have hcoh : abstractBytesCoherentPtrProv? bs = none := coh?_none_of_no_frag bs k bk hbk hnf
    rw [hcoh]
    cases hp : abstractBytesHaveProv bs with
    | false =>
      have hempty : trEntries pv bs = #[] := by
        unfold trEntries; rw [trEntries_eq_empty_of_no_prov pv 0 bs hp]
      rw [hempty]; exact trRead_empty 8 (by decide)
    | true =>
      obtain ⟨pm, hpm⟩ := trEntriesAux_sorted pv 0 bs (by omega)
      obtain ⟨hptrs, hfrags⟩ := fromParts_fields _ _ pm hpm
      unfold trRead trEntries; rw [hpm]; dsimp only
      obtain ⟨j, vj, fj, hbj⟩ := exists_prov_of_haveProv bs hp
      have hjlt : j < 8 := by
        cases Nat.lt_or_ge j 8 with
        | inl h => exact h
        | inr hge =>
          have : bs.length ≤ j := by omega
          rw [List.getElem?_eq_none this] at hbj; cases hbj
      have hmemj : (Size.ofBytes (UInt64.ofNat (0 + j)), mkFrag pv fj) ∈ (trEntriesAux pv 0 bs).toArray := by
        rw [List.mem_toArray]
        exact (mem_trEntriesAux_iff pv 0 bs _ (by omega)).mpr ⟨j, _, _, hbj, rfl, rfl⟩
      have hmiss : ∀ e ∈ (trEntriesAux pv 0 bs).toArray, e.1.bytes ≠ UInt64.ofNat k := by
        intro e he hkeq; rw [List.mem_toArray] at he
        obtain ⟨i, bi, gi, hbi, hfg, rfl⟩ := (mem_trEntriesAux_iff pv 0 bs e (by omega)).mp he
        have hilt : i < 8 := by
          cases Nat.lt_or_ge i 8 with
          | inl h => exact h
          | inr hge =>
            have : bs.length ≤ i := by omega
            rw [List.getElem?_eq_none this] at hbi; cases hbi
        have hik : i = k := by
          simp only [Size.ofBytes, Nat.zero_add] at hkeq
          have := congrArg UInt64.toNat hkeq; simp only [UInt64.toNat_ofNat'] at this
          have hi64 : i < 2 ^ 64 := by omega
          have hk64 : k < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hk64] at this; exact this
        subst hik; rw [hbk] at hbi; injection hbi with hbi; subst hbi
        cases bk with
        | uninit => cases hfg
        | init v pr => cases pr with | none => cases hfg | some f => exact hnf v f rfl
      have hltj : (Size.ofBytes (UInt64.ofNat (0 + j))).bytes < 8 := by
        simp only [Size.ofBytes, Nat.zero_add, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        have hj64 : j < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hj64]; simpa using hjlt
      have hread := readPtr8_missing_byte_strips pm (trEntriesAux pv 0 bs).toArray hptrs hfrags
        ⟨_, hmemj, hltj⟩ ⟨k, by omega, hmiss⟩
      simpa [hoff] using hread

/-- Explicit biconditional form of `readPtr8_allBytes_runtime_corr`. -/
theorem readPtr8_allBytes_runtime_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 8 = .ok (some p)) ∧
    (abstractBytesCoherentPtrProv? bs = none ↔
      trRead (trEntries pv bs) 0 8 = .ok none) := by
  have h := readPtr8_allBytes_runtime_corr pv hoff bs hlen hwf hnw hinj
  rw [h]; cases abstractBytesCoherentPtrProv? bs <;> simp

/-- Explicit biconditional form of `readPtr4_allBytes_runtime_corr` (32-bit). -/
theorem readPtr4_allBytes_runtime_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = true)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 4 = .ok (some p)) ∧
    (abstractBytesCoherentPtrProv? bs = none ↔
      trRead (trEntries pv bs) 0 4 = .ok none) := by
  have h := readPtr4_allBytes_runtime_corr pv hoff bs hlen hwf hnw hinj
  rw [h]; cases abstractBytesCoherentPtrProv? bs <;> simp

/-- **Explicit CTFE biconditionals (`8`-byte pointers).** In CTFE strict partial-pointer mode,
vendored `readPtr` of the translated state retains provenance iff `Trusted` finds the stream
coherent; it is the `readPartialPointer` error iff the stream is incoherent but carries some
provenance fragment; and it is `.ok none` iff the stream carries no provenance fragment at all. -/
theorem readPtr8_allBytes_ctfe_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 8)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 8 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = true) ↔
      trRead (trEntries pv bs) 0 8 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = false) ↔
      trRead (trEntries pv bs) 0 8 = .ok none) := by
  rw [readPtr8_allBytes_ctfe_corr pv hoff bs hlen hwf hnw hinj]
  cases abstractBytesCoherentPtrProv? bs with
  | none => cases abstractBytesHaveProv bs <;> simp
  | some f => cases abstractBytesHaveProv bs <;> simp

/-- **Explicit CTFE biconditionals (`4`-byte pointers).** In CTFE strict partial-pointer mode,
vendored `readPtr` of the translated state retains provenance iff `Trusted` finds the stream
coherent; it is the `readPartialPointer` error iff the stream is incoherent but carries some
provenance fragment; and it is `.ok none` iff the stream carries no provenance fragment at all. -/
theorem readPtr4_allBytes_ctfe_iff {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (hoff : PointerProvenance.offsetIsAddr (Prov := Prov) = false)
    (bs : List AbstractByte) (hlen : bs.length = 4)
    (hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f)
    (hnw : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) →
      ¬ some (pv f.allocId f.tag) = PointerProvenance.wildcard (Prov := Prov))
    (hinj : ∀ (i j : Nat) (vi vj : UInt8) (fi fj : PtrByteFrag),
      bs[i]? = some (.init vi (some fi)) → bs[j]? = some (.init vj (some fj)) →
      pv fi.allocId fi.tag = pv fj.allocId fj.tag → fi.allocId = fj.allocId ∧ fi.tag = fj.tag) :
    ((∃ f, abstractBytesCoherentPtrProv? bs = some f) ↔
      ∃ p, trRead (trEntries pv bs) 0 4 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = true) ↔
      trRead (trEntries pv bs) 0 4 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? bs = none ∧ abstractBytesHaveProv bs = false) ↔
      trRead (trEntries pv bs) 0 4 = .ok none) := by
  rw [readPtr4_allBytes_ctfe_corr pv hoff bs hlen hwf hnw hinj]
  cases abstractBytesCoherentPtrProv? bs with
  | none => cases abstractBytesHaveProv bs <;> simp
  | some f => cases abstractBytesHaveProv bs <;> simp

/-- Helper: decoding LE bits of `encodePtrBytesAux` yields `bits % 256 ^ n`. -/
theorem decodeLittleEndianBits_encodePtrBytesAux (a t o pb : Nat) :
    ∀ (n bits idx : Nat),
      decodeLittleEndianBits (encodePtrBytesAux a t o pb bits idx n) = some (bits % 256 ^ n)
  | 0, bits, _ => by simp [decodeLittleEndianBits, encodePtrBytesAux, Nat.mod_one]
  | n + 1, bits, idx => by
    show (match decodeLittleEndianBits (encodePtrBytesAux a t o pb (bits / 256) (idx + 1) n) with
      | some hi => some (Nat.add (UInt8.ofNat bits).toBitVec.toNat (Nat.mul 256 hi))
      | none => none) = some (bits % 256 ^ (n + 1))
    rw [decodeLittleEndianBits_encodePtrBytesAux a t o pb n (bits / 256) (idx + 1)]
    show some ((UInt8.ofNat bits).toNat + 256 * (bits / 256 % 256 ^ n)) = some (bits % 256 ^ (n + 1))
    rw [u8_ofNat_toNat, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

theorem rawCarrier_roundtrip_lm :
    ∀ bs : List AbstractByte,
      decodeRawAbstractByteVals? (bs.map encodeRawAbstractByteVal) = some bs
  | [] => rfl
  | .uninit :: rest => by
    show (match some AbstractByte.uninit, decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
      | some b', some bs' => some (b' :: bs') | _, _ => none) = _
    rw [rawCarrier_roundtrip_lm rest]
  | .init v none :: rest => by
    have h1 : decodeRawAbstractByteVal? (encodeRawAbstractByteVal (.init v none)) = some (.init v none) := by
      show decodeRawAbstractByteVal? (.scalar ⟨v.toBitVec.toNat, 1⟩) = _
      unfold decodeRawAbstractByteVal?
      split <;> simp_all <;> (rename_i hb; subst hb; exact UInt8.ofNat_toNat)
    show (match decodeRawAbstractByteVal? (encodeRawAbstractByteVal (.init v none)),
        decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
      | some b', some bs' => some (b' :: bs') | _, _ => none) = _
    rw [h1, rawCarrier_roundtrip_lm rest]
  | .init v (some f) :: rest => by
    have hv : UInt8.ofNat v.toBitVec.toNat = v := UInt8.ofNat_toNat
    show (match some (AbstractByte.init (UInt8.ofNat v.toBitVec.toNat) (some f)),
        decodeRawAbstractByteVals? (rest.map encodeRawAbstractByteVal) with
      | some b', some bs' => some (b' :: bs') | _, _ => none) = _
    rw [hv, rawCarrier_roundtrip_lm rest]

/-- **Universal intact 64-bit pointer round-trip (`Trusted` ↔ vendored `ProvenanceMap.readPtr`).** -/
theorem intact_roundtrip_8 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    let bs := encodePtrBytes bits 8 a t
    decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 8 } 8) ∧
    trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt a t)) ∧
    trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt a t)) := by
  intro bs
  have hbits : decodeLittleEndianBits bs = some (bits % 256 ^ 8) :=
    decodeLittleEndianBits_encodePtrBytesAux a t _ 8 8 bits 0
  have hcoh : abstractBytesCoherentPtrProv? bs = some ⟨a, t, 0, normPtrByteOffset 8 bits, 8⟩ := by
    simp (config := { decide := true }) [bs, encodePtrBytes, encodePtrBytesAux,
      abstractBytesCoherentPtrProv?, abstractBytesCoherentPtrProvAux]
    rfl
  have hdec : decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 8 } 8) := by
    unfold decodePtrBytesNoForge; have hlen : length bs = 8 := rfl
    simp (config := { decide := true }) [hlen, hbits, hcoh]
    rfl
  have hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 8 f := by
    intro i v f hi
    obtain ⟨v', f', hv, _, hwf⟩ := encodePtrBytes_wf bits 8 a t i _ hi
    injection hv with _ hf; injection hf with hf; subst hf; exact hwf
  have hrt : trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt a t)) := by
    have h := readPtr8_allBytes_runtime_corr pvRt rfl bs rfl hwf
      (fun i v f hi => by
        obtain ⟨_, _, hv, hf, _⟩ := encodePtrBytes_wf bits 8 a t i _ hi
        injection hv with _ he; injection he with he; subst he; subst hf
        exact pvRt_ne_wildcard a t ha ht)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 8 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 8 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]; rfl
  have hct : trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt a t)) := by
    have h := readPtr8_allBytes_ctfe_corr pvCt rfl bs rfl hwf
      (fun i v f hi => by intro hw; cases hw)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 8 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 8 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]
  exact ⟨hdec, hrt, hct⟩

/-- **Universal intact 32-bit pointer round-trip (`Trusted` ↔ vendored `ProvenanceMap.readPtr`).** -/
theorem intact_roundtrip_4 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    let bs := encodePtrBytes bits 4 a t
    decodePtrBytesNoForge isRef (.uint .u8) 4 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 4 } 4) ∧
    trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt a t)) ∧
    trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt a t)) := by
  intro bs
  have hbits : decodeLittleEndianBits bs = some (bits % 256 ^ 4) :=
    decodeLittleEndianBits_encodePtrBytesAux a t _ 4 4 bits 0
  have hcoh : abstractBytesCoherentPtrProv? bs = some ⟨a, t, 0, normPtrByteOffset 4 bits, 4⟩ := by
    simp (config := { decide := true }) [bs, encodePtrBytes, encodePtrBytesAux,
      abstractBytesCoherentPtrProv?, abstractBytesCoherentPtrProvAux]
    rfl
  have hdec : decodePtrBytesNoForge isRef (.uint .u8) 4 bs =
      some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 4 } 4) := by
    unfold decodePtrBytesNoForge; have hlen : length bs = 4 := rfl
    simp (config := { decide := true }) [hlen, hbits, hcoh]
    rfl
  have hwf : ∀ (i : Nat) (v : UInt8) (f : PtrByteFrag), bs[i]? = some (.init v (some f)) → WF 4 f := by
    intro i v f hi
    obtain ⟨v', f', hv, _, hwf⟩ := encodePtrBytes_wf bits 4 a t i _ hi
    injection hv with _ hf; injection hf with hf; subst hf; exact hwf
  have hrt : trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt a t)) := by
    have h := readPtr4_allBytes_runtime_corr pvRt rfl bs rfl hwf
      (fun i v f hi => by
        obtain ⟨_, _, hv, hf, _⟩ := encodePtrBytes_wf bits 4 a t i _ hi
        injection hv with _ he; injection he with he; subst he; subst hf
        exact pvRt_ne_wildcard a t ha ht)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 4 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 4 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]; rfl
  have hct : trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt a t)) := by
    have h := readPtr4_allBytes_ctfe_corr pvCt rfl bs rfl hwf
      (fun i v f hi => by intro hw; cases hw)
      (fun i j vi vj fi fj hi hj _ => by
        obtain ⟨_, _, hvi, hfi, _⟩ := encodePtrBytes_wf bits 4 a t i _ hi
        obtain ⟨_, _, hvj, hfj, _⟩ := encodePtrBytes_wf bits 4 a t j _ hj
        injection hvi with _ hei; injection hei with hei; subst hei; subst hfi
        injection hvj with _ hej; injection hej with hej; subst hej; subst hfj
        exact ⟨rfl, rfl⟩)
    rw [h, hcoh]
  exact ⟨hdec, hrt, hct⟩

/-- **Universal union raw-byte carrier pointer round-trip (64-bit, `Trusted` ↔ vendored Miri).** -/
theorem rawCarrier_ptr_roundtrip_8 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    ∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes bits 8 a t).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge isRef (.uint .u8) 8 bs =
        some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 8 } 8) ∧
      trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt a t)) ∧
      trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt a t)) :=
  let ⟨h1, h2, h3⟩ := intact_roundtrip_8 isRef bits a t ha ht
  ⟨encodePtrBytes bits 8 a t, rawCarrier_roundtrip_lm _, h1, h2, h3⟩

/-- **Universal union raw-byte carrier pointer round-trip (32-bit, `Trusted` ↔ vendored Miri).** -/
theorem rawCarrier_ptr_roundtrip_4 (isRef : Bool) (bits a t : Nat)
    (ha : a + 1 < 2 ^ 64) (ht : t + 1 < 2 ^ 64) :
    ∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes bits 4 a t).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge isRef (.uint .u8) 4 bs =
        some (.ptr { allocId := a, offsetBytes := bits % 256 ^ 4 } 4) ∧
      trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt a t)) ∧
      trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt a t)) :=
  let ⟨h1, h2, h3⟩ := intact_roundtrip_4 isRef bits a t ha ht
  ⟨encodePtrBytes bits 4 a t, rawCarrier_roundtrip_lm _, h1, h2, h3⟩

section WideAndKani

open Trusted.Rustc.V2026_08_01.Layout

def lLen64 : List AbstractByte := encodePlainLittleEndianBytes 3 8
def lLen32 : List AbstractByte := encodePlainLittleEndianBytes 3 4
def lVt64 : List AbstractByte := encodePtrBytes 0x80 8 42 42
def lVt32 : List AbstractByte := encodePtrBytes 0x20 4 43 43

/-- **Wide slice & `str` pointers (64-bit & 32-bit) against vendored `ProvenanceMap.readPtr`.** -/
theorem w_lm_wide_slice_and_str :
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lP ++ lLen64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (lP ++ lLen64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    decodePtrBytesNoForge true .str 8 (lP ++ lLen64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨3, 8⟩]) ∧
    trRead (trEntries pvRt (lP ++ lLen64)) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (trEntries pvRt (lP ++ lLen64)) 8 8 = .ok none ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 4 (lQ ++ lLen32) =
      some (.aggregate 0 [.ptr ⟨9, 0x1000⟩ 4, .scalar ⟨3, 4⟩]) ∧
    trRead (trEntries pvRt (lQ ++ lLen32)) 0 4 = .ok (some (pvRt 9 9)) ∧
    trRead (trEntries pvRt (lQ ++ lLen32)) 4 4 = .ok none ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lP.reverse ++ lLen64) = none ∧
    trRead (trEntries pvRt (lP.reverse ++ lLen64)) 0 8 = .ok none ∧
    decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lLen64 ++ lP) = none ∧
    decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (lLen64 ++ lP) = none ∧
    trRead (trEntries pvRt (lLen64 ++ lP)) 0 8 = .ok none := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩ <;>
    (simp only [lP, lQ, lLen64, lLen32, encodePtrBytes, encodePtrBytesAux,
      encodePlainLittleEndianBytes, normPtrByteOffset, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, trEntries, trEntriesAux, fragOf, mkFrag,
      Nat.reduceAdd, Nat.reducePow, Nat.reduceMod]
     lm_trread; lm_open; lm_close)

/-- **Wide `&dyn Trait` pointers (64-bit & 32-bit) against vendored `ProvenanceMap.readPtr`.** -/
theorem w_lm_wide_dyn :
    decodePtrBytesNoForge true (.dynamic "T") 8 (lP ++ lVt64) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .ptr ⟨42, 0x80⟩ 8]) ∧
    trRead (trEntries pvRt (lP ++ lVt64)) 0 8 = .ok (some (pvRt 7 7)) ∧
    trRead (trEntries pvRt (lP ++ lVt64)) 8 8 = .ok (some (pvRt 42 42)) ∧
    decodePtrBytesNoForge true (.dynamic "T") 4 (lQ ++ lVt32) =
      some (.aggregate 0 [.ptr ⟨9, 0x1000⟩ 4, .ptr ⟨43, 0x20⟩ 4]) ∧
    trRead (trEntries pvRt (lQ ++ lVt32)) 0 4 = .ok (some (pvRt 9 9)) ∧
    trRead (trEntries pvRt (lQ ++ lVt32)) 4 4 = .ok (some (pvRt 43 43)) ∧
    decodePtrBytesNoForge true (.dynamic "T") 8 (lP ++ lVt64.reverse) = none ∧
    decodePtrBytesNoForge false (.dynamic "T") 8 (lP ++ lVt64.reverse) =
      some (.aggregate 0 [.ptr ⟨7, 0x1000⟩ 8, .scalar ⟨0x8000000000000000, 8⟩]) ∧
    trRead (trEntries pvRt (lP ++ lVt64.reverse)) 8 8 = .ok none ∧
    trRead (trEntries pvCt (lP ++ lVt64.reverse)) 8 8 = .error (.readPartialPointer (Size.ofBytes 8)) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩ <;>
    (simp only [lP, lQ, lVt64, lVt32, encodePtrBytes, encodePtrBytesAux, normPtrByteOffset,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      trEntries, trEntriesAux, fragOf, mkFrag, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod]
     lm_trread; lm_open; lm_close)

/-- **Universal `Kani#5205` `Trusted` ↔ vendored Miri `bool` validity biconditional.** -/
theorem kani5205_bool_validity_iff (b : UInt8) :
    (validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨b.toNat, 1⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 b))
        (fun _ s => .ok false s) () = .ok .valid ()) ∧
    ((decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init b none]).isSome = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 b))
        (fun _ s => .ok false s) () = .ok .valid ()) := by
  rw [miri_checkPrimitive_bool_iff b]
  have hlt : b.toNat < 256 := UInt8.toNat_lt b
  by_cases hb : b.toNat ≤ 1
  · have : b = 0 ∨ b = 1 := by
      have : b.toNat = 0 ∨ b.toNat = 1 := by omega
      rcases this with h | h
      · exact Or.inl (UInt8.toNat_inj.mp h)
      · exact Or.inr (UInt8.toNat_inj.mp h)
    simp only [hb, ↓reduceIte, iff_true]
    rcases this with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · have hble : Nat.ble b.toNat 1 = false := by
      cases h : Nat.ble b.toNat 1 with
      | false => rfl
      | true => exact absurd (Nat.ble_eq.mp h) hb
    have hval : validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨b.toNat, 1⟩) = false := by
      show Bool.and true (Nat.ble b.toNat 1) = false
      rw [hble]; rfl
    have hne0 : Nat.beq b.toBitVec.toNat 0 = false := by
      cases h : Nat.beq b.toBitVec.toNat 0 with
      | false => rfl
      | true => have : b.toNat = 0 := Nat.eq_of_beq_eq_true h; omega
    have hne1 : Nat.beq b.toBitVec.toNat 1 = false := by
      cases h : Nat.beq b.toBitVec.toNat 1 with
      | false => rfl
      | true => have : b.toNat = 1 := Nat.eq_of_beq_eq_true h; omega
    have hdec : decodeTypedValueFromBytes defaultCodecFuel wLayouts wTyBool [.init b none] = none := by
      show (match Nat.beq b.toBitVec.toNat 0 with
        | true => some (Value.scalar ⟨0, 1⟩)
        | false => match Nat.beq b.toBitVec.toNat 1 with
          | true => some (Value.scalar ⟨1, 1⟩)
          | false => none) = none
      rw [hne0, hne1]
    simp [hb, hval, hdec]

/-- **Universal `Kani#5205` `Trusted` ↔ vendored Miri `char` validity biconditional.** -/
theorem kani5205_char_validity_iff (c : UInt32) :
    validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨c.toNat, 4⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 c))
        (fun _ s => .ok false s) () = .ok .valid () := by
  rw [miri_checkPrimitive_char_iff c]
  have hlt : c.toNat < 2 ^ 32 := UInt32.toNat_lt c
  show (Bool.and (Nat.beq 4 4) (isValidCharCode c.toNat) = true) ↔ _
  unfold isValidCharCode
  by_cases hc : c.toNat < 0xD800 ∨ (0xE000 ≤ c.toNat ∧ c.toNat ≤ 0x10FFFF)
  · simp only [hc, ↓reduceIte, iff_true]
    rcases hc with h1 | ⟨h2, h3⟩
    · have hblt : Nat.blt c.toNat 55296 = true := by unfold Nat.blt; rw [Nat.ble_eq]; omega
      simp [hblt]
      left
      cases h : Nat.ble 55296 c.toNat with
      | false => rfl
      | true => have := Nat.ble_eq.mp h; omega
    · have h2' : Nat.ble 57344 c.toNat = true := Nat.ble_eq.mpr h2
      have h3' : Nat.ble c.toNat 1114111 = true := Nat.ble_eq.mpr h3
      simp [h2', h3']
  · simp only [hc, ↓reduceIte]
    have h1 : Nat.blt c.toNat 55296 = false := by
      cases h : Nat.blt c.toNat 55296 with
      | false => rfl
      | true =>
        have : c.toNat < 55296 := by unfold Nat.blt at h; rw [Nat.ble_eq] at h; omega
        exact absurd (Or.inl this) hc
    have h2 : (Bool.and (Nat.ble 57344 c.toNat) (Nat.ble c.toNat 1114111)) = false := by
      cases h : Bool.and (Nat.ble 57344 c.toNat) (Nat.ble c.toNat 1114111) with
      | false => rfl
      | true =>
        simp only [Bool.and_eq_true, Nat.ble_eq] at h
        exact absurd (Or.inr h) hc
    simp [h1, h2]
    omega

def wUnalignedBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [2] }
def wMaybeUninitBoolL : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }
def wMaybeUninitCharL : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [3, 0] }
def wKaniLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [wUnitL, wU8L, wBoolL, wCharL, wU32L, wUnalignedBoolL, wMaybeUninitBoolL, wMaybeUninitCharL] }
def wTyUnalignedBool : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 5 }
def wTyMaybeUninitBool : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 6 }
def wTyMaybeUninitChar : Ty := { kind := .adt "core::mem::MaybeUninit" [.char], layoutIdx := 7 }

/-- **End-to-end `Kani#5205` MIR witness (`Trusted` `writeBytesAction` + `evalOperand` paired with
vendored `Miri.Memory.Allocation` + `Validity.checkPrimitive`).** -/
theorem w_lm_kani5205_e2e :
    let decls : List LocalDecl := [
      { mutability := .mut, ty := wTyBool, debugName := none },
      { mutability := .mut, ty := wTyUnalignedBool, debugName := none },
      { mutability := .mut, ty := wTyMaybeUninitBool, debugName := none },
      { mutability := .mut, ty := wTyMaybeUninitChar, debugName := none }
    ]
    let bs : List BorrowEntry := [
      { tag := 1, targetLocal := 0, targetProjection := [], perm := .active },
      { tag := 2, targetLocal := 1, targetProjection := [], perm := .active },
      { tag := 3, targetLocal := 2, targetProjection := [], perm := .active },
      { tag := 4, targetLocal := 3, targetProjection := [], perm := .active }
    ]
    let wb (tag : Nat) (tyArg : RigidTy) (byteVal : Nat) : WriteBytesAction :=
      writeBytesAction bs 0 { defPath := "core::ptr::write_bytes", typeArgs := [tyArg] }
        decls wKaniLayouts [] [.ptr { allocId := tag, offsetBytes := 0 } 8, .scalar ⟨byteVal, 1⟩, .scalar ⟨1, 8⟩]
    let surrVal : Value := .aggregate 0 [.unit, .unit, .aggregate 0
      (encodeRawAbstractByteVals (encodePlainLittleEndianBytes 0xD800 4))]
    (match wb 1 .bool 2, wb 2 wTyUnalignedBool.kind 2, wb 3 wTyMaybeUninitBool.kind 2 with
     | .store ⟨0, []⟩ 0 1 (.scalar ⟨2, 1⟩),
       .store ⟨1, []⟩ 1 2 unalVal,
       .store ⟨2, []⟩ 2 3 muBoolVal =>
       validateValueForTy? wKaniLayouts (some wTyMaybeUninitBool) muBoolVal = true ∧
       validateValueForTy? wKaniLayouts (some wTyMaybeUninitChar) surrVal = true ∧
       evalOperand [.init (.scalar ⟨2, 1⟩)] (.copy ⟨0, []⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .init unalVal] (.copy ⟨1, []⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]
         (.copy ⟨1, [.field 0 wTyBool]⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .uninit, .init muBoolVal]
         (.copy ⟨2, [.field 0 wTyBool]⟩) [] [] wKaniLayouts [] decls = .ub ∧
       evalOperand [.uninit, .uninit, .uninit, .init surrVal]
         (.copy ⟨3, [.field 0 wTyChar]⟩) [] [] wKaniLayouts [] decls = .ub
     | _, _, _ => False) ∧
    miriWriteThenReadScalar #[0] #[2] 1 = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 2)) ∧
    miriWriteThenReadScalar #[0, 0, 0, 0] #[0x00, 0xD8, 0x00, 0x00] 4 =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800)) :=
  ⟨by repeat first | refine ⟨?_, ?_⟩ | rfl | trivial,
   w_lm_kani5205_alloc_e2e.1,
   w_lm_kani5205_alloc_e2e.2.1⟩

/-- Non-vacuous instantiations of `encodePtrBytes_wf`, `readPtr{4,8}_allBytes_{runtime,ctfe}_corr`,
`intact_roundtrip_{4,8}`, `rawCarrier_ptr_roundtrip_{4,8}`, and `kani5205_{bool,char}_validity_iff`. -/
theorem ep2_b1_non_vacuity_instances :
    (∃ v f, lP[0]? = some (.init v (some f)) ∧ f = ⟨7, 7, 0, 0x1000, 8⟩ ∧ WF 8 f) ∧
    trRead (trEntries pvRt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok none ∧
    trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok none ∧
    trRead (trEntries pvRt (lP.take 7 ++ [.uninit])) 0 8 = .ok none ∧
    trRead (trEntries pvCt (lP.take 7 ++ [.uninit])) 0 8 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    trRead (trEntries pvRt (lQ.take 3 ++ [.init 0 none])) 0 4 = .ok none ∧
    trRead (trEntries pvCt (lQ.take 3 ++ [.init 0 none])) 0 4 = .error (.readPartialPointer (Size.ofBytes 0)) ∧
    (decodePtrBytesNoForge true (.uint .u8) 8 (encodePtrBytes 0x1000 8 7 7) =
      some (.ptr { allocId := 7, offsetBytes := 0x1000 % 256 ^ 8 } 8) ∧
     trRead (trEntries pvRt (encodePtrBytes 0x1000 8 7 7)) 0 8 = .ok (some (pvRt 7 7)) ∧
     trRead (trEntries pvCt (encodePtrBytes 0x1000 8 7 7)) 0 8 = .ok (some (pvCt 7 7))) ∧
    (decodePtrBytesNoForge false (.uint .u8) 4 (encodePtrBytes 0x1000 4 9 9) =
      some (.ptr { allocId := 9, offsetBytes := 0x1000 % 256 ^ 4 } 4) ∧
     trRead (trEntries pvRt (encodePtrBytes 0x1000 4 9 9)) 0 4 = .ok (some (pvRt 9 9)) ∧
     trRead (trEntries pvCt (encodePtrBytes 0x1000 4 9 9)) 0 4 = .ok (some (pvCt 9 9))) ∧
    (∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes 0x1000 8 7 7).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge true (.uint .u8) 8 bs = some (.ptr { allocId := 7, offsetBytes := 0x1000 % 256 ^ 8 } 8) ∧
      trRead (trEntries pvRt bs) 0 8 = .ok (some (pvRt 7 7)) ∧
      trRead (trEntries pvCt bs) 0 8 = .ok (some (pvCt 7 7))) ∧
    (∃ bs, decodeRawAbstractByteVals? ((encodePtrBytes 0x1000 4 9 9).map encodeRawAbstractByteVal) = some bs ∧
      decodePtrBytesNoForge false (.uint .u8) 4 bs = some (.ptr { allocId := 9, offsetBytes := 0x1000 % 256 ^ 4 } 4) ∧
      trRead (trEntries pvRt bs) 0 4 = .ok (some (pvRt 9 9)) ∧
      trRead (trEntries pvCt bs) 0 4 = .ok (some (pvCt 9 9))) ∧
    (validateValueForTy? wLayouts (some wTyBool) (.scalar ⟨(2 : UInt8).toNat, 1⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .boolean ⟨Size.ofBytes 1, ⟨0, 1⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt8 2))
        (fun _ s => .ok false s) () = .ok .valid ()) ∧
    (validateValueForTy? wLayouts (some wTyChar) (.scalar ⟨(0xD800 : UInt32).toNat, 4⟩) = true ↔
      Validity.checkPrimitive (Prov := Provenance) (MachineError := Unit) (HookState := Unit)
        .character ⟨Size.ofBytes 4, ⟨0, 0x10FFFF⟩⟩ (Scalar.fromScalarInt (ScalarInt.ofUInt32 0xD800))
        (fun _ s => .ok false s) () = .ok .valid ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    intact_roundtrip_8 true 0x1000 7 7 (by decide) (by decide),
    intact_roundtrip_4 false 0x1000 9 9 (by decide) (by decide),
    rawCarrier_ptr_roundtrip_8 true 0x1000 7 7 (by decide) (by decide),
    rawCarrier_ptr_roundtrip_4 false 0x1000 9 9 (by decide) (by decide),
    (kani5205_bool_validity_iff 2).1,
    kani5205_char_validity_iff 0xD800⟩
  · obtain ⟨v, f, hv, hf, hwf⟩ := encodePtrBytes_wf 0x1000 8 7 7 0 _ rfl
    exact ⟨v, f, hv ▸ rfl, hf, hwf⟩
  · exact (readPtr8_allBytes_runtime_corr pvRt rfl (encodePlainLittleEndianBytes 0x1000 8) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)).trans rfl
  · exact (readPtr8_allBytes_ctfe_corr pvCt rfl (encodePlainLittleEndianBytes 0x1000 8) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)).trans rfl
  · exact (readPtr8_allBytes_runtime_corr pvRt rfl (lP.take 7 ++ [.uninit]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; decide
        | 7, h | _+8, h => cases h)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 7 ∧ fi.tag = 7 := by
            match i, hi with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          have hj' : fj.allocId = 7 ∧ fj.tag = 7 := by
            match j, hj with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl
  · exact (readPtr8_allBytes_ctfe_corr pvCt rfl (lP.take 7 ++ [.uninit]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 7, h | _+8, h => cases h)
      (by intro i v f hi hw; cases hw)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 7 ∧ fi.tag = 7 := by
            match i, hi with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          have hj' : fj.allocId = 7 ∧ fj.tag = 7 := by
            match j, hj with
            | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 7, h | _+8, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl
  · exact (readPtr4_allBytes_runtime_corr pvRt rfl (lQ.take 3 ++ [.init 0 none]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 3, h | _+4, h => cases h)
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; decide
        | 3, h | _+4, h => cases h)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 9 ∧ fi.tag = 9 := by
            match i, hi with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          have hj' : fj.allocId = 9 ∧ fj.tag = 9 := by
            match j, hj with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl
  · exact (readPtr4_allBytes_ctfe_corr pvCt rfl (lQ.take 3 ++ [.init 0 none]) rfl
      (by intro i v f hi; match i, hi with
        | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, by decide, by decide⟩
        | 3, h | _+4, h => cases h)
      (by intro i v f hi hw; cases hw)
      (by intro i j vi vj fi fj hi hj _
          have hi' : fi.allocId = 9 ∧ fi.tag = 9 := by
            match i, hi with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          have hj' : fj.allocId = 9 ∧ fj.tag = 9 := by
            match j, hj with
            | 0, h | 1, h | 2, h => injection h with h; injection h with _ h; injection h with h; subst h; exact ⟨rfl, rfl⟩
            | 3, h | _+4, h => cases h
          exact ⟨hi'.1.trans hj'.1.symm, hi'.2.trans hj'.2.symm⟩)).trans rfl

end WideAndKani

/-- Non-vacuous instantiations of `readPtr8_allBytes_ctfe_iff` and `readPtr4_allBytes_ctfe_iff`
on the plain (provenance-free) images of `0x1000` with CTFE provenance. -/
theorem readPtr_allBytes_ctfe_iff_instance :
    (((∃ f, abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 8) = some f) ↔
      ∃ p, trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 8) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 8) = true) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 8) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 8) = false) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 8)) 0 8 = .ok none)) ∧
    (((∃ f, abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 4) = some f) ↔
      ∃ p, trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 4)) 0 4 = .ok (some p)) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 4) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 4) = true) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 4)) 0 4 = .error (.readPartialPointer (Size.ofBytes 0))) ∧
    ((abstractBytesCoherentPtrProv? (encodePlainLittleEndianBytes 0x1000 4) = none ∧ abstractBytesHaveProv (encodePlainLittleEndianBytes 0x1000 4) = false) ↔
      trRead (trEntries pvCt (encodePlainLittleEndianBytes 0x1000 4)) 0 4 = .ok none)) :=
  ⟨readPtr8_allBytes_ctfe_iff pvCt rfl (encodePlainLittleEndianBytes 0x1000 8) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | _+8, h => cases h),
   readPtr4_allBytes_ctfe_iff pvCt rfl (encodePlainLittleEndianBytes 0x1000 4) rfl
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | _+4, h => cases h)
      (by intro i v f hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | _+4, h => cases h)
      (by intro i _ _ _ _ _ hi; match i, hi with | 0, h | 1, h | 2, h | 3, h | _+4, h => cases h)⟩

end V08

/-! ## Lockstep parity `V2026_06_01 ↔ V2026_08_01` -/

section Parity

/-- The identity translation of fragments from `V2026_06_01` to `V2026_08_01`. -/
def frag68 (f : Trusted.Rustc.V2026_06_01.MirSemantics.PtrByteFrag) :
    Trusted.Rustc.V2026_08_01.MirSemantics.PtrByteFrag :=
  ⟨f.allocId, f.tag, f.byteIdx, f.origOffset, f.ptrBytes⟩

/-- The identity translation of abstract bytes from `V2026_06_01` to `V2026_08_01`. -/
def byte68 : Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte →
    Trusted.Rustc.V2026_08_01.MirSemantics.AbstractByte
  | .uninit => .uninit
  | .init b none => .init b none
  | .init b (some f) => .init b (some (frag68 f))

theorem coherentAux_parity (a t o pb : Nat) :
    ∀ (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) (idx : Nat),
      Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProvAux a t o pb idx
          (bs.map byte68) =
        Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProvAux a t o pb idx bs
  | [], _ => rfl
  | .uninit :: _, _ => rfl
  | .init _ none :: _, _ => rfl
  | .init _ (some _) :: rest, idx =>
      congrArg (Bool.and _) (coherentAux_parity a t o pb rest (idx + 1))

/-- **Coherence parity.** -/
theorem coherent_parity (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) :
    Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv? (bs.map byte68) =
      (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs).map frag68 := by
  cases bs with
  | nil => rfl
  | cons b rest =>
      cases b with
      | uninit => rfl
      | init v pr =>
          cases pr with
          | none => rfl
          | some f =>
              show (match Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
                    (Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProvAux
                      f.allocId f.tag f.origOffset f.ptrBytes 1 (rest.map byte68))) with
                | true => some (frag68 f)
                | false => none) =
                (match Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
                    (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProvAux
                      f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) with
                | true => some f
                | false => none).map frag68
              rw [coherentAux_parity]
              cases Bool.and (Nat.blt 0 f.ptrBytes) (Bool.and (Nat.beq f.byteIdx 0)
                (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProvAux
                  f.allocId f.tag f.origOffset f.ptrBytes 1 rest)) <;> rfl

theorem trEntriesAux_parity {Prov : Type} (pv : Nat → Nat → Prov) :
    ∀ (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte) (i : Nat),
      V08.trEntriesAux pv i (bs.map byte68) = V06.trEntriesAux pv i bs
  | [], _ => rfl
  | .uninit :: rest, i => trEntriesAux_parity pv rest (i + 1)
  | .init _ none :: rest, i => trEntriesAux_parity pv rest (i + 1)
  | .init _ (some _) :: rest, i => congrArg (List.cons _) (trEntriesAux_parity pv rest (i + 1))

/-- **`V2026_06_01 ↔ V2026_08_01` lockstep parity.** On translated streams both dialects produce
the same vendored Miri fragment state — hence the same vendored `readPtr` result for every
provenance embedding, offset, and size — and the same coherence verdict. -/
theorem lm_lockstep_parity {Prov : Type} [DecidableEq Prov] [PointerProvenance Prov]
    (pv : Nat → Nat → Prov) (bs : List Trusted.Rustc.V2026_06_01.MirSemantics.AbstractByte)
    (off n : UInt64) :
    V08.trEntries pv (bs.map byte68) = V06.trEntries pv bs ∧
    trRead (V08.trEntries pv (bs.map byte68)) off n = trRead (V06.trEntries pv bs) off n ∧
    (Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv? (bs.map byte68)).isSome =
      (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs).isSome := by
  have h : V08.trEntries pv (bs.map byte68) = V06.trEntries pv bs :=
    congrArg List.toArray (trEntriesAux_parity pv bs 0)
  refine ⟨h, by rw [h], ?_⟩
  rw [coherent_parity]
  cases Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? bs <;> rfl

theorem lm_lockstep_parity_instance :
    V06.lP.map byte68 = V08.lP ∧
    (V08.trEntries pvRt (V06.lP.map byte68) = V06.trEntries pvRt V06.lP ∧
      trRead (V08.trEntries pvRt (V06.lP.map byte68)) 0 8 = trRead (V06.trEntries pvRt V06.lP) 0 8 ∧
      (Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv?
          (V06.lP.map byte68)).isSome =
        (Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv? V06.lP).isSome) :=
  ⟨rfl, lm_lockstep_parity pvRt V06.lP 0 8⟩

end Parity

/-! ## Axiom, import-isolation, and non-triviality audit -/

section AxiomAudit
open Lean Elab Command

/-- Verify that this module imports no `MiniRustSpec.*` or `Anneal.*` module and does import the
vendored `Miri.Memory.ProvenanceMap`; that every declaration of this module depends only on the
standard axioms with zero `sorryAx` / `Lean.ofReduceBool`; that no public theorem is trivial; and
that the headline theorems exist for both dialects. -/
elab "#assert_ptr_byte_coherence_lm_audit" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  unless env.header.moduleNames.contains `Miri.Memory.ProvenanceMap do
    throwError "vendored Miri.Memory.ProvenanceMap is not imported"
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
      else false
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    if let .thmInfo v := ci then
      let u := (Lean.privateToUserName? c).getD c
      if !u.isInternal then
        if isTrivialProp v.type then
          throwError "{c} is a trivial theorem"
        theorems := theorems + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool then throwError "{c} depends on Lean.ofReduceBool"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "LeanMiriSpec.PtrByteCoherenceLM: 0 declarations found"
  let perDialect : List String := [
    "normOffset_image_inj", "encodePtrBytes_wf", "coh_iff8", "coh_iff4", "readPtr8_runtime_corr",
    "readPtr8_ctfe_corr", "readPtr4_runtime_corr", "readPtr4_ctfe_corr",
    "readPtr8_allBytes_runtime_corr", "readPtr8_allBytes_ctfe_corr",
    "readPtr4_allBytes_runtime_corr", "readPtr4_allBytes_ctfe_corr",
    "readPtr8_allBytes_runtime_iff", "readPtr4_allBytes_runtime_iff",
    "readPtr8_allBytes_ctfe_iff", "readPtr4_allBytes_ctfe_iff", "readPtr_allBytes_ctfe_iff_instance",
    "intact_roundtrip_8", "intact_roundtrip_4",
    "rawCarrier_ptr_roundtrip_8", "rawCarrier_ptr_roundtrip_4",
    "w_lm_wide_slice_and_str", "w_lm_wide_dyn",
    "kani5205_bool_validity_iff", "kani5205_char_validity_iff", "w_lm_kani5205_e2e",
    "w_lm_intact", "w_lm_zero_reversal", "w_lm_reversal", "w_lm_swap01", "w_lm_dup_head",
    "w_lm_rotate", "w_lm_splice_p_p4", "w_lm_splice_p_p256", "w_lm_mixed_alloc", "w_lm_intact32",
    "w_lm_reversal32", "w_lm_splice32_q_q256", "w_lm_missing_and_uninit", "w_lm_kani5205_trusted",
    "normOffset_image_inj_instance", "ep2_b1_non_vacuity_instances" ]
  let shared : List Lean.Name := [
    ``ptrImage_inj, ``readPtr8_runtime, ``readPtr8_ctfe, ``readPtr4_runtime, ``readPtr4_ctfe,
    ``mem_qsort, ``pvRt_inj, ``pvRt_ne_wildcard,
    ``clear_partial_mid_strips_8, ``clear_partial_mid_strips_4, ``clear_partial_7bytes_strips_8,
    ``prepareCopy_applyCopy_intact_8, ``prepareCopy_applyCopy_splice_p_p256,
    ``trRead_empty, ``readPtr_missing_byte_strips, ``readPtr4_missing_byte_strips, ``readPtr8_missing_byte_strips,
    ``w_lm_ctfe_tag_blind, ``miri_checkPrimitive_bool_iff, ``miri_checkPrimitive_char_iff,
    ``w_lm_kani5205_alloc_e2e, ``clear_and_prepareCopy_instance,
    ``w_lm_missing_miri_rt, ``w_lm_missing_miri_ct, ``w_lm_misaligned, ``w_lm_wildcard,
    ``w_lm_kani5205_miri, ``pm_w1_whole_pointer_path_only, ``coherent_parity,
    ``lm_lockstep_parity, ``lm_lockstep_parity_instance ]
  let mut headline : Nat := 0
  for dialect in ["V06", "V08"] do
    for name in perDialect do
      let c := (`LeanMiriSpec.PtrByteCoherenceLM).str dialect |>.str name
      match env.find? c with
      | some (.thmInfo _) => headline := headline + 1
      | _ => throwError "headline theorem {c} is missing"
  for c in shared do
    match env.find? c with
    | some (.thmInfo _) => headline := headline + 1
    | _ => throwError "headline theorem {c} is missing"
  logInfo m!"[PTR-BYTE-COHERENCE-LM-AUDIT] declarations={checked} theorems={theorems} headline={headline} ok=true"

#assert_ptr_byte_coherence_lm_audit

end AxiomAudit

end LeanMiriSpec.PtrByteCoherenceLM
