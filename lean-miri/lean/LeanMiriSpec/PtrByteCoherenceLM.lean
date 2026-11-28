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
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_08_01.MirSemantics.Places

/-!
# Episode 2 Dual-Authority Correspondence (`LeanMiriSpec` Authority):
# pointer-byte fragment coherence (`UCG#558` / `rust#148259`) against unmodified vendored
# `Miri.Memory.ProvenanceMap`, and read-time validity (`Kani#5205`)

Correspondence between the pointer-byte codec of `Trusted.Rustc.V2026_{06,08}_01.MirSemantics`
(`encodePtrBytes`, `abstractBytesCoherentPtrProv?`, `decodePtrBytesNoForge`,
`decodeTypedValueFromBytes`, `validateValueForTy?`) and the **unmodified vendored**
`Miri.Memory.ProvenanceMap` (`PointerFrag`, `ProvenanceMap.fromParts`,
`ProvenanceMap.fromPresortedPtrs`, `ProvenanceMap.readPtr`, `ProvenanceMap.getByte`, and the
`private` `inspectFragments`, reached by name resolution only through `delta_miri_private`),
`Miri.Memory.{Provenance, AllocId, CtfeProvenance}` and `Miri.Memory.Validity.checkPrimitive`.
No vendored definition is copied or restated.

## The translation

`mkFrag pv f` maps a `Trusted` `PtrByteFrag { allocId, tag, byteIdx, origOffset, ptrBytes }` to
the vendored `PointerFrag { idx := UInt8.ofNat byteIdx, prov := pv allocId tag,
bytes := ptrImage ptrBytes origOffset }`, where `ptrImage` is the zero-padded little-endian
8-byte image that vendored `ptrFragments` builds. `trEntries pv bytes` places one such fragment at
the offset of every fragment-carrying byte, giving the state
`ProvenanceMap.fromParts #[] (some (trEntries pv bytes))`. The embeddings are `pvRt` (Miri runtime
`Provenance.concrete`, `offsetIsAddr = true`, wildcard available) and `pvCt` (CTFE `AllocId`,
`offsetIsAddr = false`, no wildcard).

## Theorem surface (`V06` and `V08` generated identically)

1. **Byte-vector injectivity** (`ptrImage_inj`, `normOffset_image_inj`): for every width
   `0 < ptrBytes ≤ 8` (in particular `4` and `8`), two normalized offsets have equal vendored
   `PointerFrag.bytes` iff they are equal.
2. **Vendored `readPtr` on symbolic fragments** (`readPtr8_runtime`, `readPtr8_ctfe`,
   `readPtr4_runtime`, `readPtr4_ctfe`): kernel-checked closed forms of the unmodified vendored
   `readPtr` / `inspectFragments` on `n` arbitrary non-wildcard fragments.
3. **Universal `Trusted` ↔ vendored `readPtr` correspondence** (`coh_iff8`, `coh_iff4`,
   `readPtr8_runtime_corr`, `readPtr8_ctfe_corr`, `readPtr4_runtime_corr`,
   `readPtr4_ctfe_corr`): for every stream of `8` (resp. `4`) well-formed fragment bytes, the
   vendored read of the translated state is `.ok (some (pv allocId tag))` exactly when
   `abstractBytesCoherentPtrProv? bytes = some _`, and `.ok none` (runtime) /
   `.error (.readPartialPointer 0)` (CTFE) exactly when it is `none`. Every `UCG#558` W1 / W2
   attack on a pointer image (reversal, swap, duplication, permutation, offset splice, mixed
   provenance) is such a stream.
4. **Three-way witnesses** (`w_lm_*`), each instantiating the universal theorems for both Miri
   provenance kinds: intact round trip, all-zero reversal, reversal, swap, duplication, rotation,
   `p` / `p + 4` and `p` / `p + 256` splices, mixed allocation, 32-bit intact / reversal /
   splice, missing provenance and uninitialized bytes, misaligned cross-relocation reads and
   32-bit non-bleed (`w_lm_misaligned`), wildcard behaviour (`w_lm_wildcard`), and `Kani#5205`
   (`w_lm_kani5205_trusted`, `w_lm_kani5205_miri`).
5. **Lockstep parity** (`lm_lockstep_parity`) and the audit `#assert_ptr_byte_coherence_lm_audit`.

## Scoped divergences and scope

* `DIV-LM-WILDCARD` (`w_lm_wildcard`): vendored `inspectFragments` skips wildcard fragments, so a
  wildcard byte next to seven coherent bytes still reads the concrete provenance. `Trusted` has no
  wildcard (exposed) provenance and the translation never produces one; a wildcard does not rescue
  an offset splice in either authority.
* `DIV-LM-CROSS-WIDTH`: vendored `PointerFrag` carries no pointer width, so a 4-byte read of the
  first half of an 8-byte pointer's fragments is accepted by `readPtr` while `Trusted` requires
  `frag.ptrBytes = ptrBytes`. A single Miri allocation never mixes pointer widths (`pointerSize`
  is the target's); the correspondence is stated for well-formed fragments (`WF`) of the target
  width, where the two agree exactly.
* The universal correspondence is stated for streams in which every byte carries a fragment (the
  shape of every attack above); streams with plain or uninitialized bytes are covered by the
  `Trusted` stripping laws and by the vendored witnesses `w_lm_missing_and_uninit`. Vendored
  `ProvenanceMap.clear` / `prepareCopy` / `applyCopy` keep their maps sorted with `Array.qsort`
  (well-founded recursion), which the kernel does not evaluate; partial overwrite through `clear`
  is therefore characterized on the `Trusted` side and by `w_lm_misaligned` (whole-pointer
  entries straddling a read), not by a post-`clear` `readPtr` evaluation.

## Correspondence-gap postmortem (`mir-correspondence-postmortem.md`)

Why the pre-Episode-1 `LeanMiriSpec` (and `MiniRustSpec`) suites did not catch the soundness bugs
closed in Episode 1:

* **`UCG#558` W1 (byte permutation) and W2 (offset splices).** The `LeanMiriSpec` memory
  correspondence (`PtrLM3_1`, `CopyLM4_2`, `UnionLM2_4`, `MemoryLemmas`) related `Trusted`
  pointers only to whole-pointer `ProvenanceMap.ptrs` entries of aligned, size-preserving copies;
  every proof went through `read_exact_pointer` / `clear_new` / `readPtr_new`, never through the
  fragment path (`byteFragments`, `inspectFragments`). A permuted or spliced byte image never
  arises from aligned whole-pointer copies, so the gap between `Trusted`'s old per-byte
  `(allocId, tag)` merge and Miri's fragment rule was outside the proven scope
  (`pm_w1_whole_pointer_path_only` exhibits the two paths). Vendored MiniRust additionally lacks
  the originating offset in `ProvenanceFrag`, so it accepts W2 splices (see
  `MiniRustSpec.PtrByteCoherenceMR`).
* **W3–W5** (32-bit `layoutPointerBytes = 4` vs. an 8-byte constant, `body.globals` relocations,
  wide-pointer bytewise copies, multi-variant enums, union `.ref` / `.fnPtr` punning, cross-frame
  foreign copies, `evalCopyMemory`): the suites fixed a 64-bit target and never instantiated the
  pointer width, never related global relocations or wide-pointer halves at byte level, and their
  union / copy theorems carried only integer payloads.
* **`Kani#5205`**: validity was related only at typed writes; no theorem wrote an invalid bit
  pattern through an untyped place (`[u8; 1]`, `MaybeUninit<bool>`, `Unaligned<bool>`) and then
  read it at the typed `bool` / `char`, which is where `Trusted` must fault.

What now prevents regression: `readPtr8_runtime_corr` / `readPtr8_ctfe_corr` and their 4-byte
twins fix `Trusted`'s coherence verdict to the unmodified vendored fragment rule for every
fragment stream of both widths; `normOffset_image_inj` pins the `origOffset` normalization to
the vendored byte image; the `w_lm_*` witnesses pin every named attack in both dialects;
`w_lm_kani5205_trusted` / `w_lm_kani5205_miri` pin typed-read rejection; `lm_lockstep_parity`
pins `V2026_06_01 ↔ V2026_08_01`. Remaining scoped boundaries: `&dyn` vtable allocation identity
(no vtable table in the `Trusted` IR / `Memory`), the `VariantsShape.multiple` per-variant
`TypeLayout` schema, the `Ptr2IntTransmutePolicy.strictUcg630Ub` write-time pointer-to-integer
pin, and the `Array.qsort`-based `clear` / `prepareCopy` / `applyCopy` evaluation noted above.

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
    "readPtr8_ctfe_corr", "readPtr4_runtime_corr", "readPtr4_ctfe_corr", "w_lm_intact",
    "w_lm_zero_reversal", "w_lm_reversal", "w_lm_swap01", "w_lm_dup_head", "w_lm_rotate",
    "w_lm_splice_p_p4", "w_lm_splice_p_p256", "w_lm_mixed_alloc", "w_lm_intact32",
    "w_lm_reversal32", "w_lm_splice32_q_q256", "w_lm_missing_and_uninit", "w_lm_kani5205_trusted",
    "normOffset_image_inj_instance" ]
  let shared : List Lean.Name := [
    ``ptrImage_inj, ``readPtr8_runtime, ``readPtr8_ctfe, ``readPtr4_runtime, ``readPtr4_ctfe,
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
