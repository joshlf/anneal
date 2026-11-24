/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.AtomicIntrinsicsMR

/-!
# Episode 2 Dual-Authority Atomic Intrinsics Spec (`Anneal.Mir.AtomicIntrinsicsDualSpec`)

Initial Interface Freeze + MiniRust canonical 28-case (`0..27`) evaluation and
constructive codec/contract layer for Rust atomic intrinsics across:
- **Authority 1 (MiniRust `d821c6e3`)**: direct execution via
  `MiniRustSpec.Interp.evalIntrinsic` on `Mach` (`BasicMemory<x86_64>`) and
  `MiniRustSpec.Interp.evalIntrinsicM` on `MachTB` (`TreeBorrowsMemory<x86_64>`),
  reusing the builders of `MiniRustSpec.AtomicIntrinsicsMR`.
- **Authority 2 (LeanMiri)**: parameterized over `AtomicLmAuthority`, matching
  the exact 28-case (`0..27`) index table of
  `LeanMiriSpec.AtomicIntrinsicsLM.lmAtomicObserve` (closed across roots in
  Part 2 via `tests/mir/AtomicIntrinsicsDualSpecTests.lean`).

Explicit cross-authority boundary classification:
1. **Exact Agreement Zone (24/28 cases: `0..14`, `17..20`, `23..27`)**:
   `u8`/`u16`/`u32`/`u64` atomic load & store, CAS equal/unequal, in-range
   `fetch_add`/`sub`/`and`/`or`/`xor`, misaligned/oversized-`u128`/OOB UB,
   read-only `Relaxed` load, and the full 5-case Tree Borrows `Frozen`
   mode-sensitivity block (`23..27`, where `23, 24` succeed in both modes and
   `25, 26, 27` flip from success in `basic` to UB in `treeBorrows`).
2. **Documented Wrapping-Overflow Divergence (cases `15..16`)**:
   Miri/Rust wraps `u32::MAX + 1 -> 0` and `0u32 - 1 -> u32::MAX`; upstream
   MiniRust `d821c6e3` omits `bring_in_bounds` in `AtomicFetchAndOp` and emits
   `Stop.specPanic`.
3. **Documented Allocation-Mutability Divergence (cases `21..22`)**:
   Miri's `atomic_access_check` rejects writes and even *failing*
   compare-exchange on `Mutability.Not` allocations (`ReadOnlyAtomicViolation.storeOrRmw`);
   MiniRust allocations carry no `Mutability` field and model read-only via Tree
   Borrows `Frozen` (where failing CAS is read-only and succeeds).
   Cell `(treeBorrows, 21)` still agrees (`.ub`/`.ub`): see `contract_divergence_set_exact`.
4. **Coincidental Agreement on Case `18` (`u128`)**: MiniRust's UB is its size rule, LeanMiri's
   only the out-of-bounds read (`eval_u128_in_bounds_mutable_load_not_ub` in `AtomicIntrinsicsLM`).

Strict import isolation: imports ONLY `MiniRustSpec.AtomicIntrinsicsMR`
(ZERO `Trusted.*`, `Miri.*`, or `LeanMiriSpec.*` imports; verified by the
trailing `run_cmd` audit, which also enforces ZERO `Classical.choice` on
`atomicOutcomeCodec` and its constructive codec laws).
-/

namespace Anneal.Mir.AtomicIntrinsicsDualSpec

set_option Elab.async false

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.AtomicIntrinsicsMR

/-! ## §1. Frozen Interface Types -/

/-- Rust / MIR / MiniRust atomic intrinsic operation kinds. -/
inductive AtomicOpKind : Type where
  | load
  | store
  | cxchg
  | cxchgWeak
  | xadd
  | xsub
  | bitAnd
  | bitOr
  | bitXor
  | nand
  | min
  | umin
  | max
  | umax
  | xchg
  | fence
  | singleThreadFence
  deriving DecidableEq, Repr

/-- Atomic scalar integer widths (in bytes on 64-bit `x86_64`). -/
inductive AtomicScalarWidth : Type where
  | w8
  | w16
  | w32
  | w64
  | w128
  deriving DecidableEq, Repr

def AtomicScalarWidth.bytes : AtomicScalarWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8
  | .w128 => 16

def AtomicScalarWidth.toIntType : AtomicScalarWidth → IntType
  | .w8 => itU8
  | .w16 => itU16
  | .w32 => itU32
  | .w64 => itU64
  | .w128 => itU128

/-- Shared dual-authority memory/aliasing mode. -/
inductive AtomicMemoryMode : Type where
  /-- MiniRust `BasicMemory<x86_64>` / LeanMiri `treeBorrows = false`. -/
  | basic
  /-- MiniRust `TreeBorrowsMemory<x86_64>` / LeanMiri `treeBorrows = true`. -/
  | treeBorrows
  deriving DecidableEq, Repr

def AtomicMemoryMode.toLmTreeBorrows : AtomicMemoryMode → Bool
  | .basic => false
  | .treeBorrows => true

def AtomicMemoryMode.ofLmTreeBorrows : Bool → AtomicMemoryMode
  | false => .basic
  | true => .treeBorrows

theorem AtomicMemoryMode.of_toLmTreeBorrows (m : AtomicMemoryMode) :
    AtomicMemoryMode.ofLmTreeBorrows m.toLmTreeBorrows = m := by
  cases m <;> rfl

theorem AtomicMemoryMode.to_ofLmTreeBorrows (b : Bool) :
    (AtomicMemoryMode.ofLmTreeBorrows b).toLmTreeBorrows = b := by
  cases b <;> rfl

/-- All modes enumerated for finite-corpus verification. -/
def allAtomicMemoryModes : List AtomicMemoryMode := [.basic, .treeBorrows]

theorem allAtomicMemoryModes_complete (m : AtomicMemoryMode) : m ∈ allAtomicMemoryModes := by
  cases m <;> simp [allAtomicMemoryModes]

/-- Shared authority-independent outcome domain for one atomic intrinsic access. -/
inductive AtomicAccessOutcome : Type where
  | okStore (postBits : Nat)
  | okScalar (retBits : Nat) (postBits : Nat)
  | okCas (retBits : Nat) (succeeded : Bool) (postBits : Nat)
  | ub
  | specPanic
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-! ## §2. Constructive `AtomicCodecLaws` (`[propext, Quot.sound]`, Zero `Classical.choice`) -/

/-- Constructive round-trip and canonical-representation codec contract. -/
structure AtomicCodecLaws (A B : Type) : Type where
  encode : A → B
  decode : B → Option A
  ValidRep : B → Prop
  decode_encode : ∀ a, decode (encode a) = some a
  encode_valid : ∀ a, ValidRep (encode a)
  encode_decode_of_valid : ∀ b a, ValidRep b → decode b = some a → encode a = b

/-- Every valid wire representation decodes to some domain value. -/
def AtomicCodecLaws.TightValidRep {A B : Type} (c : AtomicCodecLaws A B) : Prop :=
  ∀ b, c.ValidRep b → ∃ a, c.decode b = some a

/-- Wire representation `(tag, retBits, succeeded, postBits)` for
`AtomicAccessOutcome`. -/
abbrev AtomicOutcomeRep : Type := Nat × Nat × Bool × Nat

def atomicOutcomeEncode : AtomicAccessOutcome → AtomicOutcomeRep
  | .okStore post => (0, 0, false, post)
  | .okScalar ret post => (1, ret, false, post)
  | .okCas ret succ post => (2, ret, succ, post)
  | .ub => (3, 0, false, 0)
  | .specPanic => (4, 0, false, 0)
  | .invalidOrUnsupported => (5, 0, false, 0)

def atomicOutcomeDecode : AtomicOutcomeRep → Option AtomicAccessOutcome
  | (0, 0, false, post) => some (.okStore post)
  | (1, ret, false, post) => some (.okScalar ret post)
  | (2, ret, succ, post) => some (.okCas ret succ post)
  | (3, 0, false, 0) => some .ub
  | (4, 0, false, 0) => some .specPanic
  | (5, 0, false, 0) => some .invalidOrUnsupported
  | _ => none

def atomicOutcomeValidRep : AtomicOutcomeRep → Prop
  | (0, 0, false, _) => True
  | (1, _, false, _) => True
  | (2, _, _, _) => True
  | (3, 0, false, 0) => True
  | (4, 0, false, 0) => True
  | (5, 0, false, 0) => True
  | _ => False

/-- Constructive codec instance for `AtomicAccessOutcome` (zero `Classical.choice`). -/
def atomicOutcomeCodec : AtomicCodecLaws AtomicAccessOutcome AtomicOutcomeRep where
  encode := atomicOutcomeEncode
  decode := atomicOutcomeDecode
  ValidRep := atomicOutcomeValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> exact True.intro
  encode_decode_of_valid := fun b a hv hd => by
    rcases b with ⟨t, ret, flag, post⟩
    match t with
    | 0 =>
      match ret, flag with
      | 0, false => cases hd; rfl
      | 0, true => exact False.elim hv
      | _ + 1, _ => exact False.elim hv
    | 1 =>
      match flag with
      | false => cases hd; rfl
      | true => exact False.elim hv
    | 2 =>
      cases hd; rfl
    | 3 =>
      match ret, flag, post with
      | 0, false, 0 => cases hd; rfl
      | 0, false, _ + 1 => exact False.elim hv
      | 0, true, _ => exact False.elim hv
      | _ + 1, _, _ => exact False.elim hv
    | 4 =>
      match ret, flag, post with
      | 0, false, 0 => cases hd; rfl
      | 0, false, _ + 1 => exact False.elim hv
      | 0, true, _ => exact False.elim hv
      | _ + 1, _, _ => exact False.elim hv
    | 5 =>
      match ret, flag, post with
      | 0, false, 0 => cases hd; rfl
      | 0, false, _ + 1 => exact False.elim hv
      | 0, true, _ => exact False.elim hv
      | _ + 1, _, _ => exact False.elim hv
    | _ + 6 => exact False.elim hv

/-- Tightness of `atomicOutcomeValidRep` (zero `Classical.choice`). -/
theorem atomicOutcomeCodec_tight : atomicOutcomeCodec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, ret, flag, post⟩
  match t with
  | 0 =>
    match ret, flag with
    | 0, false => exact ⟨.okStore post, rfl⟩
    | 0, true => exact False.elim hv
    | _ + 1, _ => exact False.elim hv
  | 1 =>
    match flag with
    | false => exact ⟨.okScalar ret post, rfl⟩
    | true => exact False.elim hv
  | 2 =>
    exact ⟨.okCas ret flag post, rfl⟩
  | 3 =>
    match ret, flag, post with
    | 0, false, 0 => exact ⟨.ub, rfl⟩
    | 0, false, _ + 1 => exact False.elim hv
    | 0, true, _ => exact False.elim hv
    | _ + 1, _, _ => exact False.elim hv
  | 4 =>
    match ret, flag, post with
    | 0, false, 0 => exact ⟨.specPanic, rfl⟩
    | 0, false, _ + 1 => exact False.elim hv
    | 0, true, _ => exact False.elim hv
    | _ + 1, _, _ => exact False.elim hv
  | 5 =>
    match ret, flag, post with
    | 0, false, 0 => exact ⟨.invalidOrUnsupported, rfl⟩
    | 0, false, _ + 1 => exact False.elim hv
    | 0, true, _ => exact False.elim hv
    | _ + 1, _, _ => exact False.elim hv
  | _ + 6 => exact False.elim hv

/-- Constructive injectivity of `atomicOutcomeCodec.encode`. -/
theorem atomicOutcomeCodec_encode_injective {a₁ a₂ : AtomicAccessOutcome}
    (h : atomicOutcomeCodec.encode a₁ = atomicOutcomeCodec.encode a₂) : a₁ = a₂ := by
  have h1 := atomicOutcomeCodec.decode_encode a₁
  have h2 := atomicOutcomeCodec.decode_encode a₂
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- Constructive injectivity of `atomicOutcomeCodec.decode` on valid representations. -/
theorem atomicOutcomeCodec_decode_injective_on_valid {b₁ b₂ : AtomicOutcomeRep}
    {a : AtomicAccessOutcome}
    (hv₁ : atomicOutcomeCodec.ValidRep b₁) (hv₂ : atomicOutcomeCodec.ValidRep b₂)
    (hd₁ : atomicOutcomeCodec.decode b₁ = some a)
    (hd₂ : atomicOutcomeCodec.decode b₂ = some a) : b₁ = b₂ := by
  have h1 := atomicOutcomeCodec.encode_decode_of_valid b₁ a hv₁ hd₁
  have h2 := atomicOutcomeCodec.encode_decode_of_valid b₂ a hv₂ hd₂
  exact h1.symm.trans h2

/-! ## §3. Canonical 28-Case Table Metadata (`0..27`) -/

/-- Number of canonical cross-authority atomic intrinsic test cases. -/
def canonicalCaseCount : Nat := 28

/-- Cross-authority semantic relationship for each canonical case index. -/
inductive AtomicComparisonClass : Type where
  /-- Both MiniRust (`d821c6e3`) and LeanMiri agree identically in both modes. -/
  | exactAgreement
  /-- Miri/Rust wraps on `fetch_add`/`fetch_sub` overflow; MiniRust `d821c6e3`
  omits `bring_in_bounds` and emits `Stop.specPanic`. -/
  | wrappingOverflowDivergence
  /-- Miri enforces allocation-level `Mutability.Not` (`storeOrRmw` UB even on
  failing CAS); MiniRust allocations carry no `Mutability` flag. -/
  | readOnlyAllocDivergence
  deriving DecidableEq, Repr

/-- Metadata for one canonical case index (`0..27`), aligned 1-to-1 with
`LeanMiriSpec.AtomicIntrinsicsLM.lmAtomicObserve`. -/
structure AtomicCaseMeta where
  caseIdx : Nat
  name : String
  op : AtomicOpKind
  width : AtomicScalarWidth
  comparisonClass : AtomicComparisonClass
  modeSensitive : Bool := false
  deriving DecidableEq, Repr

def canonicalCaseMeta : Nat → AtomicCaseMeta
  | 0 => ⟨0, "load_u8", .load, .w8, .exactAgreement, false⟩
  | 1 => ⟨1, "store_u8", .store, .w8, .exactAgreement, false⟩
  | 2 => ⟨2, "load_u16", .load, .w16, .exactAgreement, false⟩
  | 3 => ⟨3, "store_u16", .store, .w16, .exactAgreement, false⟩
  | 4 => ⟨4, "load_u32", .load, .w32, .exactAgreement, false⟩
  | 5 => ⟨5, "store_u32", .store, .w32, .exactAgreement, false⟩
  | 6 => ⟨6, "load_u64", .load, .w64, .exactAgreement, false⟩
  | 7 => ⟨7, "store_u64", .store, .w64, .exactAgreement, false⟩
  | 8 => ⟨8, "cas_eq_u32", .cxchg, .w32, .exactAgreement, false⟩
  | 9 => ⟨9, "cas_ne_u32", .cxchg, .w32, .exactAgreement, false⟩
  | 10 => ⟨10, "fetch_add_u32", .xadd, .w32, .exactAgreement, false⟩
  | 11 => ⟨11, "fetch_sub_u32", .xsub, .w32, .exactAgreement, false⟩
  | 12 => ⟨12, "fetch_and_u32", .bitAnd, .w32, .exactAgreement, false⟩
  | 13 => ⟨13, "fetch_or_u32", .bitOr, .w32, .exactAgreement, false⟩
  | 14 => ⟨14, "fetch_xor_u32", .bitXor, .w32, .exactAgreement, false⟩
  | 15 => ⟨15, "fetch_add_wrap_u32", .xadd, .w32, .wrappingOverflowDivergence, false⟩
  | 16 => ⟨16, "fetch_sub_wrap_u32", .xsub, .w32, .wrappingOverflowDivergence, false⟩
  | 17 => ⟨17, "misaligned_load_u32", .load, .w32, .exactAgreement, false⟩
  | 18 => ⟨18, "oversized_u128_load", .load, .w128, .exactAgreement, false⟩
  | 19 => ⟨19, "oob_load_u32", .load, .w32, .exactAgreement, false⟩
  | 20 => ⟨20, "readonly_load_u32", .load, .w32, .exactAgreement, false⟩
  | 21 => ⟨21, "readonly_store_u32", .store, .w32, .readOnlyAllocDivergence, false⟩
  | 22 => ⟨22, "readonly_cas_fail_u32", .cxchg, .w32, .readOnlyAllocDivergence, false⟩
  | 23 => ⟨23, "tb_frozen_load_u32", .load, .w32, .exactAgreement, false⟩
  | 24 => ⟨24, "tb_frozen_cas_fail_u32", .cxchg, .w32, .exactAgreement, false⟩
  | 25 => ⟨25, "tb_frozen_store_u32", .store, .w32, .exactAgreement, true⟩
  | 26 => ⟨26, "tb_frozen_xadd_u32", .xadd, .w32, .exactAgreement, true⟩
  | 27 => ⟨27, "tb_frozen_cas_succ_u32", .cxchg, .w32, .exactAgreement, true⟩
  | idx => ⟨idx, "out_of_range", .load, .w32, .exactAgreement, false⟩

/-! ## §4. Real MiniRust Evaluation (`mrAtomicObserve`) Over `Mach` and `MachTB` -/

/-- Decode the first `n` initialized little-endian bytes of a MiniRust
allocation into an unsigned `Nat`. -/
def decodeLeBytes {P : Type} (n : Nat) (bs : List (AbstractByte P)) : Option Nat :=
  let rec go (shift : Nat) (acc : Nat) : Nat → List (AbstractByte P) → Option Nat
    | 0, _ => some acc
    | k + 1, (.Init b _) :: rest => go (shift + 8) (acc + b.toNat * (2 ^ shift)) k rest
    | _ + 1, _ => none
  go 0 0 n bs

def classifyMrStop : Stop → AtomicAccessOutcome
  | .ub _ => .ub
  | .specPanic _ => .specPanic
  | _ => .invalidOrUnsupported

def obsMrStore {M P : Type} [Memory M] (width : Nat)
    (getAllocs : Machine M → List (List (AbstractByte P)))
    (r : Interp (Value M × Machine M)) : AtomicAccessOutcome :=
  match r with
  | .error s => classifyMrStop s
  | .ok (_, m) =>
    match (getAllocs m).head?.bind (decodeLeBytes width) with
    | some post => .okStore post
    | none => .invalidOrUnsupported

def obsMrScalar {M P : Type} [Memory M] (width : Nat)
    (getAllocs : Machine M → List (List (AbstractByte P)))
    (r : Interp (Value M × Machine M)) : AtomicAccessOutcome :=
  match r with
  | .error s => classifyMrStop s
  | .ok (.Int ret, m) =>
    if ret < 0 then .invalidOrUnsupported
    else
      match (getAllocs m).head?.bind (decodeLeBytes width) with
      | some post => .okScalar ret.toNat post
      | none => .invalidOrUnsupported
  | .ok (_, _) => .invalidOrUnsupported

/-- CAS return-shape *embedding*: MiniRust `AtomicCompareExchange` returns only the loaded `before`
(never a `(T, bool)` pair), so `succeeded` is **synthesized** as `before == expected`. -/
def casFlagSynth (expected : Nat) : AtomicAccessOutcome → AtomicAccessOutcome
  | .okScalar ret post => .okCas ret (ret == expected) post
  | o => o

/-- CAS return-shape *projection* `(old, succeeded) ↦ old`, keeping the post-memory cell. -/
def casOldProjection : AtomicAccessOutcome → AtomicAccessOutcome
  | .okCas ret _ post => .okScalar ret post
  | o => o

/-- Observe a MiniRust CAS: the raw scalar observation (`obsMrScalar`) plus the synthesized flag. -/
def obsMrCas {M P : Type} [Memory M] (width : Nat) (expected : Nat)
    (getAllocs : Machine M → List (List (AbstractByte P)))
    (r : Interp (Value M × Machine M)) : AtomicAccessOutcome :=
  casFlagSynth expected (obsMrScalar width getAllocs r)

private def bmAllocs (m : Mach) : List (List Byte) :=
  m.mem.memory.allocations.map (fun a => a.data)

private def tbAllocs (m : MachTB) : List (List (AbstractByte TreeBorrowsProvenance)) :=
  m.mem.memory.mem.allocations.map (fun a => a.data)

/-- Direct MiniRust `BasicMemory<x86_64>` (`evalIntrinsic` on `Mach`) evaluation
of canonical case `caseIdx ∈ 0..27`. -/
def mrBasicObserve (caseIdx : Nat) : AtomicAccessOutcome :=
  match caseIdx with
  | 0 => obsMrScalar 1 bmAllocs (bmLoad (bmWith (initBytes [200])) bmPtr (.Int itU8))
  | 1 => obsMrStore 1 bmAllocs (bmStore (bmWith (initBytes [0])) bmPtr (.Int 200) (.Int itU8))
  | 2 => obsMrScalar 2 bmAllocs (bmLoad (bmWith (initBytes [0xEF, 0xBE])) bmPtr (.Int itU16))
  | 3 => obsMrStore 2 bmAllocs (bmStore (bmWith (initBytes [0, 0])) bmPtr (.Int 48879) (.Int itU16))
  | 4 => obsMrScalar 4 bmAllocs (bmLoad (bmWith (initBytes [0xEF, 0xBE, 0xAD, 0xDE])) bmPtr (.Int itU32))
  | 5 => obsMrStore 4 bmAllocs (bmStore (bmWith (initBytes [0, 0, 0, 0])) bmPtr (.Int 3735928559) (.Int itU32))
  | 6 => obsMrScalar 8 bmAllocs
      (bmLoad (bmWith (initBytes [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01])) bmPtr (.Int itU64))
  | 7 => obsMrStore 8 bmAllocs
      (bmStore (bmWith (initBytes [0, 0, 0, 0, 0, 0, 0, 0])) bmPtr (.Int 81985529216486895) (.Int itU64))
  | 8 => obsMrCas 4 5 bmAllocs (bmCas bmFive bmPtr 5 9 itU32)
  | 9 => obsMrCas 4 6 bmAllocs (bmCas bmFive bmPtr 6 9 itU32)
  | 10 => obsMrScalar 4 bmAllocs (bmRmw bmFive bmPtr .Add 3 itU32)
  | 11 => obsMrScalar 4 bmAllocs (bmRmw bmFive bmPtr .Sub 2 itU32)
  | 12 => obsMrScalar 4 bmAllocs (bmRmw bmFive bmPtr .BitAnd 4 itU32)
  | 13 => obsMrScalar 4 bmAllocs (bmRmw bmFive bmPtr .BitOr 2 itU32)
  | 14 => obsMrScalar 4 bmAllocs (bmRmw bmFive bmPtr .BitXor 1 itU32)
  | 15 => obsMrScalar 4 bmAllocs
      (bmRmw (bmWith (initBytes [0xFF, 0xFF, 0xFF, 0xFF])) bmPtr .Add 1 itU32)
  | 16 => obsMrScalar 4 bmAllocs
      (bmRmw (bmWith (initBytes [0, 0, 0, 0])) bmPtr .Sub 1 itU32)
  | 17 => obsMrScalar 4 bmAllocs (bmLoad bmFive (bmPtr 1) (.Int itU32))
  | 18 => obsMrScalar 16 bmAllocs (bmLoad bmFive bmPtr (.Int itU128))
  | 19 => obsMrScalar 4 bmAllocs (bmLoad bmFive (bmPtr 8) (.Int itU32))
  | 20 => obsMrScalar 4 bmAllocs (bmLoad bmFive bmPtr (.Int itU32))
  | 21 => obsMrStore 4 bmAllocs (bmStore bmFive bmPtr (.Int 9) (.Int itU32))
  | 22 => obsMrCas 4 6 bmAllocs (bmCas bmFive bmPtr 6 9 itU32)
  | 23 => obsMrScalar 4 bmAllocs (bmLoad bmFive bmPtr (.Int itU32))
  | 24 => obsMrCas 4 6 bmAllocs (bmCas bmFive bmPtr 6 9 itU32)
  | 25 => obsMrStore 4 bmAllocs (bmStore bmFive bmPtr (.Int 9) (.Int itU32))
  | 26 => obsMrScalar 4 bmAllocs (bmRmw bmFive bmPtr .Add 1 itU32)
  | 27 => obsMrCas 4 5 bmAllocs (bmCas bmFive bmPtr 5 9 itU32)
  | _ => .invalidOrUnsupported

/-- Direct MiniRust `TreeBorrowsMemory<x86_64>` (`evalIntrinsicM` on `MachTB`)
evaluation of canonical case `caseIdx ∈ 0..27`. Cases `20..27` execute through
`tbShared` / `tbSharedPtr` (the reachable `Frozen` shared reference). -/
def mrTbObserve (caseIdx : Nat) : AtomicAccessOutcome :=
  match caseIdx with
  | 0 => obsMrScalar 1 tbAllocs (tbLoad (tbWith (initBytes [200])) tbPtr (.Int itU8))
  | 1 => obsMrStore 1 tbAllocs (tbStore (tbWith (initBytes [0])) tbPtr (.Int 200) (.Int itU8))
  | 2 => obsMrScalar 2 tbAllocs (tbLoad (tbWith (initBytes [0xEF, 0xBE])) tbPtr (.Int itU16))
  | 3 => obsMrStore 2 tbAllocs (tbStore (tbWith (initBytes [0, 0])) tbPtr (.Int 48879) (.Int itU16))
  | 4 => obsMrScalar 4 tbAllocs (tbLoad (tbWith (initBytes [0xEF, 0xBE, 0xAD, 0xDE])) tbPtr (.Int itU32))
  | 5 => obsMrStore 4 tbAllocs (tbStore (tbWith (initBytes [0, 0, 0, 0])) tbPtr (.Int 3735928559) (.Int itU32))
  | 6 => obsMrScalar 8 tbAllocs
      (tbLoad (tbWith (initBytes [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01])) tbPtr (.Int itU64))
  | 7 => obsMrStore 8 tbAllocs
      (tbStore (tbWith (initBytes [0, 0, 0, 0, 0, 0, 0, 0])) tbPtr (.Int 81985529216486895) (.Int itU64))
  | 8 => obsMrCas 4 5 tbAllocs (tbCas tbFive tbPtr 5 9 itU32)
  | 9 => obsMrCas 4 6 tbAllocs (tbCas tbFive tbPtr 6 9 itU32)
  | 10 => obsMrScalar 4 tbAllocs (tbRmw tbFive tbPtr .Add 3 itU32)
  | 11 => obsMrScalar 4 tbAllocs (tbRmw tbFive tbPtr .Sub 2 itU32)
  | 12 => obsMrScalar 4 tbAllocs (tbRmw tbFive tbPtr .BitAnd 4 itU32)
  | 13 => obsMrScalar 4 tbAllocs (tbRmw tbFive tbPtr .BitOr 2 itU32)
  | 14 => obsMrScalar 4 tbAllocs (tbRmw tbFive tbPtr .BitXor 1 itU32)
  | 15 => obsMrScalar 4 tbAllocs
      (tbRmw (tbWith (initBytes [0xFF, 0xFF, 0xFF, 0xFF])) tbPtr .Add 1 itU32)
  | 16 => obsMrScalar 4 tbAllocs
      (tbRmw (tbWith (initBytes [0, 0, 0, 0])) tbPtr .Sub 1 itU32)
  | 17 => obsMrScalar 4 tbAllocs (tbLoad tbFive (tbPtr 1) (.Int itU32))
  | 18 => obsMrScalar 16 tbAllocs (tbLoad tbFive tbPtr (.Int itU128))
  | 19 => obsMrScalar 4 tbAllocs (tbLoad tbFive (tbPtr 8) (.Int itU32))
  | 20 => obsMrScalar 4 tbAllocs (tbLoad tbShared tbSharedPtr (.Int itU32))
  | 21 => obsMrStore 4 tbAllocs (tbStore tbShared tbSharedPtr (.Int 9) (.Int itU32))
  | 22 => obsMrCas 4 6 tbAllocs (tbCas tbShared tbSharedPtr 6 9 itU32)
  | 23 => obsMrScalar 4 tbAllocs (tbLoad tbShared tbSharedPtr (.Int itU32))
  | 24 => obsMrCas 4 6 tbAllocs (tbCas tbShared tbSharedPtr 6 9 itU32)
  | 25 => obsMrStore 4 tbAllocs (tbStore tbShared tbSharedPtr (.Int 9) (.Int itU32))
  | 26 => obsMrScalar 4 tbAllocs (tbRmw tbShared tbSharedPtr .Add 1 itU32)
  | 27 => obsMrCas 4 5 tbAllocs (tbCas tbShared tbSharedPtr 5 9 itU32)
  | _ => .invalidOrUnsupported

/-- Unified MiniRust evaluation across both memory models (`Mach` and `MachTB`). -/
def mrAtomicObserve (mode : AtomicMemoryMode) (caseIdx : Nat) : AtomicAccessOutcome :=
  match mode with
  | .basic => mrBasicObserve caseIdx
  | .treeBorrows => mrTbObserve caseIdx

/-- Frozen expected MiniRust table for all 2 modes × 28 cases. -/
def mrExpectedOutcome (mode : AtomicMemoryMode) : Nat → AtomicAccessOutcome
  | 0 => .okScalar 200 200
  | 1 => .okStore 200
  | 2 => .okScalar 48879 48879
  | 3 => .okStore 48879
  | 4 => .okScalar 3735928559 3735928559
  | 5 => .okStore 3735928559
  | 6 => .okScalar 81985529216486895 81985529216486895
  | 7 => .okStore 81985529216486895
  | 8 => .okCas 5 true 9
  | 9 => .okCas 5 false 5
  | 10 => .okScalar 5 8
  | 11 => .okScalar 5 3
  | 12 => .okScalar 5 4
  | 13 => .okScalar 5 7
  | 14 => .okScalar 5 4
  | 15 => .specPanic
  | 16 => .specPanic
  | 17 => .ub
  | 18 => .ub
  | 19 => .ub
  | 20 => .okScalar 5 5
  | 21 => match mode with | .basic => .okStore 9 | .treeBorrows => .ub
  | 22 => .okCas 5 false 5
  | 23 => .okScalar 5 5
  | 24 => .okCas 5 false 5
  | 25 => match mode with | .basic => .okStore 9 | .treeBorrows => .ub
  | 26 => match mode with | .basic => .okScalar 5 6 | .treeBorrows => .ub
  | 27 => match mode with | .basic => .okCas 5 true 9 | .treeBorrows => .ub
  | _ => .invalidOrUnsupported

/-- Frozen expected LeanMiri table for all 2 modes × 28 cases (exact mirror of
`LeanMiriSpec.AtomicIntrinsicsLM.lmExpectedObs`). -/
def lmExpectedOutcome (mode : AtomicMemoryMode) : Nat → AtomicAccessOutcome
  | 0 => .okScalar 200 200
  | 1 => .okStore 200
  | 2 => .okScalar 48879 48879
  | 3 => .okStore 48879
  | 4 => .okScalar 3735928559 3735928559
  | 5 => .okStore 3735928559
  | 6 => .okScalar 81985529216486895 81985529216486895
  | 7 => .okStore 81985529216486895
  | 8 => .okCas 5 true 9
  | 9 => .okCas 5 false 5
  | 10 => .okScalar 5 8
  | 11 => .okScalar 5 3
  | 12 => .okScalar 5 4
  | 13 => .okScalar 5 7
  | 14 => .okScalar 5 4
  | 15 => .okScalar 4294967295 0
  | 16 => .okScalar 0 4294967295
  | 17 => .ub
  | 18 => .ub
  | 19 => .ub
  | 20 => .okScalar 5 5
  | 21 => .ub
  | 22 => .ub
  | 23 => .okScalar 5 5
  | 24 => .okCas 5 false 5
  | 25 => match mode with | .basic => .okStore 9 | .treeBorrows => .ub
  | 26 => match mode with | .basic => .okScalar 5 6 | .treeBorrows => .ub
  | 27 => match mode with | .basic => .okCas 5 true 9 | .treeBorrows => .ub
  | _ => .invalidOrUnsupported

private theorem mrAtomicObserve_table_aux :
    (allAtomicMemoryModes.all fun m =>
      (List.range canonicalCaseCount).all fun idx =>
        decide (mrAtomicObserve m idx = mrExpectedOutcome m idx)) = true := by
  decide +kernel

/-- **Kernel-checked 56-cell MiniRust evaluation table** (`2 modes × 28 cases`)
proving `mrAtomicObserve` (running `evalIntrinsic` on `Mach` and `evalIntrinsicM`
on `MachTB`) matches `mrExpectedOutcome` everywhere (zero `native_decide`). -/
theorem mrAtomicObserve_table (m : AtomicMemoryMode) (idx : Nat)
    (hIdx : idx < canonicalCaseCount) :
    mrAtomicObserve m idx = mrExpectedOutcome m idx := by
  have h1 := List.all_eq_true.mp mrAtomicObserve_table_aux m (allAtomicMemoryModes_complete m)
  have h2 := List.all_eq_true.mp h1 idx (List.mem_range.mpr hIdx)
  exact of_decide_eq_true h2

/-- MiniRust Tree Borrows `Frozen` mode sensitivity on the canonical table:
reads (`23`) and failing CAS (`24`) succeed in both modes, while writes (`25`,
`26`, `27`) succeed on `Mach` and fault `.ub` on `MachTB`. -/
theorem mr_tb_frozen_mode_sensitivity :
    mrAtomicObserve .basic 23 = .okScalar 5 5 ∧
    mrAtomicObserve .treeBorrows 23 = .okScalar 5 5 ∧
    mrAtomicObserve .basic 24 = .okCas 5 false 5 ∧
    mrAtomicObserve .treeBorrows 24 = .okCas 5 false 5 ∧
    mrAtomicObserve .basic 25 = .okStore 9 ∧
    mrAtomicObserve .treeBorrows 25 = .ub ∧
    mrAtomicObserve .basic 26 = .okScalar 5 6 ∧
    mrAtomicObserve .treeBorrows 26 = .ub ∧
    mrAtomicObserve .basic 27 = .okCas 5 true 9 ∧
    mrAtomicObserve .treeBorrows 27 = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact mrAtomicObserve_table _ _ (by decide)

/-- MiniRust `d821c6e3` wrapping-overflow specification panic on cases `15` and
`16` in both memory models. -/
theorem mr_wrapping_overflow_specPanic (m : AtomicMemoryMode) :
    mrAtomicObserve m 15 = .specPanic ∧ mrAtomicObserve m 16 = .specPanic :=
  ⟨mrAtomicObserve_table m 15 (by decide), mrAtomicObserve_table m 16 (by decide)⟩

private theorem expected_agreement_zone_aux :
    (allAtomicMemoryModes.all fun m =>
      (List.range canonicalCaseCount).all fun idx =>
        !(decide ((canonicalCaseMeta idx).comparisonClass = .exactAgreement)) ||
          decide (mrExpectedOutcome m idx = lmExpectedOutcome m idx)) = true := by
  decide +kernel

theorem expected_agreement_zone (m : AtomicMemoryMode) (idx : Nat)
    (hIdx : idx < canonicalCaseCount)
    (hAgree : (canonicalCaseMeta idx).comparisonClass = .exactAgreement) :
    mrExpectedOutcome m idx = lmExpectedOutcome m idx := by
  have h1 := List.all_eq_true.mp expected_agreement_zone_aux m (allAtomicMemoryModes_complete m)
  have h2 := List.all_eq_true.mp h1 idx (List.mem_range.mpr hIdx)
  simp only [decide_eq_true hAgree, Bool.not_true, Bool.false_or] at h2
  exact of_decide_eq_true h2

/-! ## §4.5. Universal MiniRust Bridge Laws (Episode 1 Capstone Integration) -/

/-- Polymorphic `evalIntrinsicM` at `BasicMemory<x86_64>` equals `evalIntrinsic`
on every atomic intrinsic (bridging `MiniRustSpec.AtomicIntrinsicsMR`). -/
theorem mr_universal_bm_eq_atomic (m : Mach) (op : IntrinsicOp)
    (args : List (Val × «Type»)) (retTy : «Type») (hop : isAtomicOp op = true) :
    evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy :=
  evalIntrinsicM_bm_eq_atomic m op args retTy hop

/-- Every successful atomic intrinsic preserves `MachTB.wfLive`
(bridging `MiniRustSpec.AtomicIntrinsicsMR`). -/
theorem mr_universal_tb_wfLive {m m' : MachTB} {op : IntrinsicOp}
    {args : List (Value TBM × «Type»)} {retTy : «Type»} {val : Value TBM}
    (hop : isAtomicOp op = true)
    (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) :
    MiniRustSpec.Correspondence.MachTB.wfLive m' :=
  evalIntrinsicM_atomic_tb_wfLive hop hwf h

/-- Key universal projections of Episode 1's `ep1_minirust_atomic_intrinsics_capstone`:
`MachTB.wfLive` of the fresh cell plus `atomicScalar` agreement on both `Mach`
and `MachTB`. -/
theorem mr_universal_ep1_capstone_bridge :
    MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) ∧
    scalarAgrees BM evalIntrinsic bmFive bmPtr = true ∧
    scalarAgrees TBM evalIntrinsicM tbFive tbPtr = true :=
  ⟨ep1_minirust_atomic_intrinsics_capstone.2.1.2,
   ep1_minirust_atomic_intrinsics_capstone.2.2.1.1,
   ep1_minirust_atomic_intrinsics_capstone.2.2.1.2⟩

/-! ## §5. Frozen Cross-Root Authority Interface (`AtomicLmAuthority` & `AtomicDualContract`) -/

/-- Authority-agnostic LeanMiri interface closed in `AtomicIntrinsicsDualSpecTests`
directly over `LeanMiriSpec.AtomicIntrinsicsLM.lmAtomicObserve`. -/
structure AtomicLmAuthority : Type where
  observe : Bool → Nat → AtomicAccessOutcome
  matchesExpected : ∀ (tb : Bool) (idx : Nat), idx < canonicalCaseCount →
    observe tb idx = lmExpectedOutcome (AtomicMemoryMode.ofLmTreeBorrows tb) idx

/-- Decidable 56-cell (`2 modes × 28 cases`) boolean check verifying that a
LeanMiri observation function agrees with `lmExpectedOutcome` everywhere. -/
def lmAuthorityCheck (obs : Bool → Nat → AtomicAccessOutcome) : Bool :=
  [false, true].all fun tb =>
    (List.range canonicalCaseCount).all fun idx =>
      decide (obs tb idx = lmExpectedOutcome (AtomicMemoryMode.ofLmTreeBorrows tb) idx)

/-- Soundness of `lmAuthorityCheck` (constructive: zero `Classical.choice`). -/
theorem lmAuthorityCheck_sound (obs : Bool → Nat → AtomicAccessOutcome)
    (h : lmAuthorityCheck obs = true) (tb : Bool) (idx : Nat)
    (hIdx : idx < canonicalCaseCount) :
    obs tb idx = lmExpectedOutcome (AtomicMemoryMode.ofLmTreeBorrows tb) idx := by
  have hTb : tb ∈ [false, true] := by cases tb <;> simp
  have h1 := List.all_eq_true.mp h tb hTb
  have h2 := List.all_eq_true.mp h1 idx (List.mem_range.mpr hIdx)
  exact of_decide_eq_true h2

/-- Lift any observation function passing `lmAuthorityCheck` into an
`AtomicLmAuthority`. -/
def lmAuthorityOfCheck (obs : Bool → Nat → AtomicAccessOutcome)
    (h : lmAuthorityCheck obs = true) : AtomicLmAuthority where
  observe := obs
  matchesExpected := lmAuthorityCheck_sound obs h

/-- Dual-authority correspondence contract uniting universal MiniRust laws
(`evalIntrinsicM_bm_eq_atomic`, `evalIntrinsicM_atomic_tb_wfLive`,
`ep1_minirust_atomic_intrinsics_capstone`) and the frozen 28-case (`0..27`)
MiniRust (`Mach` / `MachTB`) vs. LeanMiri (`AtomicMachine.bind` /
`IntrinsicAtomic.eval`) corpus, including explicit divergence witnesses and
joint Tree Borrows mode sensitivity. -/
structure AtomicDualContract : Type where
  lm : AtomicLmAuthority
  mr_bm_eq_atomic : ∀ (m : Mach) (op : IntrinsicOp) (args : List (Val × «Type»)) (retTy : «Type»),
    isAtomicOp op = true → evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy
  mr_tb_wfLive : ∀ (m m' : MachTB) (op : IntrinsicOp) (args : List (Value TBM × «Type»))
    (retTy : «Type») (val : Value TBM),
    isAtomicOp op = true →
    MiniRustSpec.Correspondence.MachTB.wfLive m →
    evalIntrinsicM m op args retTy = .ok (val, m') →
    MiniRustSpec.Correspondence.MachTB.wfLive m'
  mr_ep1_capstone_linked :
    MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) ∧
    scalarAgrees BM evalIntrinsic bmFive bmPtr = true ∧
    scalarAgrees TBM evalIntrinsicM tbFive tbPtr = true
  mr_matches : ∀ (m : AtomicMemoryMode) (idx : Nat), idx < canonicalCaseCount →
    mrAtomicObserve m idx = mrExpectedOutcome m idx
  agreement_zone_exact : ∀ (m : AtomicMemoryMode) (idx : Nat), idx < canonicalCaseCount →
    (canonicalCaseMeta idx).comparisonClass = .exactAgreement →
    mrAtomicObserve m idx = lm.observe m.toLmTreeBorrows idx
  overflow_divergence_explicit : ∀ (m : AtomicMemoryMode),
    mrAtomicObserve m 15 = .specPanic ∧
    lm.observe m.toLmTreeBorrows 15 = .okScalar 4294967295 0 ∧
    mrAtomicObserve m 16 = .specPanic ∧
    lm.observe m.toLmTreeBorrows 16 = .okScalar 0 4294967295
  readonly_alloc_divergence_explicit :
    lm.observe false 21 = .ub ∧
    lm.observe true 21 = .ub ∧
    lm.observe false 22 = .ub ∧
    lm.observe true 22 = .ub ∧
    mrAtomicObserve .basic 21 = .okStore 9 ∧
    mrAtomicObserve .treeBorrows 21 = .ub ∧
    mrAtomicObserve .basic 22 = .okCas 5 false 5 ∧
    mrAtomicObserve .treeBorrows 22 = .okCas 5 false 5
  mode_sensitivity_joint :
    (mrAtomicObserve .basic 25 = lm.observe false 25 ∧
     mrAtomicObserve .basic 25 = .okStore 9 ∧
     mrAtomicObserve .treeBorrows 25 = .ub ∧
     lm.observe true 25 = .ub) ∧
    (mrAtomicObserve .basic 26 = lm.observe false 26 ∧
     mrAtomicObserve .basic 26 = .okScalar 5 6 ∧
     mrAtomicObserve .treeBorrows 26 = .ub ∧
     lm.observe true 26 = .ub) ∧
    (mrAtomicObserve .basic 27 = lm.observe false 27 ∧
     mrAtomicObserve .basic 27 = .okCas 5 true 9 ∧
     mrAtomicObserve .treeBorrows 27 = .ub ∧
     lm.observe true 27 = .ub)

/-- Construct the full `AtomicDualContract` from any verified `AtomicLmAuthority`. -/
def mkAtomicDualContract (lm : AtomicLmAuthority) : AtomicDualContract where
  lm := lm
  mr_bm_eq_atomic := mr_universal_bm_eq_atomic
  mr_tb_wfLive := fun _ _ _ _ _ _ hop hwf h => mr_universal_tb_wfLive hop hwf h
  mr_ep1_capstone_linked := mr_universal_ep1_capstone_bridge
  mr_matches := mrAtomicObserve_table
  agreement_zone_exact := fun m idx hIdx hAgree => by
    rw [mrAtomicObserve_table m idx hIdx,
        lm.matchesExpected m.toLmTreeBorrows idx hIdx,
        AtomicMemoryMode.of_toLmTreeBorrows m]
    exact expected_agreement_zone m idx hIdx hAgree
  overflow_divergence_explicit := fun m => by
    have h15mr := mrAtomicObserve_table m 15 (by decide)
    have h16mr := mrAtomicObserve_table m 16 (by decide)
    have h15lm := lm.matchesExpected m.toLmTreeBorrows 15 (by decide)
    have h16lm := lm.matchesExpected m.toLmTreeBorrows 16 (by decide)
    rw [AtomicMemoryMode.of_toLmTreeBorrows] at h15lm h16lm
    exact ⟨h15mr, h15lm, h16mr, h16lm⟩
  readonly_alloc_divergence_explicit := by
    have h21f := lm.matchesExpected false 21 (by decide)
    have h21t := lm.matchesExpected true 21 (by decide)
    have h22f := lm.matchesExpected false 22 (by decide)
    have h22t := lm.matchesExpected true 22 (by decide)
    have h21mb := mrAtomicObserve_table .basic 21 (by decide)
    have h21mt := mrAtomicObserve_table .treeBorrows 21 (by decide)
    have h22mb := mrAtomicObserve_table .basic 22 (by decide)
    have h22mt := mrAtomicObserve_table .treeBorrows 22 (by decide)
    exact ⟨h21f, h21t, h22f, h22t, h21mb, h21mt, h22mb, h22mt⟩
  mode_sensitivity_joint := by
    have h25mb := mrAtomicObserve_table .basic 25 (by decide)
    have h25mt := mrAtomicObserve_table .treeBorrows 25 (by decide)
    have h25lf := lm.matchesExpected false 25 (by decide)
    have h25lt := lm.matchesExpected true 25 (by decide)
    have h26mb := mrAtomicObserve_table .basic 26 (by decide)
    have h26mt := mrAtomicObserve_table .treeBorrows 26 (by decide)
    have h26lf := lm.matchesExpected false 26 (by decide)
    have h26lt := lm.matchesExpected true 26 (by decide)
    have h27mb := mrAtomicObserve_table .basic 27 (by decide)
    have h27mt := mrAtomicObserve_table .treeBorrows 27 (by decide)
    have h27lf := lm.matchesExpected false 27 (by decide)
    have h27lt := lm.matchesExpected true 27 (by decide)
    refine ⟨⟨?_, h25mb, h25mt, h25lt⟩, ⟨?_, h26mb, h26mt, h26lt⟩, ⟨?_, h27mb, h27mt, h27lt⟩⟩
    · exact h25mb.trans h25lf.symm
    · exact h26mb.trans h26lf.symm
    · exact h27mb.trans h27lf.symm

/-- Direct check-to-contract constructor for the cross-root kernel bridge. -/
def atomicDualContractOfCheck (obs : Bool → Nat → AtomicAccessOutcome)
    (h : lmAuthorityCheck obs = true) : AtomicDualContract :=
  mkAtomicDualContract (lmAuthorityOfCheck obs h)

/-- Named projection theorems for clean cross-root kernel instantiation. -/
theorem contract_agreement_zone_exact (c : AtomicDualContract) :
    ∀ (m : AtomicMemoryMode) (idx : Nat), idx < canonicalCaseCount →
      (canonicalCaseMeta idx).comparisonClass = .exactAgreement →
      mrAtomicObserve m idx = c.lm.observe m.toLmTreeBorrows idx :=
  c.agreement_zone_exact

theorem contract_overflow_divergence (c : AtomicDualContract) :
    ∀ (m : AtomicMemoryMode),
      mrAtomicObserve m 15 = .specPanic ∧
      c.lm.observe m.toLmTreeBorrows 15 = .okScalar 4294967295 0 ∧
      mrAtomicObserve m 16 = .specPanic ∧
      c.lm.observe m.toLmTreeBorrows 16 = .okScalar 0 4294967295 :=
  c.overflow_divergence_explicit

theorem contract_readonly_alloc_divergence (c : AtomicDualContract) :
    c.lm.observe false 21 = .ub ∧
    c.lm.observe true 21 = .ub ∧
    c.lm.observe false 22 = .ub ∧
    c.lm.observe true 22 = .ub ∧
    mrAtomicObserve .basic 21 = .okStore 9 ∧
    mrAtomicObserve .treeBorrows 21 = .ub ∧
    mrAtomicObserve .basic 22 = .okCas 5 false 5 ∧
    mrAtomicObserve .treeBorrows 22 = .okCas 5 false 5 :=
  c.readonly_alloc_divergence_explicit

theorem contract_mode_sensitivity_joint (c : AtomicDualContract) :
    (mrAtomicObserve .basic 25 = c.lm.observe false 25 ∧
     mrAtomicObserve .basic 25 = .okStore 9 ∧
     mrAtomicObserve .treeBorrows 25 = .ub ∧
     c.lm.observe true 25 = .ub) ∧
    (mrAtomicObserve .basic 26 = c.lm.observe false 26 ∧
     mrAtomicObserve .basic 26 = .okScalar 5 6 ∧
     mrAtomicObserve .treeBorrows 26 = .ub ∧
     c.lm.observe true 26 = .ub) ∧
    (mrAtomicObserve .basic 27 = c.lm.observe false 27 ∧
     mrAtomicObserve .basic 27 = .okCas 5 true 9 ∧
     mrAtomicObserve .treeBorrows 27 = .ub ∧
     c.lm.observe true 27 = .ub) :=
  c.mode_sensitivity_joint

theorem contract_mr_universal_laws (c : AtomicDualContract) :
    (∀ (m : Mach) (op : IntrinsicOp) (args : List (Val × «Type»)) (retTy : «Type»),
      isAtomicOp op = true →
      evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy) ∧
    (∀ (m m' : MachTB) (op : IntrinsicOp) (args : List (Value TBM × «Type»))
      (retTy : «Type») (val : Value TBM),
      isAtomicOp op = true →
      MiniRustSpec.Correspondence.MachTB.wfLive m →
      evalIntrinsicM m op args retTy = .ok (val, m') →
      MiniRustSpec.Correspondence.MachTB.wfLive m') ∧
    (MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) ∧
      scalarAgrees BM evalIntrinsic bmFive bmPtr = true ∧
      scalarAgrees TBM evalIntrinsicM tbFive tbPtr = true) :=
  ⟨c.mr_bm_eq_atomic, c.mr_tb_wfLive, c.mr_ep1_capstone_linked⟩

/-! ## §5.5. CAS Return-Shape Projection, Universal Divergence Laws & Exact Divergence Set -/

/-- Erasing the synthesized flag recovers the erased raw observation (the flag carries no data). -/
theorem casOldProjection_casFlagSynth (expected : Nat) (o : AtomicAccessOutcome) :
    casOldProjection (casFlagSynth expected o) = casOldProjection o := by
  cases o <;> rfl

/-- **Cross-authority CAS return shape**: on every agreement-zone cell, LeanMiri's
`(old, succeeded)` erased to `old` equals MiniRust's erased observation (same `old`, same post
cell); unerased `agreement_zone_exact` further pins LeanMiri's real flag to `old == expected`. -/
theorem contract_cas_return_shape (c : AtomicDualContract) (m : AtomicMemoryMode) (idx : Nat)
    (hIdx : idx < canonicalCaseCount)
    (hAgree : (canonicalCaseMeta idx).comparisonClass = .exactAgreement) :
    casOldProjection (c.lm.observe m.toLmTreeBorrows idx) =
      casOldProjection (mrAtomicObserve m idx) :=
  congrArg casOldProjection (c.agreement_zone_exact m idx hIdx hAgree).symm

/-- Universal MiniRust CAS law: a failing CAS returns exactly `before` + the post-load machine. -/
theorem mr_universal_cas_failure_returns_before :
    type_of% @atomicCompareExchange_failure := @atomicCompareExchange_failure

/-- Universal MiniRust `d821c6e3` RMW law (divergence 1): out-of-range is `Stop.specPanic`. -/
theorem mr_universal_rmw_out_of_range_specPanic :
    type_of% @atomicFetchAndOp_out_of_range_specPanic := @atomicFetchAndOp_out_of_range_specPanic

/-- Universal MiniRust size rule (case `18`): `AtomicLoad` above `MAX_ATOMIC_SIZE` is UB. -/
theorem mr_universal_atomicLoad_size_too_big_ub :
    type_of% @atomicLoad_size_too_big_ub := @atomicLoad_size_too_big_ub

/-- Exact divergence set (7/56 cells): `15`, `16`, `22`, and `21` in `basic` mode only. -/
def divergesAt (m : AtomicMemoryMode) : Nat → Bool
  | 15 | 16 | 22 => true
  | 21 => match m with | .basic => true | .treeBorrows => false
  | _ => false

private theorem divergence_set_exact_aux :
    (allAtomicMemoryModes.all fun m =>
      (List.range canonicalCaseCount).all fun idx =>
        (divergesAt m idx || decide (mrExpectedOutcome m idx = lmExpectedOutcome m idx)) &&
        (!(divergesAt m idx) ||
          decide (mrExpectedOutcome m idx ≠ lmExpectedOutcome m idx))) = true := by
  decide +kernel

/-- **Exact divergence set** (both directions): the authorities agree on every cell outside
`divergesAt` (49 cells, incl. `(treeBorrows, 21)`) and provably differ on every cell inside it. -/
theorem contract_divergence_set_exact (c : AtomicDualContract) (m : AtomicMemoryMode)
    (idx : Nat) (hIdx : idx < canonicalCaseCount) :
    (divergesAt m idx = false → mrAtomicObserve m idx = c.lm.observe m.toLmTreeBorrows idx) ∧
    (divergesAt m idx = true → mrAtomicObserve m idx ≠ c.lm.observe m.toLmTreeBorrows idx) := by
  have h1 := List.all_eq_true.mp divergence_set_exact_aux m (allAtomicMemoryModes_complete m)
  have h2 := List.all_eq_true.mp h1 idx (List.mem_range.mpr hIdx)
  rw [mrAtomicObserve_table m idx hIdx, c.lm.matchesExpected m.toLmTreeBorrows idx hIdx,
      AtomicMemoryMode.of_toLmTreeBorrows m]
  refine ⟨fun hNo => ?_, fun hYes => ?_⟩
  · simp only [hNo, Bool.false_or, Bool.not_false, Bool.true_or, Bool.and_true] at h2
    exact of_decide_eq_true h2
  · simp only [hYes, Bool.true_or, Bool.not_true, Bool.false_or, Bool.true_and] at h2
    exact of_decide_eq_true h2

private theorem casOldProjection_ite {P : Prop} [d : Decidable P] (a b : AtomicAccessOutcome)
    (ha : casOldProjection a = a) (hb : casOldProjection b = b) :
    casOldProjection (if P then a else b) = if P then a else b := by cases d <;> assumption
/-- Erasing the synthesized flag from `obsMrCas` recovers raw `obsMrScalar` identically. -/
theorem casOldProjection_obsMrCas {M P : Type} [Memory M] (width expected : Nat)
    (getAllocs : Machine M → List (List (AbstractByte P))) (r : Interp (Value M × Machine M)) :
    casOldProjection (obsMrCas width expected getAllocs r) = obsMrScalar width getAllocs r := by
  unfold obsMrCas; rw [casOldProjection_casFlagSynth]; unfold obsMrScalar
  cases r with
  | error s => cases s <;> rfl
  | ok vm =>
    rcases vm with ⟨v, m⟩; cases v with
    | Int _ => dsimp only; exact casOldProjection_ite _ _ rfl (by cases (getAllocs m).head?.bind (decodeLeBytes width) <;> rfl)
    | _ => rfl
/-- Observe a signed/unsigned MiniRust scalar as its `width`-byte two's-complement bit pattern. -/
def obsMrTwosComp {M P : Type} [Memory M] (width : Nat) (getAllocs : Machine M → List (List (AbstractByte P))) :
    Interp (Value M × Machine M) → AtomicAccessOutcome
  | .error s => classifyMrStop s
  | .ok (.Int ret, m) =>
    let bits : Nat := if ret < 0 then (ret + ((2 ^ (8 * width) : Nat) : Int)).toNat else ret.toNat
    match (getAllocs m).head?.bind (decodeLeBytes width) with | some p => .okScalar bits p | none => .invalidOrUnsupported
  | .ok (_, _) => .invalidOrUnsupported
/-- **Signed vs. unsigned polarity & `usize` parity on `Mach`/`MachTB`** (bitwise `&`/`|`/`^` on `Mach` only): `IntType.usize_ty = itU64`,
`usize` `xadd`/`cas`, signed `-5` (`0xFFFFFFFB`) RMWs, and `0xFFFFFFFB + 5` polarity flip. -/
theorem mr_signed_unsigned_polarity_and_usize_parity :
    let bmN := bmWith (initBytes [0xFB, 0xFF, 0xFF, 0xFF]); let tbN := tbWith (initBytes [0xFB, 0xFF, 0xFF, 0xFF]);
    let bm5 := bmWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0]); let tb5 := tbWith (initBytes [5, 0, 0, 0, 0, 0, 0, 0]);
    IntType.usize_ty = itU64 ∧ obsMrScalar 8 bmAllocs (bmRmw bm5 bmPtr .Add 3 IntType.usize_ty) = .okScalar 5 8 ∧
    obsMrScalar 8 tbAllocs (tbRmw tb5 tbPtr .Add 3 IntType.usize_ty) = .okScalar 5 8 ∧
    obsMrCas 8 5 bmAllocs (bmCas bm5 bmPtr 5 9 IntType.usize_ty) = .okCas 5 true 9 ∧ obsMrCas 8 5 tbAllocs (tbCas tb5 tbPtr 5 9 IntType.usize_ty) = .okCas 5 true 9 ∧
    obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .Add 3 itI32) = .okScalar 0xFFFFFFFB 0xFFFFFFFE ∧ obsMrTwosComp 4 tbAllocs (tbRmw tbN tbPtr .Add 3 itI32) = .okScalar 0xFFFFFFFB 0xFFFFFFFE ∧
    obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .Sub 3 itI32) = .okScalar 0xFFFFFFFB 0xFFFFFFF8 ∧ obsMrTwosComp 4 tbAllocs (tbRmw tbN tbPtr .Sub 3 itI32) = .okScalar 0xFFFFFFFB 0xFFFFFFF8 ∧
    obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .BitAnd 3 itI32) = .okScalar 0xFFFFFFFB 3 ∧ obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .BitOr 3 itI32) = .okScalar 0xFFFFFFFB 0xFFFFFFFB ∧ obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .BitXor 3 itI32) = .okScalar 0xFFFFFFFB 0xFFFFFFF8 ∧
    obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .Add 5 itI32) = .okScalar 0xFFFFFFFB 0 ∧ obsMrTwosComp 4 tbAllocs (tbRmw tbN tbPtr .Add 5 itI32) = .okScalar 0xFFFFFFFB 0 ∧
    obsMrTwosComp 4 bmAllocs (bmRmw bmN bmPtr .Add 5 itU32) = .specPanic ∧ obsMrTwosComp 4 tbAllocs (tbRmw tbN tbPtr .Add 5 itU32) = .specPanic ∧
    (match bmLoad bmN bmPtr (.Int itI32) with | .ok (.Int v, _) => decide (v < 3) | _ => false) = true ∧
    (match bmLoad bmN bmPtr (.Int itU32) with | .ok (.Int v, _) => decide (v < 3) | _ => false) = false := by decide +kernel

/-- Thread ONE machine through `steps`, observing every step; stops after the first `Stop`. -/
def mrTraceGo {V Mc : Type} :
    List ((Mc → Interp (V × Mc)) × (Interp (V × Mc) → AtomicAccessOutcome)) → Mc → List AtomicAccessOutcome
  | [], _ => []
  | (stepFn, obsFn) :: rest, m =>
    let r := stepFn m
    obsFn r :: (match r with | .ok (_, m') => mrTraceGo rest m' | .error _ => [])

/-- Threaded `u32` trace `store 5 → fetch_add 3 → cas(5→9)✗ → cas(8→9)✓ → load` on ONE `Mach`/`MachTB`. -/
def mrAtomicTrace : AtomicMemoryMode → List AtomicAccessOutcome
  | .basic => mrTraceGo
      [ (fun (m : Mach) => bmStore m bmPtr (.Int 5) (.Int itU32), obsMrStore 4 bmAllocs),
        (fun m => bmRmw m bmPtr .Add 3 itU32, obsMrScalar 4 bmAllocs),
        (fun m => bmCas m bmPtr 5 9 itU32, obsMrCas 4 5 bmAllocs),
        (fun m => bmCas m bmPtr 8 9 itU32, obsMrCas 4 8 bmAllocs),
        (fun m => bmLoad m bmPtr (.Int itU32), obsMrScalar 4 bmAllocs) ] (bmWith (initBytes [0, 0, 0, 0]))
  | .treeBorrows => mrTraceGo
      [ (fun (m : MachTB) => tbStore m tbPtr (.Int 5) (.Int itU32), obsMrStore 4 tbAllocs),
        (fun m => tbRmw m tbPtr .Add 3 itU32, obsMrScalar 4 tbAllocs),
        (fun m => tbCas m tbPtr 5 9 itU32, obsMrCas 4 5 tbAllocs),
        (fun m => tbCas m tbPtr 8 9 itU32, obsMrCas 4 8 tbAllocs),
        (fun m => tbLoad m tbPtr (.Int itU32), obsMrScalar 4 tbAllocs) ] (tbWith (initBytes [0, 0, 0, 0]))

/-- **Threaded 5-step trace on `Mach`/`MachTB`**: each step observes its predecessor's write. -/
theorem mrAtomicTrace_table (m : AtomicMemoryMode) : mrAtomicTrace m =
    ([.okStore 5, .okScalar 5 8, .okCas 8 false 8, .okCas 8 true 9, .okScalar 9 9] : List AtomicAccessOutcome) := by
  cases m <;> decide +kernel

/-- Cross-authority trace check: a (translated LeanMiri) trace must equal MiniRust's in BOTH modes. -/
def lmTraceAuthorityCheck (obs : Bool → List AtomicAccessOutcome) : Bool :=
  decide (obs (AtomicMemoryMode.toLmTreeBorrows .basic) = mrAtomicTrace .basic ∧
    obs (AtomicMemoryMode.toLmTreeBorrows .treeBorrows) = mrAtomicTrace .treeBorrows)

/-- Soundness of `lmTraceAuthorityCheck`: a passing check is step-for-step trace agreement. -/
theorem lmTraceAuthorityCheck_sound (obs : Bool → List AtomicAccessOutcome)
    (h : lmTraceAuthorityCheck obs = true) (m : AtomicMemoryMode) :
    obs m.toLmTreeBorrows = mrAtomicTrace m := by
  unfold lmTraceAuthorityCheck at h
  cases m
  · exact (of_decide_eq_true h).1
  · exact (of_decide_eq_true h).2

/-! ## §6. Exhaustive Import-Isolation, Constructive-Codec, & Axiom Audit -/

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported in Anneal.Mir.AtomicIntrinsicsDualSpec"
  let constructiveDecls : List Lean.Name :=
    [ ``atomicOutcomeCodec
    , ``atomicOutcomeCodec_tight
    , ``atomicOutcomeCodec_encode_injective
    , ``atomicOutcomeCodec_decode_injective_on_valid
    , ``lmAuthorityCheck_sound
    , ``casOldProjection_casFlagSynth ]
  for c in constructiveDecls do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "constructive codec {c} must not depend on {a}"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on {a} (compiler-trusting evaluation)"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
    if (`Anneal.Mir.AtomicIntrinsicsDualSpec).isPrefixOf c then
      for u in info.type.getUsedConstants do
        if (`Trusted.Rustc).isPrefixOf u then
          throwError "shadow-evaluator violation: {c} type references {u}"
      if let .defnInfo v := info then
        for u in v.value.getUsedConstants do
          if (`Trusted.Rustc).isPrefixOf u then
            throwError "shadow-evaluator violation: {c} value references {u}"
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 29 then
    throwError "axiom audit is vacuous: only {theorems} theorems seen"
  logInfo m!"Anneal.Mir.AtomicIntrinsicsDualSpec: verified {checked} declarations ({theorems} theorems), constructive codecs choice-free, import_isolated=true, sorry_free=true, ofReduceBool_free=true"

end AxiomAudit

end Anneal.Mir.AtomicIntrinsicsDualSpec
