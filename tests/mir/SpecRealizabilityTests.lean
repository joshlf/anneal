-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Trusted
import Anneal.SpecRealizability

/-!
# Test Suite & Kernel Axiom Audit for `Anneal.SpecRealizability`

Exercises:
1. **Positive Suite**: Concrete realistic contracts (`sliceIsEmpty`, `u32CheckedAdd`,
   `rangeClamp`, `statefulCounterStep`, plus conditional boilerplate-branching
   `MirCallContract`), proving `PreconditionSatisfiable`, `ContractRealizable`,
   `PostconditionDichotomy`, `ContractDeterministic`, `StatefulClaimReturnDichotomy`,
   `MirCallContractRealizable`, `MirCallContractNormalDichotomy`, and
   `ExternalSpecEnsuresDichotomy`, paired with compile-time `#eval` checks via
   `assertEnsuresBindsOutput` and `assertDeclEnsuresBindsOutput`.
2. **Negative & Domain-Trap Suite**: All 5 `VacuityClass` failure modes
   (`DeadPrecondition`, `SpecViolation`, `TrivialPostcondition`,
   `UnboundReturnOutput`, `SurvivedAllMutants`) plus explicit instantiations of
   external-spec Soundness Traps 1, 2, and 3, paired with kernel refutation theorems
   and compile-time `#eval assertEnsuresVacuous` / `assertDeclEnsuresVacuous` checks.
3. **Compile-Time Kernel Axiom Audit (EOF)**: Audits every constant under
   `Anneal.SpecRealizability` and `SpecRealizabilityTests` for `isUnsafe == false`,
   zero axioms, zero `sorryAx`/`Lean.ofReduceBool`/`Lean.trustCompiler`, axioms
   strictly within `[propext, Classical.choice, Quot.sound]`, and `≥ 30` theorems.
-/

namespace SpecRealizabilityTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Layout
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.SpecRealizability

/-! ## Shared MIR Test Fixtures & Structural Injectivity Helpers -/

@[reducible] private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] private def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] private def optionU32MirTy : Ty :=
  { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 0 }

@[reducible] private def mkPrimLayout (bytes : Nat) : TypeLayout := {
  size := { bytes := bytes }
  align := { bytes := bytes }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible] private def boolLayout : TypeLayout := mkPrimLayout 1
@[reducible] private def u32Layout : TypeLayout := mkPrimLayout 4

@[reducible] private def mkLocalDecl (ty : Ty) : LocalDecl :=
  { mutability := .not, ty := ty, debugName := none }

@[reducible] private def mkStubBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (retLayout : TypeLayout)
    (canUnwind : Bool := true) : CapturedMir := {
  defPath := defPath
  phase := .runtimePostCleanup
  role := .subject
  argCount := argCount
  localDecls := localDecls
  basicBlocks := []
  fnAbi := {
    args := []
    ret := { layout := retLayout, mode := .direct }
    conv := .rust
    canUnwind := canUnwind
  }
  layouts := emptyLayoutTable
  allocations := []
}

private theorem scalar_bits_inj {b₁ b₂ s₁ s₂ : Nat}
    (h : Value.scalar { bits := b₁, sizeBytes := s₁ } =
         Value.scalar { bits := b₂, sizeBytes := s₂ }) :
    b₁ = b₂ ∧ s₁ = s₂ := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem aggregate_variant_inj {v₁ v₂ : VariantIdx} {f₁ f₂ : List Value}
    (h : Value.aggregate v₁ f₁ = Value.aggregate v₂ f₂) :
    v₁ = v₂ ∧ f₁ = f₂ := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem list_singleton_inj {α : Type} {a b : α} (h : [a] = [b]) : a = b := by
  cases h
  rfl

private theorem list_pair_inj {α : Type} {a₁ a₂ b₁ b₂ : α}
    (h : [a₁, a₂] = [b₁, b₂]) : a₁ = b₁ ∧ a₂ = b₂ := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem list_triple_inj {α : Type} {a₁ a₂ a₃ b₁ b₂ b₃ : α}
    (h : [a₁, a₂, a₃] = [b₁, b₂, b₃]) : a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

private theorem memory_nextTag_ne_1_2 :
    emptyMemory ≠ { emptyMemory with nextTag := 2 } := by
  intro h
  have hTag : emptyMemory.nextTag = ({ emptyMemory with nextTag := 2 } : Memory).nextTag :=
    congrArg Memory.nextTag h
  dsimp [emptyMemory] at hTag
  omega

private theorem optionEmpty_subsingleton : Subsingleton (Option Empty) :=
  ⟨fun a b => by
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some e => exact nomatch e
    | some e => exact nomatch e⟩

/-! ## 1. Positive Suite -/

/-! ### 1.1 `sliceIsEmpty` (`ret = 1` iff `len = 0`) -/

def sliceIsEmptySidecar : CapturedMir :=
  mkStubBody "core::slice::is_empty" 1
    [mkLocalDecl boolMirTy, mkLocalDecl usizeMirTy]
    boolLayout true

def sliceIsEmptyPre (args : List Value) : Prop :=
  ∃ len : Nat, len < scalarModulus 8 ∧ args = [.scalar { bits := len, sizeBytes := 8 }]

def sliceIsEmptyPost (args : List Value) (ret : Value) : Prop :=
  ∃ len : Nat,
    args = [.scalar { bits := len, sizeBytes := 8 }] ∧
    ret = .scalar { bits := if len = 0 then 1 else 0, sizeBytes := 1 }

def sliceIsEmptyClaim : Claim := {
  body := sliceIsEmptySidecar
  pre := sliceIsEmptyPre
  post := sliceIsEmptyPost
}

def sliceIsEmptyExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    sliceIsEmptyPre sliceIsEmptyPost

theorem sliceIsEmpty_preSatisfiable : ClaimPreSatisfiable sliceIsEmptyClaim :=
  ⟨[.scalar { bits := 0, sizeBytes := 8 }], 0, by decide, rfl⟩

theorem sliceIsEmpty_realizable : ClaimRealizable sliceIsEmptyClaim :=
  ⟨[.scalar { bits := 0, sizeBytes := 8 }],
    ⟨0, by decide, rfl⟩,
    .scalar { bits := 1, sizeBytes := 1 },
    ⟨0, rfl, rfl⟩⟩

theorem sliceIsEmpty_dichotomy : ClaimDichotomy sliceIsEmptyClaim := by
  refine ⟨[.scalar { bits := 0, sizeBytes := 8 }], ⟨0, by decide, rfl⟩,
    ⟨.scalar { bits := 1, sizeBytes := 1 }, ⟨0, rfl, rfl⟩⟩,
    ⟨.scalar { bits := 0, sizeBytes := 1 }, ?_⟩⟩
  rintro ⟨len, hArgs, hRet⟩
  have hLen : (0 : Nat) = len := (scalar_bits_inj (list_singleton_inj hArgs)).1
  subst hLen
  have hBits : (0 : Nat) = (if (0 : Nat) = 0 then 1 else 0) := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem sliceIsEmpty_deterministic : ClaimDeterministic sliceIsEmptyClaim := by
  rintro args y₁ y₂ _ ⟨len₁, hArgs₁, hRet₁⟩ ⟨len₂, hArgs₂, hRet₂⟩
  have hEqArgs : [Value.scalar { bits := len₁, sizeBytes := 8 }] =
      [Value.scalar { bits := len₂, sizeBytes := 8 }] :=
    hArgs₁.symm.trans hArgs₂
  have hLen : len₁ = len₂ := (scalar_bits_inj (list_singleton_inj hEqArgs)).1
  subst hLen
  exact hRet₁.trans hRet₂.symm

theorem sliceIsEmpty_ext_realizable :
    MirCallContractRealizable sliceIsEmptyExtContract := by
  let req : MirCallReq := {
    defPath := "core::slice::is_empty"
    args := [.scalar { bits := 0, sizeBytes := 8 }]
    memory := emptyMemory
  }
  refine externalSpecCallContract_realizable_of_witness
    req (.scalar { bits := 1, sizeBytes := 1 }) ?_ ?_ ?_
  · exact ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨0, rfl, rfl⟩

theorem sliceIsEmpty_ext_ensuresDichotomy :
    ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
      sliceIsEmptyPre sliceIsEmptyPost := by
  apply (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre sliceIsEmptyPost).mpr
  let req : MirCallReq := {
    defPath := "core::slice::is_empty"
    args := [.scalar { bits := 0, sizeBytes := 8 }]
    memory := emptyMemory
  }
  refine ⟨req, emptyMemory,
    .scalar { bits := 1, sizeBytes := 1 },
    .scalar { bits := 0, sizeBytes := 1 },
    ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩,
    callFramePreserved_refl emptyMemory,
    ⟨1, by decide, rfl⟩,
    ⟨0, by decide, rfl⟩,
    ⟨0, rfl, rfl⟩,
    ?_⟩
  rintro ⟨len, hArgs, hRet⟩
  have hLen : (0 : Nat) = len := (scalar_bits_inj (list_singleton_inj hArgs)).1
  subst hLen
  have hBits : (0 : Nat) = (if (0 : Nat) = 0 then 1 else 0) := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem sliceIsEmpty_ext_normalDichotomy :
    MirCallContractNormalDichotomy sliceIsEmptyExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    sliceIsEmpty_ext_ensuresDichotomy).toNormalDichotomy

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``sliceIsEmptyPost) (some (Lean.mkConst ``sliceIsEmptyPre))
#eval assertDeclEnsuresBindsOutput ``sliceIsEmptyClaim
#eval assertDeclEnsuresBindsOutput ``sliceIsEmptyExtContract

/-! ### 1.2 `u32CheckedAdd` (in-range `Some (a + b)` and overflow `None`) -/

def u32CheckedAddSidecar : CapturedMir :=
  mkStubBody "core::num::u32::checked_add" 2
    [mkLocalDecl optionU32MirTy, mkLocalDecl u32MirTy, mkLocalDecl u32MirTy]
    u32Layout true

def u32CheckedAddPre (args : List Value) : Prop :=
  ∃ a b : Nat,
    a < scalarModulus 4 ∧ b < scalarModulus 4 ∧
    args = [.scalar { bits := a, sizeBytes := 4 }, .scalar { bits := b, sizeBytes := 4 }]

def u32CheckedAddPost (args : List Value) (ret : Value) : Prop :=
  ∃ a b : Nat,
    args = [.scalar { bits := a, sizeBytes := 4 }, .scalar { bits := b, sizeBytes := 4 }] ∧
    ((a + b < scalarModulus 4 ∧
        ret = .aggregate 1 [.scalar { bits := a + b, sizeBytes := 4 }]) ∨
     (scalarModulus 4 ≤ a + b ∧ ret = .aggregate 0 []))

def u32CheckedAddClaim : Claim := {
  body := u32CheckedAddSidecar
  pre := u32CheckedAddPre
  post := u32CheckedAddPost
}

def u32CheckedAddExtContract : MirCallContract :=
  externalSpecCallContract "core::num::u32::checked_add" u32CheckedAddSidecar
    u32CheckedAddPre u32CheckedAddPost

theorem u32CheckedAdd_preSatisfiable : ClaimPreSatisfiable u32CheckedAddClaim :=
  ⟨[.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }],
    2, 3, by decide, by decide, rfl⟩

theorem u32CheckedAdd_realizable_inRange : ClaimRealizable u32CheckedAddClaim :=
  ⟨[.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }],
    ⟨2, 3, by decide, by decide, rfl⟩,
    .aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }],
    ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩⟩

theorem u32CheckedAdd_realizable_overflow : ClaimRealizable u32CheckedAddClaim :=
  ⟨[.scalar { bits := scalarModulus 4 - 1, sizeBytes := 4 },
    .scalar { bits := 1, sizeBytes := 4 }],
    ⟨scalarModulus 4 - 1, 1, by decide, by decide, rfl⟩,
    .aggregate 0 [],
    ⟨scalarModulus 4 - 1, 1, rfl, Or.inr ⟨by decide, rfl⟩⟩⟩

theorem u32CheckedAdd_dichotomy : ClaimDichotomy u32CheckedAddClaim := by
  refine ⟨[.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }],
    ⟨2, 3, by decide, by decide, rfl⟩,
    ⟨.aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }],
      ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩⟩,
    ⟨.aggregate 0 [], ?_⟩⟩
  rintro ⟨a, b, hArgs, hBranch⟩
  rcases list_pair_inj hArgs with ⟨ha, hb⟩
  have ha' : (2 : Nat) = a := (scalar_bits_inj ha).1
  have hb' : (3 : Nat) = b := (scalar_bits_inj hb).1
  subst ha'; subst hb'
  rcases hBranch with ⟨_, hEq⟩ | ⟨hOvf, _⟩
  · have hv : (0 : Nat) = 1 := (aggregate_variant_inj hEq).1
    omega
  · exact absurd hOvf (by decide)

theorem u32CheckedAdd_deterministic : ClaimDeterministic u32CheckedAddClaim := by
  rintro args y₁ y₂ _ ⟨a₁, b₁, hArgs₁, hB₁⟩ ⟨a₂, b₂, hArgs₂, hB₂⟩
  have hPair := list_pair_inj (hArgs₁.symm.trans hArgs₂)
  have ha : a₁ = a₂ := (scalar_bits_inj hPair.1).1
  have hb : b₁ = b₂ := (scalar_bits_inj hPair.2).1
  subst ha; subst hb
  rcases hB₁ with ⟨hLt₁, hEq₁⟩ | ⟨hGe₁, hEq₁⟩
  · rcases hB₂ with ⟨_, hEq₂⟩ | ⟨hGe₂, _⟩
    · exact hEq₁.trans hEq₂.symm
    · omega
  · rcases hB₂ with ⟨hLt₂, _⟩ | ⟨_, hEq₂⟩
    · omega
    · exact hEq₁.trans hEq₂.symm

theorem u32CheckedAdd_ext_realizable :
    MirCallContractRealizable u32CheckedAddExtContract := by
  let req : MirCallReq := {
    defPath := "core::num::u32::checked_add"
    args := [.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }]
    memory := emptyMemory
  }
  refine externalSpecCallContract_realizable_of_witness
    req (.aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }]) ?_ ?_ ?_
  · exact ⟨rfl, rfl, ⟨⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩, trivial⟩,
      ⟨2, 3, by decide, by decide, rfl⟩⟩
  · rfl
  · exact ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩

theorem u32CheckedAdd_ext_ensuresDichotomy :
    ExternalSpecEnsuresDichotomy "core::num::u32::checked_add" u32CheckedAddSidecar
      u32CheckedAddPre u32CheckedAddPost := by
  apply (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::num::u32::checked_add" u32CheckedAddSidecar u32CheckedAddPre u32CheckedAddPost).mpr
  let req : MirCallReq := {
    defPath := "core::num::u32::checked_add"
    args := [.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }]
    memory := emptyMemory
  }
  refine ⟨req, emptyMemory,
    .aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }],
    .aggregate 0 [],
    ⟨rfl, rfl, ⟨⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩, trivial⟩,
      ⟨2, 3, by decide, by decide, rfl⟩⟩,
    callFramePreserved_refl emptyMemory,
    rfl,
    rfl,
    ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩,
    ?_⟩
  rintro ⟨a, b, hArgs, hBranch⟩
  rcases list_pair_inj hArgs with ⟨ha, hb⟩
  have ha' : (2 : Nat) = a := (scalar_bits_inj ha).1
  have hb' : (3 : Nat) = b := (scalar_bits_inj hb).1
  subst ha'; subst hb'
  rcases hBranch with ⟨_, hEq⟩ | ⟨hOvf, _⟩
  · have hv : (0 : Nat) = 1 := (aggregate_variant_inj hEq).1
    omega
  · exact absurd hOvf (by decide)

theorem u32CheckedAdd_ext_normalDichotomy :
    MirCallContractNormalDichotomy u32CheckedAddExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    u32CheckedAdd_ext_ensuresDichotomy).toNormalDichotomy

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``u32CheckedAddPost) (some (Lean.mkConst ``u32CheckedAddPre))
#eval assertDeclEnsuresBindsOutput ``u32CheckedAddClaim
#eval assertDeclEnsuresBindsOutput ``u32CheckedAddExtContract

/-! ### 1.3 `rangeClamp` (`lo ≤ hi`, `ret = min (max val lo) hi`) -/

def rangeClampSidecar : CapturedMir :=
  mkStubBody "core::cmp::Ord::clamp" 3
    [mkLocalDecl u32MirTy, mkLocalDecl u32MirTy, mkLocalDecl u32MirTy, mkLocalDecl u32MirTy]
    u32Layout true

def rangeClampPre (args : List Value) : Prop :=
  ∃ val lo hi : Nat,
    val < scalarModulus 4 ∧ lo < scalarModulus 4 ∧ hi < scalarModulus 4 ∧ lo ≤ hi ∧
    args = [
      .scalar { bits := val, sizeBytes := 4 },
      .scalar { bits := lo, sizeBytes := 4 },
      .scalar { bits := hi, sizeBytes := 4 }
    ]

def rangeClampPost (args : List Value) (ret : Value) : Prop :=
  ∃ val lo hi : Nat,
    args = [
      .scalar { bits := val, sizeBytes := 4 },
      .scalar { bits := lo, sizeBytes := 4 },
      .scalar { bits := hi, sizeBytes := 4 }
    ] ∧
    ret = .scalar { bits := min (max val lo) hi, sizeBytes := 4 }

def rangeClampClaim : Claim := {
  body := rangeClampSidecar
  pre := rangeClampPre
  post := rangeClampPost
}

def rangeClampExtContract : MirCallContract :=
  externalSpecCallContract "core::cmp::Ord::clamp" rangeClampSidecar
    rangeClampPre rangeClampPost

theorem rangeClamp_preSatisfiable : ClaimPreSatisfiable rangeClampClaim :=
  ⟨[.scalar { bits := 15, sizeBytes := 4 },
    .scalar { bits := 10, sizeBytes := 4 },
    .scalar { bits := 20, sizeBytes := 4 }],
    15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩

theorem rangeClamp_realizable : ClaimRealizable rangeClampClaim :=
  ⟨[.scalar { bits := 15, sizeBytes := 4 },
    .scalar { bits := 10, sizeBytes := 4 },
    .scalar { bits := 20, sizeBytes := 4 }],
    ⟨15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩,
    .scalar { bits := 15, sizeBytes := 4 },
    ⟨15, 10, 20, rfl, rfl⟩⟩

theorem rangeClamp_dichotomy : ClaimDichotomy rangeClampClaim := by
  refine ⟨[.scalar { bits := 15, sizeBytes := 4 },
      .scalar { bits := 10, sizeBytes := 4 },
      .scalar { bits := 20, sizeBytes := 4 }],
    ⟨15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩,
    ⟨.scalar { bits := 15, sizeBytes := 4 }, ⟨15, 10, 20, rfl, rfl⟩⟩,
    ⟨.scalar { bits := 0, sizeBytes := 4 }, ?_⟩⟩
  rintro ⟨val, lo, hi, hArgs, hRet⟩
  rcases list_triple_inj hArgs with ⟨hv, hlo, hhi⟩
  have hv' : (15 : Nat) = val := (scalar_bits_inj hv).1
  have hlo' : (10 : Nat) = lo := (scalar_bits_inj hlo).1
  have hhi' : (20 : Nat) = hi := (scalar_bits_inj hhi).1
  subst hv'; subst hlo'; subst hhi'
  have hBits : (0 : Nat) = min (max 15 10) 20 := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem rangeClamp_deterministic : ClaimDeterministic rangeClampClaim := by
  rintro args y₁ y₂ _ ⟨v₁, lo₁, hi₁, hArgs₁, hRet₁⟩ ⟨v₂, lo₂, hi₂, hArgs₂, hRet₂⟩
  rcases list_triple_inj (hArgs₁.symm.trans hArgs₂) with ⟨hv, hlo, hhi⟩
  have hv' : v₁ = v₂ := (scalar_bits_inj hv).1
  have hlo' : lo₁ = lo₂ := (scalar_bits_inj hlo).1
  have hhi' : hi₁ = hi₂ := (scalar_bits_inj hhi).1
  subst hv'; subst hlo'; subst hhi'
  exact hRet₁.trans hRet₂.symm

theorem rangeClamp_ext_ensuresDichotomy :
    ExternalSpecEnsuresDichotomy "core::cmp::Ord::clamp" rangeClampSidecar
      rangeClampPre rangeClampPost := by
  apply (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::cmp::Ord::clamp" rangeClampSidecar rangeClampPre rangeClampPost).mpr
  let req : MirCallReq := {
    defPath := "core::cmp::Ord::clamp"
    args := [
      .scalar { bits := 15, sizeBytes := 4 },
      .scalar { bits := 10, sizeBytes := 4 },
      .scalar { bits := 20, sizeBytes := 4 }
    ]
    memory := emptyMemory
  }
  refine ⟨req, emptyMemory,
    .scalar { bits := 15, sizeBytes := 4 },
    .scalar { bits := 0, sizeBytes := 4 },
    ⟨rfl, rfl,
      ⟨⟨15, by decide, rfl⟩, ⟨10, by decide, rfl⟩, ⟨20, by decide, rfl⟩, trivial⟩,
      ⟨15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩⟩,
    callFramePreserved_refl emptyMemory,
    ⟨15, by decide, rfl⟩,
    ⟨0, by decide, rfl⟩,
    ⟨15, 10, 20, rfl, rfl⟩,
    ?_⟩
  rintro ⟨val, lo, hi, hArgs, hRet⟩
  rcases list_triple_inj hArgs with ⟨hv, hlo, hhi⟩
  have hv' : (15 : Nat) = val := (scalar_bits_inj hv).1
  have hlo' : (10 : Nat) = lo := (scalar_bits_inj hlo).1
  have hhi' : (20 : Nat) = hi := (scalar_bits_inj hhi).1
  subst hv'; subst hlo'; subst hhi'
  have hBits : (0 : Nat) = min (max 15 10) 20 := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem rangeClamp_ext_realizable :
    MirCallContractRealizable rangeClampExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    rangeClamp_ext_ensuresDichotomy).toNormalDichotomy.toRealizable

theorem rangeClamp_ext_normalDichotomy :
    MirCallContractNormalDichotomy rangeClampExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    rangeClamp_ext_ensuresDichotomy).toNormalDichotomy

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``rangeClampPost) (some (Lean.mkConst ``rangeClampPre))
#eval assertDeclEnsuresBindsOutput ``rangeClampClaim
#eval assertDeclEnsuresBindsOutput ``rangeClampExtContract

/-! ### 1.4 `statefulCounterStep` (`StatefulClaim` & `StatefulClaimReturnDichotomy`) -/

def statefulCounterStepBody : CapturedMir :=
  mkStubBody "counter::step" 0 [mkLocalDecl u32MirTy] u32Layout true

def statefulCounterStepPre (args : List Value) (mem : Memory) : Prop :=
  args = [] ∧ mem.nextTag < scalarModulus 4

def statefulCounterStepPost
    (_args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  ret = .scalar { bits := mem.nextTag, sizeBytes := 4 } ∧
  mem' = { mem with nextTag := mem.nextTag + 1 }

def statefulCounterStepClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := statefulCounterStepPre
  post := statefulCounterStepPost
}

theorem statefulCounterStep_preSatisfiable :
    StatefulClaimPreSatisfiable statefulCounterStepClaim :=
  ⟨([], emptyMemory), rfl, by decide⟩

theorem statefulCounterStep_realizable :
    StatefulClaimRealizable statefulCounterStepClaim :=
  ⟨([], emptyMemory), ⟨rfl, by decide⟩,
    (.scalar { bits := emptyMemory.nextTag, sizeBytes := 4 },
      { emptyMemory with nextTag := emptyMemory.nextTag + 1 }),
    ⟨rfl, rfl⟩⟩

theorem statefulCounterStep_returnDichotomy :
    StatefulClaimReturnDichotomy statefulCounterStepClaim := by
  refine ⟨[], emptyMemory, { emptyMemory with nextTag := emptyMemory.nextTag + 1 },
    .scalar { bits := emptyMemory.nextTag, sizeBytes := 4 },
    .scalar { bits := 0, sizeBytes := 4 },
    ⟨rfl, by decide⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨hRet, _⟩
  have hBits : (0 : Nat) = emptyMemory.nextTag := (scalar_bits_inj hRet).1
  dsimp [emptyMemory] at hBits
  omega

theorem statefulCounterStep_dichotomy :
    StatefulClaimDichotomy statefulCounterStepClaim :=
  statefulCounterStep_returnDichotomy.toDichotomy

theorem statefulCounterStep_deterministic :
    StatefulClaimDeterministic statefulCounterStepClaim := by
  rintro ⟨args, mem⟩ ⟨v₁, m₁⟩ ⟨v₂, m₂⟩ _ ⟨hv₁, hm₁⟩ ⟨hv₂, hm₂⟩
  have hv : v₁ = v₂ := hv₁.trans hv₂.symm
  have hm : m₁ = m₂ := hm₁.trans hm₂.symm
  cases hv; cases hm; rfl

#eval assertDeclEnsuresBindsOutput ``statefulCounterStepClaim
#eval assertDeclEnsuresBindsOutput ``statefulCounterStepClaim { strictReturnValue := true }

/-! ### 1.5 Conditional Boilerplate Contract (Must Not Be False-Flagged) -/

open scoped Classical in
def condFrameContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      if callFramePreserved req.memory memAfter then
        retVal = .scalar { bits := 1, sizeBytes := 4 }
      else
        retVal = .scalar { bits := 2, sizeBytes := 4 }
    | .panicked _ => False
    | .aborted => True
}

#eval assertDeclEnsuresBindsOutput ``condFrameContract

/-! ## 2. Negative & Domain-Trap Suite (All 5 `VacuityClass` Variants) -/

/-! ### Class 1: `DeadPrecondition` -/

def deadPre (x : Nat) : Prop := x > 100 ∧ x < 50
def deadPost (x ret : Nat) : Prop := ret = x

theorem deadPre_not_satisfiable : ¬ PreconditionSatisfiable deadPre := by
  rintro ⟨x, hGt, hLt⟩
  omega

theorem deadPre_not_realizable : ¬ ContractRealizable deadPre deadPost :=
  not_contractRealizable_of_unsat_pre deadPre_not_satisfiable

#eval assertEnsuresVacuous
  (Lean.mkConst ``deadPost) (some (Lean.mkConst ``deadPre)) (some .deadPrecondition)

#eval show Lean.Meta.MetaM Unit from do
  let resDead ← checkRequiresSatisfiable (Lean.mkConst ``deadPre)
  unless resDead.satisfiable? == some false do
    throwError "expected deadPre unsatisfiable, got {repr resDead}"

/-! ### Class 2: `SpecViolation` -/

def specViolPre (x : Nat) : Prop := x < 10
def specViolPost (x ret : Nat) : Prop := x ≥ 10 ∧ ret = 5
def contraPost (_x ret : Nat) : Prop := ret = 1 ∧ ret = 2

theorem specViol_not_realizable : ¬ ContractRealizable specViolPre specViolPost := by
  rintro ⟨x, hLt, _, hGe, _⟩
  dsimp [specViolPre, specViolPost] at hLt hGe
  omega

theorem contraPost_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) contraPost := by
  rintro ⟨_, _, ret, h1, h2⟩
  omega

#eval assertEnsuresVacuous
  (Lean.mkConst ``specViolPost) (some (Lean.mkConst ``specViolPre)) (some .specViolation)
#eval assertEnsuresVacuous
  (Lean.mkConst ``contraPost) none (some .specViolation)

/-! ### Class 3: `TrivialPostcondition` -/

def trivTruePost (_x _ret : Nat) : Prop := True
def trivReflPost (_x ret : Nat) : Prop := ret = ret
def trivNotNePost (_x ret : Nat) : Prop := ¬ (ret ≠ ret)
def trivDisjPost (_x ret : Nat) : Prop := ret = ret ∨ ret = 0
def trivImpPost (x ret : Nat) : Prop := (ret = x) → (ret = x)

theorem trivTruePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivTruePost :=
  not_postconditionDichotomy_of_post_true _

theorem trivReflPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivReflPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => rfl)

theorem trivNotNePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivNotNePost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ hNe => hNe rfl)

theorem trivDisjPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivDisjPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => Or.inl rfl)

theorem trivImpPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivImpPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ h => h)

#eval assertEnsuresVacuous (Lean.mkConst ``trivTruePost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivReflPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivNotNePost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivDisjPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivImpPost) none (some .trivialPostcondition)

/-! ### Class 4: `UnboundReturnOutput` -/

def discardedLetPost (_x ret : Nat) : Prop :=
  let _ := ret
  True

def inputOnlyPost (x _ret : Nat) : Prop := x < 100

def optEmptyPost (_x : Nat) (ret : Option Empty) : Prop := ret = none

def memOnlyStatefulClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := fun _ _ => True
  post := fun _ mem _ mem' => mem' = mem
}

def boilerplateOnlyExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    sliceIsEmptyPre (fun _ _ => True)

def restatedFrameContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter => callFramePreserved req.memory memAfter
    | .panicked memAfter => callFramePreserved req.memory memAfter
    | .aborted => True
}

theorem discardedLetPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) discardedLetPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => trivial)

theorem inputOnlyPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) inputOnlyPost :=
  not_postconditionDichotomy_of_outputInsensitive (fun _ _ _ _ => Iff.rfl)

theorem optEmptyPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) optEmptyPost :=
  @not_postconditionDichotomy_of_subsingleton _ _ optionEmpty_subsingleton _ _

theorem memOnlyStateful_dichotomy :
    StatefulClaimDichotomy memOnlyStatefulClaim := by
  refine ⟨([], emptyMemory), trivial,
    ⟨(.unit, emptyMemory), rfl⟩,
    ⟨(.unit, { emptyMemory with nextTag := 2 }), ?_⟩⟩
  intro hEq
  exact memory_nextTag_ne_1_2 hEq.symm

theorem memOnlyStateful_not_returnDichotomy :
    ¬ StatefulClaimReturnDichotomy memOnlyStatefulClaim := by
  rintro ⟨_, _, _, _, _, _, hOk, hBad⟩
  exact hBad hOk

theorem boilerplateOnlyExt_not_ensuresDichotomy :
    ¬ ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
        sliceIsEmptyPre (fun _ _ => True) :=
  not_externalSpecEnsuresDichotomy_of_trivial_extraPost
    "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre (fun _ _ => trivial)

#eval assertEnsuresVacuous (Lean.mkConst ``discardedLetPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``inputOnlyPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``optEmptyPost) none (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``memOnlyStatefulClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``boilerplateOnlyExtContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``restatedFrameContract (some .unboundReturnOutput)

/-! ### Class 5: `SurvivedAllMutants` -/

def survivedPre (x : Nat) : Prop := x < 10
def survivedDisjPost (x ret : Nat) : Prop := x < 10 ∨ ret = 42
def survivedImpPost (x ret : Nat) : Prop := x ≥ 10 → ret = 42

theorem survivedDisj_not_dichotomy :
    ¬ PostconditionDichotomy survivedPre survivedDisjPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ hPre => Or.inl hPre)

theorem survivedImp_not_dichotomy :
    ¬ PostconditionDichotomy survivedPre survivedImpPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ hPre hGe => by
    dsimp [survivedPre] at hPre
    omega)

#eval assertEnsuresVacuous
  (Lean.mkConst ``survivedDisjPost) (some (Lean.mkConst ``survivedPre)) (some .survivedAllMutants)
#eval assertEnsuresVacuous
  (Lean.mkConst ``survivedImpPost) (some (Lean.mkConst ``survivedPre)) (some .survivedAllMutants)

#eval show Lean.Meta.MetaM Unit from do
  let resSat ← checkRequiresSatisfiable (Lean.mkConst ``survivedPre)
  unless resSat.satisfiable? == some true do
    throwError "expected survivedPre satisfiable, got {repr resSat}"

/-! ### Explicit Domain Traps 1, 2, 3 on `externalSpecCallContract` -/

/-- Trap 1 fixture: `externalSpecCallContract` with contradictory `extraPost := False`. -/
def trap1FalsePostContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    sliceIsEmptyPre (fun _ _ => False)

theorem trap1_naive_realizable_passes :
    ContractRealizable trap1FalsePostContract.pre trap1FalsePostContract.post :=
  (externalSpecCallContract_naive_realizable_iff_preSatisfiable
      "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre (fun _ _ => False)).mpr
    ⟨{ defPath := "core::slice::is_empty",
       args := [.scalar { bits := 0, sizeBytes := 8 }],
       memory := emptyMemory },
     ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩⟩

theorem trap1_normal_realizable_fails :
    ¬ MirCallContractRealizable trap1FalsePostContract :=
  not_mirCallContractRealizable_externalSpec_false_post
    "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre

#eval assertDeclEnsuresVacuous ``trap1FalsePostContract (some .specViolation)

/-- Trap 2 fixture: nounwind `externalSpecCallContract` with empty `localDecls` and
    trivial `extraPost := True` (generic dichotomy holds via `.returned` vs `.panicked`). -/
def trap2NoUnwindSidecar : CapturedMir :=
  mkStubBody "ffi::nounwind_noop" 0 [] boolLayout false

def trap2Contract : MirCallContract :=
  externalSpecCallContract "ffi::nounwind_noop" trap2NoUnwindSidecar
    (fun _ => True) (fun _ _ => True)

theorem trap2_generic_dichotomy_passes :
    PostconditionDichotomy trap2Contract.pre trap2Contract.post := by
  let req : MirCallReq := { defPath := "ffi::nounwind_noop", args := [], memory := emptyMemory }
  refine ⟨req, ⟨rfl, rfl, trivial, trivial⟩,
    ⟨.returned .unit emptyMemory, ⟨callFramePreserved_refl emptyMemory, trivial, trivial⟩⟩,
    ⟨.panicked emptyMemory, fun h => h⟩⟩

theorem trap2_ensuresDichotomy_fails :
    ¬ ExternalSpecEnsuresDichotomy "ffi::nounwind_noop" trap2NoUnwindSidecar
        (fun _ => True) (fun _ _ => True) :=
  not_externalSpecEnsuresDichotomy_of_trivial_extraPost
    "ffi::nounwind_noop" trap2NoUnwindSidecar (fun _ => True) (fun _ _ => trivial)

theorem trap2_strict_separation :
    ∃ c : MirCallContract,
      PostconditionDichotomy c.pre c.post ∧ ¬ MirCallContractNormalDichotomy c :=
  normalDichotomy_strictly_stronger_than_dichotomy.2

/-- Trap 3: `boilerplateOnlyExtContract` passes `MirCallContractNormalDichotomy` solely
    because `retMatchesCalleeReturnTy` rejects `.unit`, yet fails
    `ExternalSpecEnsuresDichotomy` modulo boilerplate observations. -/
theorem trap3_normalDichotomy_passes_via_boilerplate :
    MirCallContractNormalDichotomy boilerplateOnlyExtContract := by
  let req : MirCallReq := {
    defPath := "core::slice::is_empty"
    args := [.scalar { bits := 0, sizeBytes := 8 }]
    memory := emptyMemory
  }
  refine ⟨req, .scalar { bits := 1, sizeBytes := 1 }, emptyMemory, .unit, emptyMemory,
    ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩,
    ⟨callFramePreserved_refl emptyMemory, ⟨1, by decide, rfl⟩, trivial⟩,
    ?_⟩
  rintro ⟨_, ⟨b, _, hEq⟩, _⟩
  cases hEq

theorem trap3_ensuresDichotomy_fails :
    ¬ ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
        sliceIsEmptyPre (fun _ _ => True) :=
  boilerplateOnlyExt_not_ensuresDichotomy

/-! ## 3. Mandatory Compile-Time Kernel Axiom Audit -/

#eval show Lean.Meta.MetaM Unit from do
  let env ← Lean.getEnv
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden : List Lean.Name := [`sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler]
  let matchesPrefix (n : Lean.Name) : Bool :=
    (`Anneal.SpecRealizability).isPrefixOf n || (`SpecRealizabilityTests).isPrefixOf n
  let isTarget (n : Lean.Name) : Bool :=
    matchesPrefix n ||
      match Lean.privateToUserName? n with
      | some u => matchesPrefix u
      | none => false
  let allEntries : List (Lean.Name × Lean.ConstantInfo) :=
    env.constants.map₁.toList ++ env.constants.map₂.toList
  let mut declCount : Nat := 0
  let mut thmCount : Nat := 0
  for (n, ci) in allEntries do
    if !isTarget n then
      continue
    declCount := declCount + 1
    if ci.isUnsafe then
      throwError "kernel audit failed: unsafe declaration `{n}`"
    if ci matches .axiomInfo _ then
      throwError "kernel audit failed: axiom declaration `{n}`"
    if ci matches .thmInfo _ then
      thmCount := thmCount + 1
      let axs ← Lean.collectAxioms n
      for ax in axs do
        if forbidden.contains ax then
          throwError "kernel audit failed: theorem `{n}` depends on forbidden axiom `{ax}`"
        unless allowed.contains ax do
          throwError "kernel audit failed: theorem `{n}` depends on disallowed axiom `{ax}`"
  if thmCount < 30 then
    throwError "kernel audit failed: audited only {thmCount} theorems (expected ≥ 30)"
  Lean.logInfo
    m!"SpecRealizability kernel axiom audit passed: {declCount} declarations ({thmCount} theorems, all clean)"

end SpecRealizabilityTests
